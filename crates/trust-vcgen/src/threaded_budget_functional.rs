// trust-vcgen/threaded_budget_functional.rs: SN-vs-fuel RESOLUTION item 1 —
// the STATE-THREADED numeric-budget induction VC lane.
//
// The sibling `mutual_recursive_datatype_functional` lane models the PER-LEVEL
// structural fuel discipline: every cluster call in a step arm receives the
// SAME one-step-smaller fuel `k` (each-at-k). The real kernel cluster is not
// each-at-k: it is budget-mediated by a state-THREADED heartbeat counter
// (`Cell<u32>`, decrement per guarded entry, fail-closed exhaustion) — each
// entry decrements the budget at least once and every callee receives the
// caller's REMAINDER, and the remainder flows back out through the return
// value. THIS lane is the fixture-grade mirror of that discipline (the
// adopted partial-correctness-via-fuel design, item 1).
//
// SHAPE DETECTED (fail-closed outside it): a call-graph SCC of size N > 1
// whose members all have the extracted threaded form
//
//   fn m(fuel: &Fuel, e: &E) -> Res {           // Res = Mk(Fuel, E): the
//       match fuel {                            // (remainder, result) pair —
//           Fuel::Z    => Res::Mk(Fuel::Z, e)   // the functional image of the
//           Fuel::S(k) => match e {             // threaded counter
//               C(..) => {
//                   let r1 = callee1(k, x);         // ENTRY DECREMENT: the
//                   let r2 = callee2(r1.0, y);      // first callee gets k;
//                   Res::Mk(r2.0, C(r1.1, r2.1))    // every LATER callee gets
//               }                                   // the PREVIOUS REMAINDER;
//               ...                                 // the arm returns the
//           }                                       // LAST remainder
//       }
//   }
//
// where `Fuel` is nat-shaped (`Z | S Fuel`), `E` is the shared payload
// datatype (recursive/nullary constructor fields only), and `Res` is a
// single-constructor pair datatype `Mk(Fuel, E)`. The exhaustion arm
// (fuel = Z) is PINNED to `Mk(Z, e)` — return the input unreduced with the
// spent budget — the fail-closed identity shape (whnf's exhaustion-identity;
// the Done/Exhausted outcome shapes are the sibling `fuel_outcome_functional`
// lane, item 2).
//
// THREADING GATES (each makes the induction marker honest; violating any
// fails the WHOLE bundle closed):
//   * the FIRST call of an arm receives exactly the fuel binder `k` (the
//     guarded-entry decrement: k < S k);
//   * call p > 0 receives exactly `<call p-1's result>.0` — the previous
//     remainder (`Sel` of the pair's fuel field);
//   * the arm's returned remainder is `k` (call-free arms) or the LAST call's
//     remainder;
//   * calls only inside step payload arms; the base arm is call-free.
// Strict decrease across guarded entries is what lets the discharge use plain
// `Fuel.rec` — NO `Acc` (trust-certify's twin documents the motive shape).
//
// POSTCONDITION MODE: model-vs-reference ONLY — every member's postcondition
// is `Eq(_0, FnApp(ref, [fuel, e]))` naming a REFERENCE function; the
// reference set (closed under its own calls, disjoint from the cluster) must
// itself be threaded-shaped over the same fuel/payload/result datatypes, and
// its arms travel as DEFINITIONAL transport VCs (refbase/refstep).
//
// EMITTED BUNDLE (per SCC):
//   * base VCs, per member:
//       `threaded_budget_functional_base::<m>`
//       `Forall [e] Eq(Mk(Z, e), FnApp(ref_m, [Z, e]))`
//   * step VCs, per member per payload constructor:
//       `threaded_budget_functional_case::<m>::<C>[calls=c1,..]`
//       `Forall [k, fields, ihs] (Implies (And IH-atoms)
//           Eq(Mk(rem, tree), FnApp(ref_m, [S k, C(fields)])))`
//     where IH atom p is the CALLEE's postcondition at the THREADED fuel —
//     `Eq(__ih_p, FnApp(ref_cp, [k | __ih_{p-1}.0, field]))` — the
//     REMAINDER-THREADING IH atoms: atom p's fuel argument is a projection of
//     atom p-1's result variable, not the uniform `k`;
//   * reference definitional VCs
//       `threaded_budget_functional_refbase::<r>`  `Forall [e]
//           Eq(FnApp(r, [Z, e]), Mk(Z, e))`
//       `threaded_budget_functional_refstep::<r>::<C>[calls=..]`  `Forall
//           [k, fields] Eq(FnApp(r, [S k, C(fields)]), Mk(rem', tree'))`
//     (call values inline as `FnApp`, fuel-chained through `Sel`);
//   * ONE JOINT CONCLUSION VC
//       `threaded_budget_functional_conclusion[threaded-induction:
//        fuel=<F>:<Z>|<S>;res=<R>:<Mk>;data=<E>;members=..;bases=..;cases=..;
//        refs=..;refbases=..;refcases=..]`
//       `And [Forall [fuel, e] Eq(_0, FnApp(ref_i, [fuel, e])), ..]`
//     discharged BY THREADED-BUDGET INDUCTION FROM THE CASES or not at all.
//
// SOUNDNESS: this module only PRODUCES proof obligations; it discharges none.
// HONESTY: fixture-grade — the LITERAL kernel cluster additionally has
// interior mutability (`Cell`), `Rc` sharing, and generics between it and the
// extractor; those are the named non-SN extraction gaps, out of scope here.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::HashMap;

use trust_types::{
    BlockId, Formula, Place, Projection, Sort, Terminator, Ty, VcKind, VerifiableFunction,
    VerificationCondition,
};

use crate::call_graph::{build_call_graph, detect_cycles};
use crate::mutual_recursive_datatype_functional::{
    is_marker_safe_path, is_marker_safe_segment, nat_shape,
};
use crate::recursive_datatype_functional::{
    WalkState, apply_stmt, conjoin_all, discriminant_place, local_ty, peel_indirection,
    resolve_operand, resolve_place, subst_post, subst_vars,
};

/// Property tag prefix of a BASE (fuel = Z, pinned exhaustion) VC.
pub const THREADED_BASE_PROPERTY_PREFIX: &str = "threaded_budget_functional_base::";
/// Property tag prefix of a STEP (fuel = S k) case VC.
pub const THREADED_CASE_PROPERTY_PREFIX: &str = "threaded_budget_functional_case::";
/// Property tag prefix of the joint CONCLUSION VC (suffixed with the
/// `[threaded-induction:..]` bundle marker).
pub const THREADED_CONCLUSION_PROPERTY_PREFIX: &str = "threaded_budget_functional_conclusion";
/// Property tag prefix of a REFERENCE-function BASE definitional VC.
pub const THREADED_REF_BASE_PROPERTY_PREFIX: &str = "threaded_budget_functional_refbase::";
/// Property tag prefix of a REFERENCE-function STEP definitional VC.
pub const THREADED_REF_STEP_PROPERTY_PREFIX: &str = "threaded_budget_functional_refstep::";

/// The fuel parameter is the FIRST parameter and the payload the SECOND.
const FUEL_LOCAL: usize = 1;
const PAYLOAD_LOCAL: usize = 2;

/// Which fuel arm the walk is currently under.
#[derive(Clone, Copy, PartialEq, Eq)]
enum FuelLayer {
    None,
    Base,
    Step,
}

/// How the walk treats cluster calls (mirrors the mutual lane).
#[derive(Clone, Copy, PartialEq, Eq)]
enum WalkKind {
    /// Cluster MEMBER: calls become remainder-threading IH atoms.
    Member,
    /// REFERENCE function: calls become definitional `FnApp`s inline.
    Reference,
}

/// One completed step arm.
struct ArmRec {
    tag: usize,
    ctor: String,
    callees: Vec<String>,
    formula: Formula,
}

/// Everything the walk learns about one member/reference.
#[derive(Default)]
struct MemberOut {
    fuel_dt: Option<Ty>,
    fuel_z: Option<(usize, String)>,
    fuel_s: Option<(usize, String)>,
    payload_dt: Option<Ty>,
    /// The single pinned exhaustion VC body (`Eq(Mk(Z, e), ..)`-instance).
    base: Vec<Formula>,
    steps: Vec<ArmRec>,
}

/// The result-pair shape: `Res = Mk(<fuel field>, <payload field>)` — one
/// constructor, field 0 (indirection-peeled) the fuel datatype, field 1 the
/// payload datatype. Returns `(mk_ctor, fuel_field_name, payload_field_name)`.
fn res_shape(res: &Ty, fuel_name: &str, payload_name: &str) -> Option<(String, String, String)> {
    let Ty::Datatype { variants, .. } = res else {
        return None;
    };
    let [(mk, fields)] = variants.as_slice() else {
        return None;
    };
    let [(f0, t0), (f1, t1)] = fields.as_slice() else {
        return None;
    };
    let (Ty::Datatype { name: n0, .. }, Ty::Datatype { name: n1, .. }) =
        (peel_indirection(t0), peel_indirection(t1))
    else {
        return None;
    };
    (n0 == fuel_name && n1 == payload_name).then(|| (mk.clone(), f0.clone(), f1.clone()))
}

/// In model-vs-reference mode, the member's postcondition names its
/// REFERENCE: `Eq(_0, FnApp(ref, [<fuel param>, <payload param>]))`.
fn ref_fn_target<'a>(func: &VerifiableFunction, post: &'a Formula) -> Option<&'a str> {
    let Formula::Eq(lhs, rhs) = post else {
        return None;
    };
    if lhs.var_name() != Some("_0") {
        return None;
    }
    let Formula::FnApp { func: name, args, .. } = rhs.as_ref() else {
        return None;
    };
    let [fuel_arg, payload_arg] = args.as_slice() else {
        return None;
    };
    (fuel_arg.var_name()
        == Some(crate::place_to_var_name(func, &Place::local(FUEL_LOCAL)).as_str())
        && payload_arg.var_name()
            == Some(crate::place_to_var_name(func, &Place::local(PAYLOAD_LOCAL)).as_str()))
    .then_some(name.as_str())
}

/// The DEFINITIONAL pseudo-postcondition a reference function is walked
/// against: `Eq(FnApp(r, [fuel, e]), _0)`.
fn ref_pseudo_post(func: &VerifiableFunction) -> Option<Formula> {
    let fuel = crate::recursive_datatype_functional::param_var(func, FUEL_LOCAL)?;
    let e = crate::recursive_datatype_functional::param_var(func, PAYLOAD_LOCAL)?;
    let ret_sort = crate::sort_for_ty(peel_indirection(&func.body.return_ty));
    Some(Formula::Eq(
        Box::new(Formula::FnApp {
            func: func.name.clone(),
            args: vec![fuel, e],
            sort: ret_sort.clone(),
        }),
        Box::new(Formula::var_owned("_0".to_string(), ret_sort)),
    ))
}

/// Emit the threaded-budget induction VC bundles for every call-graph SCC of
/// size > 1 in `funcs` whose members fit the threaded shape. Each SCC fails
/// closed on its own.
#[must_use]
pub fn threaded_budget_functional_vcs(funcs: &[VerifiableFunction]) -> Vec<VerificationCondition> {
    let graph = build_call_graph(funcs);
    let mut out = Vec::new();
    for scc in detect_cycles(&graph) {
        if scc.members.len() < 2 {
            continue;
        }
        let members: Vec<&VerifiableFunction> = scc
            .members
            .iter()
            .filter_map(|path| funcs.iter().find(|f| &f.def_path == path))
            .collect();
        if members.len() != scc.members.len() {
            continue;
        }
        if let Some(vcs) = emit_cluster(&members, funcs) {
            let arithmetic_gaps: Vec<_> = members
                .iter()
                .filter_map(|func| {
                    crate::contracts::functional_lane_unmodeled_postcondition_vc(
                        func,
                        "threaded-budget functional induction",
                    )
                })
                .collect();
            if arithmetic_gaps.is_empty() {
                out.extend(vcs);
            } else {
                out.extend(arithmetic_gaps);
            }
        }
    }
    out
}

/// Emit the bundle for ONE threaded cluster. `None` (fail-closed) on any
/// out-of-scope shape.
#[allow(clippy::too_many_lines)]
fn emit_cluster(
    members: &[&VerifiableFunction],
    funcs: &[VerifiableFunction],
) -> Option<Vec<VerificationCondition>> {
    let names: Vec<&str> = members.iter().map(|f| f.name.as_str()).collect();
    {
        let mut sorted = names.clone();
        sorted.sort_unstable();
        sorted.dedup();
        if sorted.len() != names.len() {
            return None;
        }
    }
    if !names.iter().all(|n| is_marker_safe_segment(n)) {
        return None;
    }
    for f in members {
        if f.postconditions.is_empty() || f.body.arg_count != 2 {
            return None;
        }
    }
    let posts: Vec<Formula> =
        members.iter().map(|f| conjoin_all(f.postconditions.clone())).collect();

    // Postcondition mode: model-vs-reference for EVERY member (this lane has
    // no constructor-tree mode: the remainder component has no closed form).
    let ref_targets: Vec<&str> =
        members.iter().zip(&posts).map(|(f, p)| ref_fn_target(f, p)).collect::<Option<Vec<_>>>()?;

    // The result-pair datatype: every member returns the SAME single-ctor
    // pair; its field datatypes are checked after the walk pins fuel/payload.
    let res_dt = peel_indirection(&members[0].body.return_ty).clone();
    for f in members {
        if peel_indirection(&f.body.return_ty) != &res_dt {
            return None;
        }
    }

    // Walk every member.
    let mut outs: Vec<MemberOut> = Vec::with_capacity(members.len());
    for (idx, func) in members.iter().enumerate() {
        let entry = func.body.blocks.first()?;
        let mut mo = MemberOut::default();
        let mut ih_counter = 0usize;
        let ok = twalk(
            TwalkCx { members, posts: &posts, kind: WalkKind::Member, member_idx: idx },
            entry.id,
            WalkState::default(),
            ArmCx::default(),
            FuelLayer::None,
            0,
            &mut ih_counter,
            &mut mo,
        );
        if !ok {
            return None;
        }
        outs.push(mo);
    }

    // Resolve the REFERENCE set — the named refs closed under their own calls
    // — and walk each in definitional mode.
    let mut refs: Vec<&VerifiableFunction> = Vec::new();
    let mut ref_outs: Vec<MemberOut> = Vec::new();
    {
        let mut queue: Vec<String> = ref_targets.iter().map(|t| (*t).to_string()).collect();
        let mut qi = 0usize;
        while qi < queue.len() {
            let target = queue[qi].clone();
            qi += 1;
            let func = funcs.iter().find(|f| f.name == target || f.def_path == target)?;
            if refs.iter().any(|r| r.name == func.name) {
                continue;
            }
            if names.contains(&func.name.as_str())
                || !is_marker_safe_segment(&func.name)
                || func.body.arg_count != 2
                || peel_indirection(&func.body.return_ty) != &res_dt
            {
                return None;
            }
            refs.push(func);
            for block in &func.body.blocks {
                if let Terminator::Call { func: callee, .. } = &block.terminator {
                    queue.push(callee.clone());
                }
            }
        }
        if refs.is_empty() {
            return None;
        }
        let pseudo: Vec<Formula> =
            refs.iter().map(|f| ref_pseudo_post(f)).collect::<Option<Vec<_>>>()?;
        for (idx, func) in refs.iter().enumerate() {
            let entry = func.body.blocks.first()?;
            let mut mo = MemberOut::default();
            let mut ih_counter = 0usize;
            let ok = twalk(
                TwalkCx {
                    members: &refs,
                    posts: &pseudo,
                    kind: WalkKind::Reference,
                    member_idx: idx,
                },
                entry.id,
                WalkState::default(),
                ArmCx::default(),
                FuelLayer::None,
                0,
                &mut ih_counter,
                &mut mo,
            );
            if !ok {
                return None;
            }
            ref_outs.push(mo);
        }
    }

    // Cross-member consistency: one fuel, one payload, one result-pair shape.
    let first = &outs[0];
    let fuel_dt = first.fuel_dt.clone()?;
    let Ty::Datatype { name: fuel_name, .. } = &fuel_dt else {
        return None;
    };
    let (fuel_z, fuel_s) = (first.fuel_z.clone()?, first.fuel_s.clone()?);
    let payload_dt = first.payload_dt.clone()?;
    let Ty::Datatype { name: payload_name, variants: payload_variants } = &payload_dt else {
        return None;
    };
    if fuel_name == payload_name || payload_variants.is_empty() {
        return None;
    }
    let Ty::Datatype { name: res_name, .. } = &res_dt else {
        return None;
    };
    let (res_mk, _, _) = res_shape(&res_dt, fuel_name, payload_name)?;
    if res_name == fuel_name || res_name == payload_name {
        return None;
    }
    if !is_marker_safe_path(fuel_name)
        || !is_marker_safe_path(payload_name)
        || !is_marker_safe_path(res_name)
        || !is_marker_safe_segment(&fuel_z.1)
        || !is_marker_safe_segment(&fuel_s.1)
        || !is_marker_safe_segment(&res_mk)
        || !payload_variants.iter().all(|(c, _)| is_marker_safe_segment(c))
    {
        return None;
    }
    // Payload fields must be recursive (the payload datatype itself) only.
    for (_, fields) in payload_variants {
        for (_, fty) in fields {
            let Ty::Datatype { name, .. } = peel_indirection(fty) else {
                return None;
            };
            if name != payload_name {
                return None;
            }
        }
    }
    for mo in outs.iter().chain(&ref_outs) {
        let (Some(fdt), Some(pdt)) = (&mo.fuel_dt, &mo.payload_dt) else {
            return None;
        };
        if fdt != &fuel_dt || pdt != &payload_dt {
            return None;
        }
        if mo.fuel_z != Some(fuel_z.clone()) || mo.fuel_s != Some(fuel_s.clone()) {
            return None;
        }
    }

    // Coverage: the step arms cover every payload constructor exactly once;
    // exactly one pinned base per member/reference.
    let all_tags: Vec<usize> = (0..payload_variants.len()).collect();
    for mo in outs.iter_mut().chain(ref_outs.iter_mut()) {
        mo.steps.sort_by_key(|a| a.tag);
        let tags: Vec<usize> = mo.steps.iter().map(|a| a.tag).collect();
        if tags != all_tags || mo.base.len() != 1 {
            return None;
        }
    }

    // Assemble.
    let mut vcs: Vec<VerificationCondition> = Vec::new();
    let mut n_bases = 0usize;
    let mut n_cases = 0usize;
    let e_sort = crate::sort_for_ty(&payload_dt);
    for ((func, mo), name) in members.iter().zip(&outs).zip(&names) {
        let mk = |property: String, formula: Formula| VerificationCondition {
            kind: VcKind::FunctionalCorrectness { property, context: (*name).to_string() },
            function: (*name).into(),
            location: func.span.clone(),
            formula,
            contract_metadata: None,
            obligation: None,
        };
        let e_name = crate::place_to_var_name(func, &Place::local(PAYLOAD_LOCAL));
        let base = Formula::forall(&[(e_name.as_str(), e_sort.clone())], mo.base[0].clone());
        vcs.push(mk(format!("{THREADED_BASE_PROPERTY_PREFIX}{name}"), base));
        n_bases += 1;
        for arm in &mo.steps {
            vcs.push(mk(
                format!(
                    "{THREADED_CASE_PROPERTY_PREFIX}{name}::{}[calls={}]",
                    arm.ctor,
                    arm.callees.join(",")
                ),
                arm.formula.clone(),
            ));
            n_cases += 1;
        }
    }
    let mut n_refbases = 0usize;
    let mut n_refcases = 0usize;
    for (func, mo) in refs.iter().zip(&ref_outs) {
        let name = func.name.as_str();
        let mk = |property: String, formula: Formula| VerificationCondition {
            kind: VcKind::FunctionalCorrectness { property, context: name.to_string() },
            function: name.into(),
            location: func.span.clone(),
            formula,
            contract_metadata: None,
            obligation: None,
        };
        let e_name = crate::place_to_var_name(func, &Place::local(PAYLOAD_LOCAL));
        let base = Formula::forall(&[(e_name.as_str(), e_sort.clone())], mo.base[0].clone());
        vcs.push(mk(format!("{THREADED_REF_BASE_PROPERTY_PREFIX}{name}"), base));
        n_refbases += 1;
        for arm in &mo.steps {
            vcs.push(mk(
                format!(
                    "{THREADED_REF_STEP_PROPERTY_PREFIX}{name}::{}[calls={}]",
                    arm.ctor,
                    arm.callees.join(",")
                ),
                arm.formula.clone(),
            ));
            n_refcases += 1;
        }
    }

    // Joint conclusion.
    let mut conjuncts = Vec::with_capacity(members.len());
    for (func, post) in members.iter().zip(&posts) {
        let binders: Vec<(String, Sort)> = [FUEL_LOCAL, PAYLOAD_LOCAL]
            .into_iter()
            .map(|i| {
                Some((
                    crate::place_to_var_name(func, &Place::local(i)),
                    crate::sort_for_ty(peel_indirection(local_ty(func, i)?)),
                ))
            })
            .collect::<Option<Vec<_>>>()?;
        let refs_b: Vec<(&str, Sort)> =
            binders.iter().map(|(n, s)| (n.as_str(), s.clone())).collect();
        conjuncts.push(Formula::forall(&refs_b, post.clone()));
    }
    let ref_names: Vec<&str> = refs.iter().map(|f| f.name.as_str()).collect();
    let marker = format!(
        "[threaded-induction:fuel={fuel_name}:{}|{};res={res_name}:{res_mk};data={payload_name};\
         members={};bases={n_bases};cases={n_cases};refs={};refbases={n_refbases};\
         refcases={n_refcases}]",
        fuel_z.1,
        fuel_s.1,
        names.join(","),
        ref_names.join(","),
    );
    let joint = names.join("+");
    vcs.push(VerificationCondition {
        kind: VcKind::FunctionalCorrectness {
            property: format!("{THREADED_CONCLUSION_PROPERTY_PREFIX}{marker}"),
            context: joint.clone(),
        },
        function: joint.into(),
        location: members[0].span.clone(),
        formula: Formula::And(conjuncts),
        contract_metadata: None,
        obligation: None,
    });
    Some(vcs)
}

/// Immutable walk context (which cluster, which member, which mode).
#[derive(Clone, Copy)]
struct TwalkCx<'a> {
    members: &'a [&'a VerifiableFunction],
    posts: &'a [Formula],
    kind: WalkKind,
    member_idx: usize,
}

/// Per-arm mutable context threaded down one CFG path.
#[derive(Clone, Default)]
struct ArmCx {
    /// The step arm's fuel binder name (`__fld_<S>_0`).
    k_name: Option<String>,
    /// The arm's payload field variable names.
    field_names: Vec<String>,
    /// Callee names, one per call, in call order.
    callees: Vec<String>,
    /// The value each call's result resolves to (`Var __ih_p` in member mode,
    /// the definitional `FnApp` in reference mode), in call order.
    call_values: Vec<Formula>,
}

/// Whether `f` is exactly the fuel-field selection `<value>.0` of `prev`
/// (the remainder of the previous call).
fn is_remainder_of(f: &Formula, res_dt: &Ty, prev: &Formula) -> bool {
    let Ty::Datatype { name, variants } = res_dt else {
        return false;
    };
    let Some((_, fields)) = variants.first() else {
        return false;
    };
    let Some((fuel_field, _)) = fields.first() else {
        return false;
    };
    matches!(f, Formula::Sel { datatype, field, arg, .. }
        if datatype == name && field == fuel_field && arg.as_ref() == prev)
}

/// Whether `f` is the payload-field selection `<call value>.1`; returns the
/// call index.
fn payload_of_call(f: &Formula, res_dt: &Ty, calls: &[Formula]) -> Option<usize> {
    let Ty::Datatype { name, variants } = res_dt else {
        return None;
    };
    let (_, fields) = variants.first()?;
    let (payload_field, _) = fields.get(1)?;
    let Formula::Sel { datatype, field, arg, .. } = f else {
        return None;
    };
    (datatype == name && field == payload_field)
        .then(|| calls.iter().position(|c| c == arg.as_ref()))
        .flatten()
}

/// Validate the arm's PAYLOAD result tree: leaves are pattern fields or
/// `<call>.1` payload selections; nodes are payload constructors at arity.
fn valid_payload_tree(f: &Formula, cx: &ArmCx, res_dt: &Ty, payload_dt: &Ty) -> bool {
    if let Some(name) = f.var_name() {
        return cx.field_names.iter().any(|n| n == name);
    }
    if payload_of_call(f, res_dt, &cx.call_values).is_some() {
        return true;
    }
    let Formula::Ctor { ctor, args, .. } = f else {
        return false;
    };
    let Ty::Datatype { variants, .. } = payload_dt else {
        return false;
    };
    let Some((_, fields)) = variants.iter().find(|(c, _)| c == ctor) else {
        return false;
    };
    args.len() == fields.len() && args.iter().all(|a| valid_payload_tree(a, cx, res_dt, payload_dt))
}

/// Bounded CFG walk for one member of the threaded cluster (or one REFERENCE
/// function in definitional mode).
#[allow(clippy::too_many_arguments, clippy::too_many_lines)]
fn twalk(
    cx: TwalkCx<'_>,
    block_id: BlockId,
    mut state: WalkState,
    mut arm: ArmCx,
    fuel: FuelLayer,
    depth: usize,
    ih_counter: &mut usize,
    out: &mut MemberOut,
) -> bool {
    if depth > 64 {
        return false;
    }
    let func = cx.members[cx.member_idx];
    let Some(block) = func.body.blocks.iter().find(|b| b.id == block_id) else {
        return false;
    };

    for stmt in &block.stmts {
        apply_stmt(func, &mut state, stmt);
    }

    match &block.terminator {
        Terminator::Return => {
            let Some(result) = resolve_place(func, &state, &Place::local(0)) else {
                return false;
            };
            let post = &cx.posts[cx.member_idx];
            let res_dt = peel_indirection(&func.body.return_ty);
            let Ty::Datatype { variants: res_variants, .. } = res_dt else {
                return false;
            };
            let Some((mk_name, _)) = res_variants.first() else {
                return false;
            };
            let Formula::Ctor { ctor, args, .. } = &result else {
                return false;
            };
            if ctor != mk_name {
                return false;
            }
            let [rem, tree] = args.as_slice() else {
                return false;
            };
            match (fuel, state.ctor.clone()) {
                (FuelLayer::None, _) => false,
                (FuelLayer::Base, None) => {
                    // PINNED exhaustion: `Mk(Z, e)` — zero remainder, input
                    // payload, no binders, no calls.
                    if !state.binders.is_empty() || !state.ih_atoms.is_empty() {
                        return false;
                    }
                    let Some((_, z_ctor)) = &out.fuel_z else {
                        return false;
                    };
                    let z_ok = matches!(rem, Formula::Ctor { ctor, args, .. }
                        if ctor == z_ctor && args.is_empty());
                    let e_name = crate::place_to_var_name(func, &Place::local(PAYLOAD_LOCAL));
                    if !z_ok || tree.var_name() != Some(e_name.as_str()) {
                        return false;
                    }
                    out.base.push(subst_post(func, post, &state, result.clone()));
                    out.base.len() == 1
                }
                (FuelLayer::Base, Some(_)) | (FuelLayer::Step, None) => false,
                (FuelLayer::Step, Some((tag, ctor_name))) => {
                    // Remainder: `k` (call-free) or the LAST call's remainder.
                    let Some(k_name) = arm.k_name.clone() else {
                        return false;
                    };
                    let rem_ok = if let Some(last) = arm.call_values.last() {
                        is_remainder_of(rem, res_dt, last)
                    } else {
                        rem.var_name() == Some(k_name.as_str())
                    };
                    if !rem_ok {
                        return false;
                    }
                    let payload_dt = out.payload_dt.clone();
                    let Some(payload_dt) = payload_dt else {
                        return false;
                    };
                    if !valid_payload_tree(tree, &arm, res_dt, &payload_dt) {
                        return false;
                    }
                    let conclusion = subst_post(func, post, &state, result.clone());
                    let body = if state.ih_atoms.is_empty() {
                        conclusion
                    } else {
                        Formula::Implies(
                            Box::new(conjoin_all(state.ih_atoms.clone())),
                            Box::new(conclusion),
                        )
                    };
                    let refs: Vec<(&str, Sort)> =
                        state.binders.iter().map(|(n, s)| (n.as_str(), s.clone())).collect();
                    out.steps.push(ArmRec {
                        tag,
                        ctor: ctor_name,
                        callees: arm.callees.clone(),
                        formula: Formula::forall(&refs, body),
                    });
                    true
                }
            }
        }
        Terminator::Goto(target) => {
            twalk(cx, *target, state, arm, fuel, depth + 1, ih_counter, out)
        }
        Terminator::Assert { target, .. } | Terminator::Drop { target, .. } => {
            twalk(cx, *target, state, arm, fuel, depth + 1, ih_counter, out)
        }
        Terminator::Unreachable => true,
        Terminator::SwitchInt { discr, targets, .. } => {
            let Some(matched) = discriminant_place(&state, discr) else {
                return false;
            };
            if !matched.projections.iter().all(|p| matches!(p, Projection::Deref)) {
                return false;
            }
            match (fuel, &state.ctor) {
                // Layer 1: the FUEL match.
                (FuelLayer::None, None) => {
                    if matched.local != FUEL_LOCAL {
                        return false;
                    }
                    let Some(fuel_ty) = local_ty(func, FUEL_LOCAL) else {
                        return false;
                    };
                    let dt = peel_indirection(fuel_ty).clone();
                    let Some(((z_tag, z_ctor), (s_tag, s_ctor))) = nat_shape(&dt) else {
                        return false;
                    };
                    let mut tags: Vec<usize> = targets.iter().map(|(t, _)| *t as usize).collect();
                    tags.sort_unstable();
                    let mut expected = vec![z_tag, s_tag];
                    expected.sort_unstable();
                    if tags != expected {
                        return false;
                    }
                    out.fuel_dt = Some(dt.clone());
                    out.fuel_z = Some((z_tag, z_ctor.clone()));
                    out.fuel_s = Some((s_tag, s_ctor.clone()));
                    let dt_sort = crate::sort_for_ty(&dt);
                    for (tag, target) in targets {
                        let tag = *tag as usize;
                        let mut arm_state = state.clone();
                        let mut arm_cx = arm.clone();
                        let layer = if tag == z_tag {
                            arm_state.store.insert(
                                FUEL_LOCAL,
                                Formula::Ctor {
                                    ctor: z_ctor.clone(),
                                    args: vec![],
                                    sort: dt_sort.clone(),
                                },
                            );
                            FuelLayer::Base
                        } else {
                            let k_name = format!("__fld_{s_ctor}_0");
                            let k_var = Formula::var_owned(k_name.clone(), dt_sort.clone());
                            arm_state.binders.push((k_name.clone(), dt_sort.clone()));
                            arm_state.store.insert(
                                FUEL_LOCAL,
                                Formula::Ctor {
                                    ctor: s_ctor.clone(),
                                    args: vec![k_var],
                                    sort: dt_sort.clone(),
                                },
                            );
                            arm_cx.k_name = Some(k_name);
                            FuelLayer::Step
                        };
                        if !twalk(cx, *target, arm_state, arm_cx, layer, depth + 1, ih_counter, out)
                        {
                            return false;
                        }
                    }
                    true
                }
                // Layer 2: the PAYLOAD match (step layer only — the base arm
                // is the pinned direct return).
                (FuelLayer::Step, None) => {
                    if matched.local != PAYLOAD_LOCAL {
                        return false;
                    }
                    let Some(matched_ty) = local_ty(func, PAYLOAD_LOCAL) else {
                        return false;
                    };
                    let dt = peel_indirection(matched_ty).clone();
                    let Ty::Datatype { variants, .. } = &dt else {
                        return false;
                    };
                    if variants.is_empty() {
                        return false;
                    }
                    match &out.payload_dt {
                        None => out.payload_dt = Some(dt.clone()),
                        Some(prev) if prev == &dt => {}
                        Some(_) => return false,
                    }
                    let dt_sort = crate::sort_for_ty(&dt);
                    for (tag, target) in targets {
                        let tag = *tag as usize;
                        let Some((ctor, fields)) = variants.get(tag).cloned() else {
                            return false;
                        };
                        let mut arm_state = state.clone();
                        let mut arm_cx = arm.clone();
                        let mut field_vars = Vec::with_capacity(fields.len());
                        for (i, (_, fty)) in fields.iter().enumerate() {
                            let name = format!("__fld_{ctor}_{i}");
                            let sort = crate::sort_for_ty(peel_indirection(fty));
                            arm_state.binders.push((name.clone(), sort.clone()));
                            arm_cx.field_names.push(name.clone());
                            field_vars.push(Formula::var_owned(name, sort));
                        }
                        arm_state.store.insert(
                            PAYLOAD_LOCAL,
                            Formula::Ctor {
                                ctor: ctor.clone(),
                                args: field_vars,
                                sort: dt_sort.clone(),
                            },
                        );
                        arm_state.ctor = Some((tag, ctor));
                        if !twalk(cx, *target, arm_state, arm_cx, fuel, depth + 1, ih_counter, out)
                        {
                            return false;
                        }
                    }
                    true
                }
                _ => false,
            }
        }
        Terminator::Call { func: callee, args, dest, target, .. } => {
            // Calls only inside a STEP payload arm, THREADED: the first call
            // at `k`, call p at call p-1's remainder.
            if fuel != FuelLayer::Step || state.ctor.is_none() {
                return false;
            }
            let Some(k_name) = arm.k_name.clone() else {
                return false;
            };
            let Some(callee_idx) =
                cx.members.iter().position(|m| &m.name == callee || &m.def_path == callee)
            else {
                return false;
            };
            let callee_fn = cx.members[callee_idx];
            let Some(target) = target else {
                return false;
            };
            if args.len() != 2 || callee_fn.body.arg_count != 2 || !dest.projections.is_empty() {
                return false;
            }
            let Some(fuel_arg) = resolve_operand(func, &state, &args[0]) else {
                return false;
            };
            let res_dt = peel_indirection(&func.body.return_ty);
            // THREADING gate.
            let fuel_ok = match arm.call_values.last() {
                None => fuel_arg.var_name() == Some(k_name.as_str()),
                Some(prev) => is_remainder_of(&fuel_arg, res_dt, prev),
            };
            if !fuel_ok {
                return false;
            }
            let Some(payload_arg) = resolve_operand(func, &state, &args[1]) else {
                return false;
            };
            // The recursed-on payload must be one of the arm's pattern fields.
            let field_ok =
                payload_arg.var_name().is_some_and(|n| arm.field_names.iter().any(|f| f == n));
            if !field_ok {
                return false;
            }
            let ret_sort = crate::sort_for_ty(peel_indirection(&callee_fn.body.return_ty));
            let call_value = match cx.kind {
                WalkKind::Member => {
                    let ih_name = format!("__ih{ih_counter}");
                    *ih_counter += 1;
                    let ih_var = Formula::var_owned(ih_name.clone(), ret_sort.clone());
                    state.binders.push((ih_name, ret_sort));
                    state.store.insert(dest.local, ih_var.clone());
                    // The REMAINDER-THREADING IH atom: the callee's
                    // postcondition at the threaded fuel.
                    let mut map: HashMap<String, Formula> = HashMap::new();
                    map.insert(
                        crate::place_to_var_name(callee_fn, &Place::local(FUEL_LOCAL)),
                        fuel_arg,
                    );
                    map.insert(
                        crate::place_to_var_name(callee_fn, &Place::local(PAYLOAD_LOCAL)),
                        payload_arg,
                    );
                    map.insert("_0".to_string(), ih_var.clone());
                    state.ih_atoms.push(subst_vars(cx.posts[callee_idx].clone(), &map));
                    ih_var
                }
                WalkKind::Reference => {
                    let app = Formula::FnApp {
                        func: callee_fn.name.clone(),
                        args: vec![fuel_arg, payload_arg],
                        sort: ret_sort,
                    };
                    state.store.insert(dest.local, app.clone());
                    app
                }
            };
            arm.callees.push(callee_fn.name.clone());
            arm.call_values.push(call_value);
            twalk(cx, *target, state, arm, fuel, depth + 1, ih_counter, out)
        }
        _ => false,
    }
}

/// HAND-BUILT fixture builders in the extracted MIR shape — shared by the
/// unit tests below and by trust-integration-tests' end-to-end drive of the
/// literal emitted bundle. Not a public API surface.
#[doc(hidden)]
pub mod fixtures {
    use trust_types::{
        AggregateKind, BasicBlock, LocalDecl, Operand, Rvalue, SourceSpan, Statement,
        VerifiableBody,
    };

    use super::*;

    // ── The threaded 2-member fixture, in the extracted MIR shape ───────────────
    //
    // `ft`/`gt : (&Fuel, &E) -> Res` over `fuel::Fuel = Z | S(*const Fuel)`,
    // `expr::E = A | B(*const E) | M(*const E, *const E)`, and the pair
    // `res::Res = Mk(Fuel, E)`:
    //   ft(Z, e)      = Mk(Z, e)                        (pinned exhaustion)
    //   ft(S k, A)    = Mk(k, A)                        (entry decrement only)
    //   ft(S k, B x)  = let r = gt(k, x); Mk(r.0, B r.1)
    //   ft(S k, M x y)= let r1 = gt(k, x); let r2 = gt(r1.0, y);
    //                   Mk(r2.0, M(r1.1, r2.1))         (REMAINDER THREADING)
    //   gt            = symmetric, calling ft.
    // The references `fr`/`gr` are the same shape as definitional twins.

    pub fn fuel_ref() -> Ty {
        Ty::Datatype { name: "fuel::Fuel".to_string(), variants: Vec::new() }
    }

    pub fn fuel_dt() -> Ty {
        Ty::Datatype {
            name: "fuel::Fuel".to_string(),
            variants: vec![
                ("Z".to_string(), vec![]),
                ("S".to_string(), vec![("0".to_string(), fuel_ref())]),
            ],
        }
    }

    pub fn e_ref() -> Ty {
        Ty::Datatype { name: "expr::E".to_string(), variants: Vec::new() }
    }

    pub fn e_dt() -> Ty {
        Ty::Datatype {
            name: "expr::E".to_string(),
            variants: vec![
                ("A".to_string(), vec![]),
                ("B".to_string(), vec![("0".to_string(), e_ref())]),
                ("M".to_string(), vec![("0".to_string(), e_ref()), ("1".to_string(), e_ref())]),
            ],
        }
    }

    pub fn res_dt() -> Ty {
        Ty::Datatype {
            name: "res::Res".to_string(),
            variants: vec![(
                "Mk".to_string(),
                vec![("0".to_string(), fuel_dt()), ("1".to_string(), e_dt())],
            )],
        }
    }

    pub fn fuel_sort() -> Sort {
        crate::sort_for_ty(&fuel_dt())
    }

    pub fn e_sort() -> Sort {
        crate::sort_for_ty(&e_dt())
    }

    pub fn res_sort() -> Sort {
        crate::sort_for_ty(&res_dt())
    }

    fn local(index: usize, ty: Ty, name: Option<&str>) -> LocalDecl {
        LocalDecl { index, ty, name: name.map(str::to_string) }
    }

    fn assign(place: Place, rvalue: Rvalue) -> Statement {
        Statement::Assign { place, rvalue, span: SourceSpan::default() }
    }

    /// `m fuel e = FnApp(r, [fuel, e])` — the model=reference postcondition.
    pub fn ref_post(r: &str) -> Formula {
        Formula::Eq(
            Box::new(Formula::var_owned("_0".to_string(), res_sort())),
            Box::new(Formula::FnApp {
                func: r.to_string(),
                args: vec![
                    Formula::var_owned("fuel".to_string(), fuel_sort()),
                    Formula::var_owned("e".to_string(), e_sort()),
                ],
                sort: res_sort(),
            }),
        )
    }

    /// One threaded function in the extracted MIR shape (see module tests
    /// header). `thread_second_call = false` is the NEGATIVE control: the
    /// M-arm's second call receives `k` again instead of the first call's
    /// remainder (budget spent twice — not threaded).
    #[allow(clippy::too_many_lines)]
    pub fn threaded_fn(
        name: &str,
        callee: &str,
        post: Vec<Formula>,
        thread_second_call: bool,
    ) -> VerifiableFunction {
        let raw_e = Ty::RawPtr { mutable: false, pointee: Box::new(e_dt()) };
        let adt = |dt: &str, variant: usize, ops: Vec<Operand>| {
            Rvalue::Aggregate(
                AggregateKind::Adt { name: dt.to_string(), variant, active_field: None, args: None },
                ops,
            )
        };
        let disc = |dst: usize, of: usize| {
            assign(
                Place::local(dst),
                Rvalue::Discriminant(Place { local: of, projections: vec![Projection::Deref] }),
            )
        };
        let deref_field = |dst: usize, of: usize, variant: usize, field: usize| {
            assign(
                Place::local(dst),
                Rvalue::Use(Operand::Copy(Place {
                    local: of,
                    projections: vec![
                        Projection::Deref,
                        Projection::Downcast(variant),
                        Projection::Field(field),
                    ],
                })),
            )
        };
        // A direct (non-deref) pair-field read: `dst = of.<field>`.
        let pair_field = |dst: usize, of: usize, field: usize| {
            assign(
                Place::local(dst),
                Rvalue::Use(Operand::Copy(Place {
                    local: of,
                    projections: vec![Projection::Field(field)],
                })),
            )
        };
        let reborrow = |dst: usize, of: usize| {
            assign(
                Place::local(dst),
                Rvalue::Ref {
                    mutable: false,
                    place: Place { local: of, projections: vec![Projection::Deref] },
                },
            )
        };
        // A reference to a local directly (no deref): `dst = &of`.
        let borrow_local = |dst: usize, of: usize| {
            assign(Place::local(dst), Rvalue::Ref { mutable: false, place: Place::local(of) })
        };
        let call = |a: usize, b: usize, dst: usize, next: usize| Terminator::Call {
            is_unsafe_sig: false,
            is_foreign: false,
            func: callee.to_string(),
            args: vec![Operand::Move(Place::local(a)), Operand::Move(Place::local(b))],
            dest: Place::local(dst),
            target: Some(BlockId(next)),
            span: SourceSpan::default(),
            atomic: None,
            unwind: trust_types::UnwindEdge::Unreachable,
        };
        let switch = |d: usize, targets: Vec<(u128, BlockId)>| Terminator::SwitchInt {
            discr: Operand::Move(Place::local(d)),
            targets,
            otherwise: BlockId(1),
            exhaustive_enum_unreachable: true,
            span: SourceSpan::default(),
        };
        let body = VerifiableBody {
            locals: vec![
                local(0, res_dt(), None),
                local(1, Ty::Ref { mutable: false, inner: Box::new(fuel_dt()) }, Some("fuel")),
                local(2, Ty::Ref { mutable: false, inner: Box::new(e_dt()) }, Some("e")),
                local(3, Ty::Int { width: 64, signed: true }, None), // fuel disc
                local(4, fuel_dt(), None),                           // Z value (base)
                local(5, e_dt(), None),                              // e copy (base)
                local(6, Ty::RawPtr { mutable: false, pointee: Box::new(fuel_dt()) }, None), // k
                local(7, Ty::Int { width: 64, signed: true }, None), // payload disc
                local(8, fuel_dt(), None),                           // k copy (arm A rem)
                local(9, e_dt(), None),                              // A value
                local(10, raw_e.clone(), None),                      // B.x read
                local(11, Ty::Ref { mutable: false, inner: Box::new(fuel_dt()) }, None),
                local(12, Ty::Ref { mutable: false, inner: Box::new(e_dt()) }, None),
                local(13, res_dt(), Some("r")), // B call dest
                local(14, fuel_dt(), None),     // r.0
                local(15, e_dt(), None),        // r.1
                local(16, e_dt(), None),        // B(r.1)
                local(17, raw_e.clone(), None), // M.x read
                local(18, raw_e, None),         // M.y read
                local(19, Ty::Ref { mutable: false, inner: Box::new(fuel_dt()) }, None),
                local(20, Ty::Ref { mutable: false, inner: Box::new(e_dt()) }, None),
                local(21, res_dt(), Some("r1")), // M first call dest
                local(22, fuel_dt(), None),      // r1.0
                local(23, Ty::Ref { mutable: false, inner: Box::new(fuel_dt()) }, None),
                local(24, Ty::Ref { mutable: false, inner: Box::new(e_dt()) }, None),
                local(25, res_dt(), Some("r2")), // M second call dest
                local(26, fuel_dt(), None),      // r2.0
                local(27, e_dt(), None),         // r1.1
                local(28, e_dt(), None),         // r2.1
                local(29, e_dt(), None),         // M(r1.1, r2.1)
            ],
            blocks: vec![
                // bb0: fuel switch.
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![disc(3, 1)],
                    terminator: switch(3, vec![(0, BlockId(2)), (1, BlockId(3))]),
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Unreachable },
                // bb2 (fuel Z): _0 = Mk(Z, *e); return-path.
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![
                        assign(Place::local(4), adt("fuel::Fuel", 0, vec![])),
                        assign(
                            Place::local(5),
                            Rvalue::Use(Operand::Copy(Place {
                                local: 2,
                                projections: vec![Projection::Deref],
                            })),
                        ),
                        assign(
                            Place::local(0),
                            adt(
                                "res::Res",
                                0,
                                vec![
                                    Operand::Move(Place::local(4)),
                                    Operand::Move(Place::local(5)),
                                ],
                            ),
                        ),
                    ],
                    terminator: Terminator::Goto(BlockId(12)),
                },
                // bb3 (fuel S): read k; payload switch.
                BasicBlock {
                    id: BlockId(3),
                    stmts: vec![deref_field(6, 1, 1, 0), disc(7, 2)],
                    terminator: switch(7, vec![(0, BlockId(4)), (1, BlockId(5)), (2, BlockId(7))]),
                },
                // bb4 (step A): _0 = Mk(k, A).
                BasicBlock {
                    id: BlockId(4),
                    stmts: vec![
                        assign(
                            Place::local(8),
                            Rvalue::Use(Operand::Copy(Place {
                                local: 6,
                                projections: vec![Projection::Deref],
                            })),
                        ),
                        assign(Place::local(9), adt("expr::E", 0, vec![])),
                        assign(
                            Place::local(0),
                            adt(
                                "res::Res",
                                0,
                                vec![
                                    Operand::Move(Place::local(8)),
                                    Operand::Move(Place::local(9)),
                                ],
                            ),
                        ),
                    ],
                    terminator: Terminator::Goto(BlockId(12)),
                },
                // bb5 (step B): r = callee(k, x) -> bb6.
                BasicBlock {
                    id: BlockId(5),
                    stmts: vec![deref_field(10, 2, 1, 0), reborrow(11, 6), reborrow(12, 10)],
                    terminator: call(11, 12, 13, 6),
                },
                // bb6: _0 = Mk(r.0, B(r.1)).
                BasicBlock {
                    id: BlockId(6),
                    stmts: vec![
                        pair_field(14, 13, 0),
                        pair_field(15, 13, 1),
                        assign(
                            Place::local(16),
                            adt("expr::E", 1, vec![Operand::Copy(Place::local(15))]),
                        ),
                        assign(
                            Place::local(0),
                            adt(
                                "res::Res",
                                0,
                                vec![
                                    Operand::Move(Place::local(14)),
                                    Operand::Move(Place::local(16)),
                                ],
                            ),
                        ),
                    ],
                    terminator: Terminator::Goto(BlockId(12)),
                },
                // bb7 (step M): r1 = callee(k, x) -> bb8.
                BasicBlock {
                    id: BlockId(7),
                    stmts: vec![
                        deref_field(17, 2, 2, 0),
                        deref_field(18, 2, 2, 1),
                        reborrow(19, 6),
                        reborrow(20, 17),
                    ],
                    terminator: call(19, 20, 21, 8),
                },
                // bb8: r2 = callee(r1.0, y) -> bb9 (or callee(k, y): NEGATIVE).
                BasicBlock {
                    id: BlockId(8),
                    stmts: if thread_second_call {
                        vec![pair_field(22, 21, 0), borrow_local(23, 22), reborrow(24, 18)]
                    } else {
                        vec![reborrow(23, 6), reborrow(24, 18)]
                    },
                    terminator: call(23, 24, 25, 9),
                },
                // bb9: _0 = Mk(r2.0, M(r1.1, r2.1)).
                BasicBlock {
                    id: BlockId(9),
                    stmts: vec![
                        pair_field(26, 25, 0),
                        pair_field(27, 21, 1),
                        pair_field(28, 25, 1),
                        assign(
                            Place::local(29),
                            adt(
                                "expr::E",
                                2,
                                vec![
                                    Operand::Copy(Place::local(27)),
                                    Operand::Copy(Place::local(28)),
                                ],
                            ),
                        ),
                        assign(
                            Place::local(0),
                            adt(
                                "res::Res",
                                0,
                                vec![
                                    Operand::Move(Place::local(26)),
                                    Operand::Move(Place::local(29)),
                                ],
                            ),
                        ),
                    ],
                    terminator: Terminator::Goto(BlockId(12)),
                },
                BasicBlock { id: BlockId(10), stmts: vec![], terminator: Terminator::Unreachable },
                BasicBlock { id: BlockId(11), stmts: vec![], terminator: Terminator::Unreachable },
                // bb12: return.
                BasicBlock { id: BlockId(12), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 2,
            return_ty: res_dt(),
        };
        VerifiableFunction {
            name: name.to_string(),
            def_path: name.to_string(),
            span: SourceSpan::default(),
            body,
            contracts: vec![],
            preconditions: vec![],
            postconditions: post,
            spec: Default::default(),
        }
    }

    /// The full model-vs-reference fixture: model {ft, gt}, reference {fr, gr}.
    pub fn threaded_cluster() -> Vec<VerifiableFunction> {
        vec![
            threaded_fn("ft", "gt", vec![ref_post("fr")], true),
            threaded_fn("gt", "ft", vec![ref_post("gr")], true),
            threaded_fn("fr", "gr", vec![], true),
            threaded_fn("gr", "fr", vec![], true),
        ]
    }
}

#[cfg(test)]
mod tests {
    use super::fixtures::*;
    use super::*;

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

    fn properties(vcs: &[VerificationCondition]) -> Vec<String> {
        vcs.iter()
            .map(|vc| match &vc.kind {
                VcKind::FunctionalCorrectness { property, .. } => property.clone(),
                other => panic!("expected FunctionalCorrectness, got {other:?}"),
            })
            .collect()
    }

    // ── Test 1: the threaded bundle shape ────────────────────────────────────────

    #[test]
    fn test_threaded_cluster_emits_bundle() {
        let funcs = threaded_cluster();
        let vcs = threaded_budget_functional_vcs(&funcs);
        assert_eq!(
            properties(&vcs),
            vec![
                "threaded_budget_functional_base::ft",
                "threaded_budget_functional_case::ft::A[calls=]",
                "threaded_budget_functional_case::ft::B[calls=gt]",
                "threaded_budget_functional_case::ft::M[calls=gt,gt]",
                "threaded_budget_functional_base::gt",
                "threaded_budget_functional_case::gt::A[calls=]",
                "threaded_budget_functional_case::gt::B[calls=ft]",
                "threaded_budget_functional_case::gt::M[calls=ft,ft]",
                "threaded_budget_functional_refbase::fr",
                "threaded_budget_functional_refstep::fr::A[calls=]",
                "threaded_budget_functional_refstep::fr::B[calls=gr]",
                "threaded_budget_functional_refstep::fr::M[calls=gr,gr]",
                "threaded_budget_functional_refbase::gr",
                "threaded_budget_functional_refstep::gr::A[calls=]",
                "threaded_budget_functional_refstep::gr::B[calls=fr]",
                "threaded_budget_functional_refstep::gr::M[calls=fr,fr]",
                "threaded_budget_functional_conclusion[threaded-induction:\
                 fuel=fuel::Fuel:Z|S;res=res::Res:Mk;data=expr::E;members=ft,gt;\
                 bases=2;cases=6;refs=fr,gr;refbases=2;refcases=6]",
            ],
            "bundle: {vcs:#?}"
        );

        // The M step arm of ft carries the REMAINDER-THREADING IH atoms
        // (the B arm consumed `__ih0`, so the M arm binds `__ih1`/`__ih2`):
        // atom 1's fuel argument is `__ih1.0` — a Sel of atom 0's result.
        let Formula::Forall(binders, body) = &vcs[3].formula else {
            panic!("step M case must be a Forall, got {:?}", vcs[3].formula);
        };
        assert_eq!(
            binders.iter().map(|(s, _)| s.as_str()).collect::<Vec<_>>(),
            vec!["__fld_S_0", "__fld_M_0", "__fld_M_1", "__ih1", "__ih2"],
        );
        let Formula::Implies(ih, concl) = body.as_ref() else {
            panic!("step M body must be IHs => conclusion, got {body:?}");
        };
        let Formula::And(atoms) = ih.as_ref() else {
            panic!("two-call arm must carry an And of two IH atoms, got {ih:?}");
        };
        // Atom 0: `__ih1 = gr(__fld_S_0, __fld_M_0)` — the entry decrement.
        let Formula::Eq(l0, r0) = &atoms[0] else { panic!("atom 0 must be Eq") };
        assert_eq!(l0.var_name(), Some("__ih1"));
        let Formula::FnApp { func, args, .. } = r0.as_ref() else {
            panic!("atom 0 rhs must be the callee's reference application");
        };
        assert_eq!(func, "gr");
        assert_eq!(args[0].var_name(), Some("__fld_S_0"));
        // Atom 1: `__ih2 = gr(__ih1.0, __fld_M_1)` — the THREADED remainder.
        let Formula::Eq(l1, r1) = &atoms[1] else { panic!("atom 1 must be Eq") };
        assert_eq!(l1.var_name(), Some("__ih2"));
        let Formula::FnApp { func, args, .. } = r1.as_ref() else {
            panic!("atom 1 rhs must be the callee's reference application");
        };
        assert_eq!(func, "gr");
        let Formula::Sel { datatype, field, arg, .. } = &args[0] else {
            panic!("atom 1's fuel must be the previous call's REMAINDER, got {:?}", args[0]);
        };
        assert_eq!(datatype, "res::Res");
        assert_eq!(field, "0");
        assert_eq!(arg.var_name(), Some("__ih1"));
        // Conclusion: `Mk(__ih2.0, M(__ih1.1, __ih2.1)) = fr(S k, M(x, y))`.
        let Formula::Eq(c_l, c_r) = concl.as_ref() else { panic!() };
        let Formula::Ctor { ctor, args: mk_args, .. } = c_l.as_ref() else {
            panic!("conclusion lhs must be the rebuilt pair, got {c_l:?}");
        };
        assert_eq!(ctor, "Mk");
        let Formula::Sel { arg, .. } = &mk_args[0] else {
            panic!("returned remainder must be the LAST call's, got {:?}", mk_args[0]);
        };
        assert_eq!(arg.var_name(), Some("__ih2"));
        let Formula::FnApp { func, .. } = c_r.as_ref() else { panic!() };
        assert_eq!(func, "fr");

        // The refstep M VC chains the definitional FnApps through Sel.
        let Formula::Forall(_, body) = &vcs[11].formula else { panic!() };
        let Formula::Eq(_, rhs) = body.as_ref() else { panic!() };
        let Formula::Ctor { args: mk_args, .. } = rhs.as_ref() else { panic!() };
        let Formula::Sel { arg, .. } = &mk_args[0] else {
            panic!("refstep remainder must be a Sel, got {:?}", mk_args[0]);
        };
        let Formula::FnApp { func, args, .. } = arg.as_ref() else {
            panic!("refstep remainder must select from the second call, got {arg:?}");
        };
        assert_eq!(func, "gr");
        let Formula::Sel { arg: inner, .. } = &args[0] else {
            panic!("the second ref call's fuel must be the first call's remainder");
        };
        let Formula::FnApp { func, .. } = inner.as_ref() else { panic!() };
        assert_eq!(func, "gr");
    }

    #[test]
    fn test_u8_wraparound_postcondition_outside_lane_shape_emits_nothing() {
        let mut funcs = threaded_cluster();
        funcs[0].postconditions = vec![u8_wraparound_post()];
        let vcs = threaded_budget_functional_vcs(&funcs);
        assert!(
            vcs.is_empty(),
            "the threaded lane requires an exact reference postcondition; arithmetic makes this SCC out of shape"
        );
    }

    // ── Test 2: gates fail closed ────────────────────────────────────────────────

    #[test]
    fn test_non_threaded_second_call_fails_closed() {
        // The M arm's second call receives `k` again (budget spent twice).
        let funcs = vec![
            threaded_fn("ft", "gt", vec![ref_post("fr")], false),
            threaded_fn("gt", "ft", vec![ref_post("gr")], true),
            threaded_fn("fr", "gr", vec![], true),
            threaded_fn("gr", "fr", vec![], true),
        ];
        assert!(
            threaded_budget_functional_vcs(&funcs).is_empty(),
            "a second call at the un-threaded `k` must not emit a threaded bundle"
        );
    }

    #[test]
    fn test_non_threaded_reference_fails_closed() {
        let funcs = vec![
            threaded_fn("ft", "gt", vec![ref_post("fr")], true),
            threaded_fn("gt", "ft", vec![ref_post("gr")], true),
            threaded_fn("fr", "gr", vec![], false),
            threaded_fn("gr", "fr", vec![], true),
        ];
        assert!(
            threaded_budget_functional_vcs(&funcs).is_empty(),
            "an un-threaded REFERENCE must fail the whole bundle closed"
        );
    }

    #[test]
    fn test_missing_reference_fails_closed() {
        let funcs = vec![
            threaded_fn("ft", "gt", vec![ref_post("fr")], true),
            threaded_fn("gt", "ft", vec![ref_post("gr")], true),
        ];
        assert!(
            threaded_budget_functional_vcs(&funcs).is_empty(),
            "the reference set must be in scope"
        );
    }

    #[test]
    fn test_ctor_tree_post_fails_closed() {
        // This lane has no constructor-tree postcondition mode: the remainder
        // component has no closed form.
        let identity = Formula::Eq(
            Box::new(Formula::var_owned("_0".to_string(), res_sort())),
            Box::new(Formula::var_owned("e".to_string(), e_sort())),
        );
        let funcs = vec![
            threaded_fn("ft", "gt", vec![identity.clone()], true),
            threaded_fn("gt", "ft", vec![identity], true),
        ];
        assert!(threaded_budget_functional_vcs(&funcs).is_empty());
    }

    #[test]
    fn test_self_scc_of_one_emits_nothing() {
        let funcs = vec![
            threaded_fn("ft", "ft", vec![ref_post("fr")], true),
            threaded_fn("fr", "fr", vec![], true),
        ];
        assert!(threaded_budget_functional_vcs(&funcs).is_empty());
    }
}
