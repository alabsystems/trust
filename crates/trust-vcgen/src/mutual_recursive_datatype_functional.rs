// trust-vcgen/mutual_recursive_datatype_functional.rs: WALL C scaled to
// MUTUAL SCCs — the fuel-indexed mutual-cluster INDUCTION VC lane.
//
// The sibling lane `recursive_datatype_functional` is the recursion PRIMITIVE:
// structural induction VCs for a SELF-recursive function (call-graph SCC of
// size 1). This lane is the MUTUAL increment — the named next wall of the
// literal-fidelity front, mirroring the Aristotle-proved template
// `MutualCluster.lean` (a genuine 3-function SCC `infer <-> whnf <-> defEq`,
// fuel-indexed, per-arm step VCs over a uniform IH-atom bundle, base VCs at
// fuel 0, assembled by ONE joint induction on fuel with a product motive).
//
// SHAPE DETECTED (fail-closed outside it): a call-graph SCC of size N > 1
// whose members all have the extracted fuel-indexed form
//
//   fn m(fuel: &Fuel, e: &E) -> E {
//       match fuel {
//           Fuel::Z    => <base: match e per-ctor, or a direct return; NO calls>
//           Fuel::S(k) => match e {
//               C(..) => <arm result; cluster-member calls at fuel k>
//               ...
//           }
//       }
//   }
//
// where `Fuel` is a modeled nat-shaped `Ty::Datatype` (one nullary + one
// unary-recursive constructor — the total-model fuel index; the real kernel
// cluster's termination is SN-based, the extracted total shape is fuel-indexed
// exactly as the template documents) and `E` is a modeled payload datatype
// shared by all members. Every recursive call may target ANY cluster member —
// that is what makes the bundle MUTUAL — and must pass the one-step-smaller
// fuel `k` (fuel-decreasing, checked; a non-decreasing call would make the
// `[mutual-induction:..]` tag a lie).
//
// EMITTED BUNDLE (per SCC), the machine twin of the template's VC view:
//   * BASE VCs (fuel = Z), per member: either one per payload constructor
//       `mutual_recursive_datatype_functional_base::<m>::<C>`
//       `Forall [fields] P_m(pattern, arm-result)`
//     or a single direct-return VC
//       `mutual_recursive_datatype_functional_base::<m>`
//       `Forall [e] P_m(e, result)`
//     (the template's `vc_*_fuelZero` legs; no IH at fuel 0);
//   * STEP VCs (fuel = S k), per member per payload constructor:
//       `mutual_recursive_datatype_functional_case::<m>::<C>[calls=c1,..]`
//       `Forall [k, fields, ihs] (Implies (And IH-atoms) P_m(pattern, result))`
//     where each IH atom is the CALLEE's postcondition assumed at the smaller
//     fuel — `P_cj(call-args, __ih_j)` — the instantiated form of the
//     template's uniform bundle (`ihI, ihW, ihD`): in a mutual SCC a call to
//     ANY member becomes an IH atom, and `[calls=..]` records which member
//     each atom belongs to (the joint discharge must project the RIGHT
//     component of the product IH — member identity is load-bearing);
//   * ONE JOINT CONCLUSION VC for the whole cluster:
//       `mutual_recursive_datatype_functional_conclusion[mutual-induction:
//        fuel=<dt>:<Z>|<S>;data=<dt>;members=<m1,..>;bases=<nb>;cases=<nc>]`
//       `And [Forall [fuel, e] P_1, ..., Forall [fuel, e] P_N]`
//     (conjunct i is member i's statement, `_0` denoting THAT member's
//     output — the template's `cluster_agrees_assembled` AndType), tagged so
//     no consumer can treat any single conjunct as independently discharged:
//     it is discharged BY MUTUAL INDUCTION FROM THE CASES or not at all.
//
// SOUNDNESS: this module only PRODUCES proof obligations; it discharges none.
// Fail-closed on: SCC not fully in scope, missing postconditions, non-2-param
// members, a first match not on a nat-shaped fuel param, payload datatype
// mismatch across members, calls outside the cluster, calls not passing the
// one-step-smaller fuel, calls in the base arm, uncovered constructors,
// marker-hostile names. A partial mutual bundle is not a proof plan.
//
// LITERAL-CLUSTER EXTENSIONS (the three named items of the mutual lane):
//   1. MULTI-IH CONSTRUCTORS: a payload constructor may have SEVERAL recursive
//      fields (`Max`/`IMax(Level, Level)`), so one step arm may carry several
//      cluster calls — each becomes its own IH atom, `[calls=..]` records the
//      callee per atom in order.
//   2. NON-DATATYPE PAYLOAD FIELDS: a constructor field of a NON-modeled type
//      (`Param(Name)` — the `Name` field is opaque) is bound as a universally
//      quantified OPAQUE atom: its binder sort is the by-name uninterpreted
//      `Sort::Datatype { name, constructors: [] }` of its `Ty::Adt`. The VC
//      only ever moves such an atom around (pattern -> result); no formula
//      inspects it.
//   3. FUNCTION-VS-FUNCTION POSTCONDITIONS (model = reference): a member's
//      postcondition may be `Eq(_0, FnApp(ref, [fuel, e]))` naming a second
//      REFERENCE function (the `bootstrap_model_fidelity` shape). The
//      reference set (closed under its own calls) must itself be a
//      fuel-indexed cluster over the same fuel/payload datatypes; its arms are
//      emitted as DEFINITIONAL transport VCs
//        `..._refbase::<r>[::<C>]`   `Forall [fields] Eq(FnApp(r,[Z,pat]), result)`
//        `..._refstep::<r>::<C>[calls=..]`
//                                    `Forall [k, fields] Eq(FnApp(r,[S k,pat]),
//                                                           result-with-FnApp-calls)`
//      (true by definition of `r`; the discharge side rebuilds `r` as a fold
//      and checks them by iota), and the conclusion marker gains
//      `;refs=..;refbases=..;refcases=..` so a dropped ref VC fails closed.
//      Postcondition modes may not be mixed across members.
//
// HONESTY: this is the recursion primitive SCALED to mutual — still
// fuel-indexed. The literal `infer_type <-> whnf <-> is_def_eq` cluster
// additionally needs SN-vs-fuel (the real cluster's termination is SN-based)
// and extraction serialization — named, out of scope here.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::HashMap;

use trust_types::{
    BlockId, Formula, Place, Projection, Sort, Terminator, Ty, VcKind, VerifiableFunction,
    VerificationCondition,
};

use crate::call_graph::{build_call_graph, detect_cycles};
use crate::recursive_datatype_functional::{
    WalkState, apply_stmt, conjoin_all, discriminant_place, local_ty, param_var, peel_indirection,
    resolve_operand, resolve_place, subst_post,
};

/// Property tag prefix of a BASE (fuel = 0) VC:
/// `..._base::<member>` (direct return) or `..._base::<member>::<Ctor>`.
pub const MUTUAL_BASE_PROPERTY_PREFIX: &str = "mutual_recursive_datatype_functional_base::";
/// Property tag prefix of a STEP (fuel = S k) case VC:
/// `..._case::<member>::<Ctor>[calls=<c1,..>]`.
pub const MUTUAL_CASE_PROPERTY_PREFIX: &str = "mutual_recursive_datatype_functional_case::";
/// Property tag prefix of the joint CONCLUSION VC (suffixed with the
/// `[mutual-induction:..]` bundle marker).
pub const MUTUAL_CONCLUSION_PROPERTY_PREFIX: &str =
    "mutual_recursive_datatype_functional_conclusion";
/// Property tag prefix of a REFERENCE-function BASE definitional VC (the
/// function-vs-function postcondition mode):
/// `..._refbase::<ref>` (direct return) or `..._refbase::<ref>::<Ctor>`.
pub const MUTUAL_REF_BASE_PROPERTY_PREFIX: &str = "mutual_recursive_datatype_functional_refbase::";
/// Property tag prefix of a REFERENCE-function STEP definitional VC:
/// `..._refstep::<ref>::<Ctor>[calls=<c1,..>]`.
pub const MUTUAL_REF_STEP_PROPERTY_PREFIX: &str = "mutual_recursive_datatype_functional_refstep::";

/// Which fuel arm the walk is currently under.
#[derive(Clone, Copy, PartialEq, Eq)]
enum FuelLayer {
    /// Before the fuel match.
    None,
    /// Under the nullary fuel constructor (fuel = 0): calls are FORBIDDEN.
    Base,
    /// Under the unary fuel constructor (fuel = S k): cluster calls at `k`.
    Step,
}

/// One completed per-constructor arm (base or step).
struct ArmRec {
    tag: usize,
    ctor: String,
    /// Callee member names, one per IH atom in the arm's formula (step arms
    /// only; empty for base arms).
    callees: Vec<String>,
    formula: Formula,
}

/// Everything the walk learns about one member.
#[derive(Default)]
struct MemberOut {
    /// The fuel parameter's datatype (recorded at the first switch).
    fuel_dt: Option<Ty>,
    fuel_z: Option<(usize, String)>,
    fuel_s: Option<(usize, String)>,
    /// The payload parameter's datatype (recorded at the payload switch).
    payload_dt: Option<Ty>,
    /// Direct-return base arms (no payload match). At most one is in scope.
    base_direct: Vec<Formula>,
    base_arms: Vec<ArmRec>,
    step_arms: Vec<ArmRec>,
}

/// The fuel parameter is the FIRST parameter and the payload the SECOND —
/// the uniform extracted-cluster signature this lane models.
const FUEL_LOCAL: usize = 1;
const PAYLOAD_LOCAL: usize = 2;

/// How the walk treats cluster calls.
#[derive(Clone, Copy, PartialEq, Eq)]
enum WalkKind {
    /// A cluster MEMBER: every call becomes an IH atom (the callee's
    /// postcondition assumed at the smaller fuel).
    Member,
    /// A REFERENCE function (function-vs-function mode): every call becomes
    /// the definitional application `FnApp(callee, [k, arg])` inline — no IH.
    Reference,
}

/// The binder sort of one payload-constructor FIELD. A field of a modeled
/// datatype keeps its datatype sort (a recursive payload field is the by-name
/// reference); a field of a non-modeled `Ty::Adt` (e.g. `Param(Name)`'s
/// opaque `Name`) becomes a universally-quantified OPAQUE atom: a by-name
/// uninterpreted `Sort::Datatype { name, constructors: [] }`. Everything else
/// (scalars, tuples, ...) is out of scope — `None` fails the bundle closed.
fn payload_field_sort(fty: &Ty) -> Option<Sort> {
    match peel_indirection(fty) {
        dt @ Ty::Datatype { .. } => Some(crate::sort_for_ty(dt)),
        Ty::Adt { name, .. } if is_marker_safe_path(name) => {
            Some(Sort::Datatype { name: name.clone(), constructors: Vec::new() })
        }
        _ => None,
    }
}

/// In function-vs-function mode, the member's postcondition names its
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
/// against: `Eq(FnApp(r, [fuel, e]), _0)` — substituting the arm's pattern and
/// result yields the per-arm transport equation, true by definition of `r`.
fn ref_pseudo_post(func: &VerifiableFunction) -> Option<Formula> {
    let fuel = param_var(func, FUEL_LOCAL)?;
    let e = param_var(func, PAYLOAD_LOCAL)?;
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

/// Emit the mutual-induction VC bundles for every call-graph SCC of size > 1
/// in `funcs`. Each SCC is attempted independently and fails closed on its
/// own (an out-of-scope SCC emits nothing without poisoning the others).
#[must_use]
pub fn mutual_recursive_datatype_functional_vcs(
    funcs: &[VerifiableFunction],
) -> Vec<VerificationCondition> {
    let graph = build_call_graph(funcs);
    let mut out = Vec::new();
    for scc in detect_cycles(&graph) {
        if scc.members.len() < 2 {
            continue;
        }
        // Resolve members (Tarjan already sorted them — the canonical order).
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
                        "mutual recursive-datatype functional induction",
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

/// Emit the bundle for ONE mutual cluster. `None` (fail-closed) on any
/// out-of-scope shape. `funcs` is the full in-scope function set — the
/// function-vs-function mode resolves REFERENCE functions from it.
#[allow(clippy::too_many_lines)]
fn emit_cluster(
    members: &[&VerifiableFunction],
    funcs: &[VerifiableFunction],
) -> Option<Vec<VerificationCondition>> {
    // Uniform signature + spec gates.
    let names: Vec<&str> = members.iter().map(|f| f.name.as_str()).collect();
    {
        let mut sorted = names.clone();
        sorted.sort_unstable();
        sorted.dedup();
        if sorted.len() != names.len() {
            return None; // ambiguous member names cannot label the bundle
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

    // Postcondition MODE: every member `_0 = ctor-tree(e)` (the original
    // shape) or every member `_0 = FnApp(ref, [fuel, e])` (function-vs-
    // function). Mixed modes fail closed.
    let ref_targets: Vec<Option<&str>> =
        members.iter().zip(&posts).map(|(f, p)| ref_fn_target(f, p)).collect();
    let ref_mode = ref_targets.iter().all(Option::is_some);
    if !ref_mode && ref_targets.iter().any(Option::is_some) {
        return None;
    }

    // Walk every member.
    let mut outs: Vec<MemberOut> = Vec::with_capacity(members.len());
    for (idx, func) in members.iter().enumerate() {
        let entry = func.body.blocks.first()?;
        let mut mo = MemberOut::default();
        let mut ih_counter = 0usize;
        let ok = mwalk(
            members,
            &posts,
            WalkKind::Member,
            idx,
            entry.id,
            WalkState::default(),
            Vec::new(),
            FuelLayer::None,
            None,
            0,
            &mut ih_counter,
            &mut mo,
        );
        if !ok {
            return None;
        }
        outs.push(mo);
    }

    // Function-vs-function mode: resolve the REFERENCE set — the named refs
    // closed under their own calls — and walk each in definitional mode.
    let mut refs: Vec<&VerifiableFunction> = Vec::new();
    let mut ref_outs: Vec<MemberOut> = Vec::new();
    if ref_mode {
        let mut queue: Vec<String> =
            ref_targets.iter().map(|t| t.map(str::to_string)).collect::<Option<Vec<_>>>()?;
        let mut qi = 0usize;
        while qi < queue.len() {
            let target = queue[qi].clone();
            qi += 1;
            let func = funcs.iter().find(|f| f.name == target || f.def_path == target)?;
            if refs.iter().any(|r| r.name == func.name) {
                continue;
            }
            // The reference set must be DISJOINT from the cluster (a member
            // cannot be its own reference) and uniformly shaped.
            if names.contains(&func.name.as_str())
                || !is_marker_safe_segment(&func.name)
                || func.body.arg_count != 2
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
            let ok = mwalk(
                &refs,
                &pseudo,
                WalkKind::Reference,
                idx,
                entry.id,
                WalkState::default(),
                Vec::new(),
                FuelLayer::None,
                None,
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

    // Cross-member consistency: one fuel datatype, one payload datatype —
    // across members AND references.
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
    if !is_marker_safe_path(fuel_name)
        || !is_marker_safe_path(payload_name)
        || !is_marker_safe_segment(&fuel_z.1)
        || !is_marker_safe_segment(&fuel_s.1)
        || !payload_variants.iter().all(|(c, _)| is_marker_safe_segment(c))
    {
        return None;
    }
    for mo in outs.iter().chain(&ref_outs) {
        let (Some(fdt), Some(pdt)) = (&mo.fuel_dt, &mo.payload_dt) else {
            return None;
        };
        let (Ty::Datatype { name: fname, .. }, Ty::Datatype { name: pname, variants: pvars }) =
            (fdt, pdt)
        else {
            return None;
        };
        if fname != fuel_name || pname != payload_name {
            return None;
        }
        // The FULL variant structure (names, arities, field types) must agree
        // — a field-kind mismatch (recursive vs opaque) is a different type.
        if pvars != payload_variants {
            return None;
        }
        if mo.fuel_z != Some(fuel_z.clone()) || mo.fuel_s != Some(fuel_s.clone()) {
            return None;
        }
    }

    // Coverage: for each member/reference the step arms — and the base arms,
    // unless the base is a single direct return — cover every payload
    // constructor exactly once, in tag order.
    let all_tags: Vec<usize> = (0..payload_variants.len()).collect();
    let covered = |arms: &[ArmRec]| -> bool {
        let mut tags: Vec<usize> = arms.iter().map(|a| a.tag).collect();
        tags.sort_unstable();
        tags == all_tags
    };
    for mo in outs.iter_mut().chain(ref_outs.iter_mut()) {
        mo.base_arms.sort_by_key(|a| a.tag);
        mo.step_arms.sort_by_key(|a| a.tag);
        if !covered(&mo.step_arms) {
            return None;
        }
        match (mo.base_direct.len(), mo.base_arms.len()) {
            (1, 0) => {}
            (0, _) if covered(&mo.base_arms) => {}
            _ => return None,
        }
    }

    // Assemble the bundle: per member (canonical order) base VCs then step
    // VCs, then (function-vs-function mode) the reference definitional VCs,
    // then the joint conclusion.
    let mut vcs: Vec<VerificationCondition> = Vec::new();
    let mut n_bases = 0usize;
    let mut n_cases = 0usize;
    for ((func, mo), name) in members.iter().zip(&outs).zip(&names) {
        let mk = |property: String, formula: Formula| VerificationCondition {
            kind: VcKind::FunctionalCorrectness { property, context: (*name).to_string() },
            function: (*name).into(),
            location: func.span.clone(),
            formula,
            contract_metadata: None,
        };
        if let [direct] = mo.base_direct.as_slice() {
            // Direct base return: quantify the payload parameter itself.
            let e_name = crate::place_to_var_name(func, &Place::local(PAYLOAD_LOCAL));
            let e_sort = crate::sort_for_ty(peel_indirection(local_ty(func, PAYLOAD_LOCAL)?));
            let formula = Formula::forall(&[(e_name.as_str(), e_sort)], direct.clone());
            vcs.push(mk(format!("{MUTUAL_BASE_PROPERTY_PREFIX}{name}"), formula));
            n_bases += 1;
        } else {
            for arm in &mo.base_arms {
                vcs.push(mk(
                    format!("{MUTUAL_BASE_PROPERTY_PREFIX}{name}::{}", arm.ctor),
                    arm.formula.clone(),
                ));
                n_bases += 1;
            }
        }
        for arm in &mo.step_arms {
            vcs.push(mk(
                format!(
                    "{MUTUAL_CASE_PROPERTY_PREFIX}{name}::{}[calls={}]",
                    arm.ctor,
                    arm.callees.join(",")
                ),
                arm.formula.clone(),
            ));
            n_cases += 1;
        }
    }

    // Reference definitional VCs (function-vs-function mode only): the
    // transported arm equations, true by definition of each reference.
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
        };
        if let [direct] = mo.base_direct.as_slice() {
            let e_name = crate::place_to_var_name(func, &Place::local(PAYLOAD_LOCAL));
            let e_sort = crate::sort_for_ty(peel_indirection(local_ty(func, PAYLOAD_LOCAL)?));
            let formula = Formula::forall(&[(e_name.as_str(), e_sort)], direct.clone());
            vcs.push(mk(format!("{MUTUAL_REF_BASE_PROPERTY_PREFIX}{name}"), formula));
            n_refbases += 1;
        } else {
            for arm in &mo.base_arms {
                vcs.push(mk(
                    format!("{MUTUAL_REF_BASE_PROPERTY_PREFIX}{name}::{}", arm.ctor),
                    arm.formula.clone(),
                ));
                n_refbases += 1;
            }
        }
        for arm in &mo.step_arms {
            vcs.push(mk(
                format!(
                    "{MUTUAL_REF_STEP_PROPERTY_PREFIX}{name}::{}[calls={}]",
                    arm.ctor,
                    arm.callees.join(",")
                ),
                arm.formula.clone(),
            ));
            n_refcases += 1;
        }
    }

    // The joint conclusion: conjunct i is member i's `Forall [fuel, e] P_i`
    // (`_0` denotes THAT member's output), bound to the cases by the marker.
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
        let refs: Vec<(&str, Sort)> =
            binders.iter().map(|(n, s)| (n.as_str(), s.clone())).collect();
        conjuncts.push(Formula::forall(&refs, post.clone()));
    }
    let mut marker = format!(
        "[mutual-induction:fuel={fuel_name}:{}|{};data={payload_name};members={};bases={n_bases};cases={n_cases}",
        fuel_z.1,
        fuel_s.1,
        names.join(",")
    );
    if ref_mode {
        let ref_names: Vec<&str> = refs.iter().map(|f| f.name.as_str()).collect();
        marker.push_str(&format!(
            ";refs={};refbases={n_refbases};refcases={n_refcases}",
            ref_names.join(",")
        ));
    }
    marker.push(']');
    let joint = names.join("+");
    vcs.push(VerificationCondition {
        kind: VcKind::FunctionalCorrectness {
            property: format!("{MUTUAL_CONCLUSION_PROPERTY_PREFIX}{marker}"),
            context: joint.clone(),
        },
        function: joint.into(),
        location: members[0].span.clone(),
        formula: Formula::And(conjuncts),
        contract_metadata: None,
    });
    Some(vcs)
}

/// `true` iff `s` can sit inside the property markers without colliding with
/// a delimiter (`::`-free segment form: member and constructor names).
/// `pub(crate)`: shared with the `threaded_budget_functional` and
/// `fuel_outcome_functional` sibling lanes.
pub(crate) fn is_marker_safe_segment(s: &str) -> bool {
    !s.is_empty() && s.chars().all(|c| c.is_alphanumeric() || c == '_')
}

/// `true` iff `s` can sit inside the property markers as a datatype path
/// (`::` allowed; marker delimiters and `:`/`|` inside a single segment not).
pub(crate) fn is_marker_safe_path(s: &str) -> bool {
    !s.is_empty() && s.split("::").all(is_marker_safe_segment)
}

/// Nat-shape gate for the fuel datatype: exactly one nullary constructor and
/// one unary constructor whose field is (an indirection of) the datatype
/// itself. Returns `((z_tag, z_ctor), (s_tag, s_ctor))`.
pub(crate) fn nat_shape(dt: &Ty) -> Option<((usize, String), (usize, String))> {
    let Ty::Datatype { name, variants } = dt else {
        return None;
    };
    if variants.len() != 2 {
        return None;
    }
    let mut z = None;
    let mut s = None;
    for (tag, (ctor, fields)) in variants.iter().enumerate() {
        match fields.as_slice() {
            [] => {
                if z.replace((tag, ctor.clone())).is_some() {
                    return None;
                }
            }
            [(_, fty)] => {
                let Ty::Datatype { name: fname, .. } = peel_indirection(fty) else {
                    return None;
                };
                if fname != name || s.replace((tag, ctor.clone())).is_some() {
                    return None;
                }
            }
            _ => return None,
        }
    }
    Some((z?, s?))
}

/// Bounded CFG walk for one member of the cluster (or one REFERENCE function
/// in definitional mode). Returns `false` (fail-closed for the WHOLE cluster)
/// on any unmodeled construct along a `Return`-reaching path. `callees` stays
/// aligned with `state.ih_atoms` in member mode; in reference mode it simply
/// records the arm's call targets in order.
#[allow(clippy::too_many_arguments, clippy::too_many_lines)]
fn mwalk(
    members: &[&VerifiableFunction],
    posts: &[Formula],
    kind: WalkKind,
    member_idx: usize,
    block_id: BlockId,
    mut state: WalkState,
    mut callees: Vec<String>,
    fuel: FuelLayer,
    fuel_field: Option<String>,
    depth: usize,
    ih_counter: &mut usize,
    out: &mut MemberOut,
) -> bool {
    if depth > 64 {
        return false;
    }
    let func = members[member_idx];
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
            let post = &posts[member_idx];
            match (fuel, state.ctor.clone()) {
                // A return before the fuel match is not a fuel-indexed arm.
                (FuelLayer::None, _) => false,
                (FuelLayer::Base, None) => {
                    // Direct base return: no arm binders, no IH.
                    if !state.binders.is_empty() || !state.ih_atoms.is_empty() {
                        return false;
                    }
                    out.base_direct.push(subst_post(func, post, &state, result));
                    out.base_direct.len() == 1
                }
                (FuelLayer::Base, Some((tag, ctor))) => {
                    if !state.ih_atoms.is_empty() {
                        return false;
                    }
                    let body = subst_post(func, post, &state, result);
                    out.base_arms.push(ArmRec {
                        tag,
                        ctor,
                        callees: Vec::new(),
                        formula: close_over(&state.binders, body),
                    });
                    true
                }
                // A step return outside any payload arm cannot be a case.
                (FuelLayer::Step, None) => false,
                (FuelLayer::Step, Some((tag, ctor))) => {
                    let conclusion = subst_post(func, post, &state, result);
                    let body = if state.ih_atoms.is_empty() {
                        conclusion
                    } else {
                        Formula::Implies(
                            Box::new(conjoin_all(state.ih_atoms.clone())),
                            Box::new(conclusion),
                        )
                    };
                    out.step_arms.push(ArmRec {
                        tag,
                        ctor,
                        callees,
                        formula: close_over(&state.binders, body),
                    });
                    true
                }
            }
        }
        Terminator::Goto(target) => mwalk(
            members,
            posts,
            kind,
            member_idx,
            *target,
            state,
            callees,
            fuel,
            fuel_field,
            depth + 1,
            ih_counter,
            out,
        ),
        Terminator::Assert { target, .. } | Terminator::Drop { target, .. } => mwalk(
            members,
            posts,
            kind,
            member_idx,
            *target,
            state,
            callees,
            fuel,
            fuel_field,
            depth + 1,
            ih_counter,
            out,
        ),
        // A dead arm (rustc's exhaustive-match `otherwise -> Unreachable`)
        // contributes no case and does not poison the bundle.
        Terminator::Unreachable => true,
        Terminator::SwitchInt { discr, targets, .. } => {
            let Some(matched) = discriminant_place(&state, discr) else {
                return false;
            };
            if !matched.projections.iter().all(|p| matches!(p, Projection::Deref)) {
                return false;
            }
            match (fuel, &state.ctor) {
                // Layer 1: the FUEL match, on the first parameter.
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
                        let (layer, field) = if tag == z_tag {
                            arm_state.store.insert(
                                FUEL_LOCAL,
                                Formula::Ctor {
                                    ctor: z_ctor.clone(),
                                    args: vec![],
                                    sort: dt_sort.clone(),
                                },
                            );
                            (FuelLayer::Base, None)
                        } else {
                            // Bind the one-step-smaller fuel `k`.
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
                            (FuelLayer::Step, Some(k_name))
                        };
                        if !mwalk(
                            members,
                            posts,
                            kind,
                            member_idx,
                            *target,
                            arm_state,
                            callees.clone(),
                            layer,
                            field,
                            depth + 1,
                            ih_counter,
                            out,
                        ) {
                            return false;
                        }
                    }
                    true
                }
                // Layer 2: the PAYLOAD match, on the second parameter.
                (FuelLayer::Base | FuelLayer::Step, None) => {
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
                        let mut field_vars = Vec::with_capacity(fields.len());
                        for (i, (_, fty)) in fields.iter().enumerate() {
                            let name = format!("__fld_{ctor}_{i}");
                            // Datatype fields keep their datatype sort; a
                            // non-modeled `Ty::Adt` field is a universally
                            // quantified OPAQUE atom (by-name sort). Anything
                            // else fails the bundle closed.
                            let Some(sort) = payload_field_sort(fty) else {
                                return false;
                            };
                            arm_state.binders.push((name.clone(), sort.clone()));
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
                        if !mwalk(
                            members,
                            posts,
                            kind,
                            member_idx,
                            *target,
                            arm_state,
                            callees.clone(),
                            fuel,
                            fuel_field.clone(),
                            depth + 1,
                            ih_counter,
                            out,
                        ) {
                            return false;
                        }
                    }
                    true
                }
                // A third match layer is out of scope.
                (_, Some(_)) => false,
            }
        }
        Terminator::Call { func: callee, args, dest, target, .. } => {
            // Cluster-member calls only, inside a STEP payload arm, at the
            // one-step-smaller fuel. Anything else poisons the bundle.
            if fuel != FuelLayer::Step || state.ctor.is_none() {
                return false;
            }
            let Some(k_name) = fuel_field.clone() else {
                return false;
            };
            let Some(callee_idx) =
                members.iter().position(|m| &m.name == callee || &m.def_path == callee)
            else {
                return false;
            };
            let callee_fn = members[callee_idx];
            let Some(target) = target else {
                return false;
            };
            if args.len() != 2 || callee_fn.body.arg_count != 2 || !dest.projections.is_empty() {
                return false;
            }
            let Some(fuel_arg) = resolve_operand(func, &state, &args[0]) else {
                return false;
            };
            // FUEL-DECREASING gate: the callee's fuel must be exactly `k`.
            if fuel_arg.var_name() != Some(k_name.as_str()) {
                return false;
            }
            let Some(payload_arg) = resolve_operand(func, &state, &args[1]) else {
                return false;
            };
            match kind {
                WalkKind::Member => {
                    // Fresh IH result variable standing for the cluster
                    // call's output.
                    let ih_name = format!("__ih{ih_counter}");
                    *ih_counter += 1;
                    let ret_sort = crate::sort_for_ty(peel_indirection(&callee_fn.body.return_ty));
                    let ih_var = Formula::var_owned(ih_name.clone(), ret_sort.clone());
                    state.binders.push((ih_name, ret_sort));
                    state.store.insert(dest.local, ih_var.clone());
                    // IH atom: the CALLEE's postcondition assumed at the
                    // smaller fuel — `P_callee(k, payload_arg, __ih_j)`.
                    let mut map: HashMap<String, Formula> = HashMap::new();
                    map.insert(
                        crate::place_to_var_name(callee_fn, &Place::local(FUEL_LOCAL)),
                        fuel_arg,
                    );
                    map.insert(
                        crate::place_to_var_name(callee_fn, &Place::local(PAYLOAD_LOCAL)),
                        payload_arg,
                    );
                    map.insert("_0".to_string(), ih_var);
                    state.ih_atoms.push(crate::recursive_datatype_functional::subst_vars(
                        posts[callee_idx].clone(),
                        &map,
                    ));
                }
                WalkKind::Reference => {
                    // Definitional mode: the call IS the callee's application
                    // at the smaller fuel — `FnApp(callee, [k, arg])`, inline.
                    let ret_sort = crate::sort_for_ty(peel_indirection(&callee_fn.body.return_ty));
                    state.store.insert(
                        dest.local,
                        Formula::FnApp {
                            func: callee_fn.name.clone(),
                            args: vec![fuel_arg, payload_arg],
                            sort: ret_sort,
                        },
                    );
                }
            }
            callees.push(callee_fn.name.clone());
            mwalk(
                members,
                posts,
                kind,
                member_idx,
                *target,
                state,
                callees,
                fuel,
                fuel_field,
                depth + 1,
                ih_counter,
                out,
            )
        }
        _ => false,
    }
}

/// Universally close `body` over the arm binders (no-op when there are none).
fn close_over(binders: &[(String, Sort)], body: Formula) -> Formula {
    if binders.is_empty() {
        body
    } else {
        let refs: Vec<(&str, Sort)> =
            binders.iter().map(|(n, s)| (n.as_str(), s.clone())).collect();
        Formula::forall(&refs, body)
    }
}

#[cfg(test)]
mod tests {
    use trust_types::UnwindEdge;
    use trust_types::{
        AggregateKind, BasicBlock, LocalDecl, Operand, Rvalue, SourceSpan, Statement,
        VerifiableBody,
    };

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

    // ── The 2-member mutual fixture, in the extracted MIR shape ─────────────────
    //
    // `fm`/`gm : (&Fuel, &E) -> E` over `fuel::Fuel = Z | S(*const Fuel)` and
    // `expr::Expr = A | B(*const Expr)`:
    //   fm(Z, e)      = match e { A => A, B(x) => B(x) }      (identity rebuild)
    //   fm(S k, A)    = A
    //   fm(S k, B x)  = B (gm k x)                            (fm -> gm edge)
    //   gm            = symmetric, calling fm                 (gm -> fm edge)
    // {fm, gm} is a genuine 2-SCC; the TRUE postcondition of both is identity
    // (`_0 = e`), the template's model-vs-reference agreement collapsed to the
    // spec form the Formula language can state.

    fn fuel_ref() -> Ty {
        Ty::Datatype { name: "fuel::Fuel".to_string(), variants: Vec::new() }
    }

    fn fuel_dt() -> Ty {
        Ty::Datatype {
            name: "fuel::Fuel".to_string(),
            variants: vec![
                ("Z".to_string(), vec![]),
                ("S".to_string(), vec![("0".to_string(), fuel_ref())]),
            ],
        }
    }

    fn e_ref() -> Ty {
        Ty::Datatype { name: "expr::Expr".to_string(), variants: Vec::new() }
    }

    fn e_dt() -> Ty {
        Ty::Datatype {
            name: "expr::Expr".to_string(),
            variants: vec![
                ("A".to_string(), vec![]),
                ("B".to_string(), vec![("0".to_string(), e_ref())]),
            ],
        }
    }

    fn e_sort() -> Sort {
        crate::sort_for_ty(&e_dt())
    }

    fn local(index: usize, ty: Ty, name: Option<&str>) -> LocalDecl {
        LocalDecl { index, ty, name: name.map(str::to_string) }
    }

    fn assign(place: Place, rvalue: Rvalue) -> Statement {
        Statement::Assign { place, rvalue, span: SourceSpan::default() }
    }

    /// `m fuel e = e` — the true postcondition.
    fn identity_post() -> Formula {
        Formula::Eq(
            Box::new(Formula::var_owned("_0".to_string(), e_sort())),
            Box::new(Formula::var_owned("e".to_string(), e_sort())),
        )
    }

    /// `m fuel e = B e` — a FALSE postcondition (negative-control input).
    fn wrong_b_post() -> Formula {
        Formula::Eq(
            Box::new(Formula::var_owned("_0".to_string(), e_sort())),
            Box::new(Formula::Ctor {
                ctor: "B".to_string(),
                args: vec![Formula::var_owned("e".to_string(), e_sort())],
                sort: e_sort(),
            }),
        )
    }

    /// The extracted-shape MIR of one cluster member calling `callee`.
    fn cluster_member(name: &str, callee: &str, post: Formula) -> VerifiableFunction {
        let raw_fuel = Ty::RawPtr { mutable: false, pointee: Box::new(fuel_dt()) };
        let raw_e = Ty::RawPtr { mutable: false, pointee: Box::new(e_dt()) };
        let adt = |name: &str, variant: usize, ops: Vec<Operand>| {
            Rvalue::Aggregate(
                AggregateKind::Adt { name: name.to_string(), variant, active_field: None, args: None },
                ops,
            )
        };
        let body = VerifiableBody {
            locals: vec![
                local(0, e_dt(), None),
                local(1, Ty::Ref { mutable: false, inner: Box::new(fuel_dt()) }, Some("fuel")),
                local(2, Ty::Ref { mutable: false, inner: Box::new(e_dt()) }, Some("e")),
                local(3, Ty::Int { width: 64, signed: true }, None), // fuel discriminant
                local(4, Ty::Int { width: 64, signed: true }, None), // base e discriminant
                local(5, raw_fuel.clone(), None),                    // k payload read
                local(6, Ty::Int { width: 64, signed: true }, None), // step e discriminant
                local(7, raw_e.clone(), None),                       // base x payload read
                local(8, raw_e.clone(), None),                       // step x payload read
                local(9, Ty::Ref { mutable: false, inner: Box::new(fuel_dt()) }, None),
                local(10, Ty::Ref { mutable: false, inner: Box::new(e_dt()) }, None),
                local(11, e_dt(), Some("m")), // cluster-call dest
                local(12, raw_e, None),       // &raw m
            ],
            blocks: vec![
                // bb0: _3 = discriminant((*_1)); switch [(0 -> bb2 Z), (1 -> bb3 S)] else bb1
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![assign(
                        Place::local(3),
                        Rvalue::Discriminant(Place {
                            local: 1,
                            projections: vec![Projection::Deref],
                        }),
                    )],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Move(Place::local(3)),
                        targets: vec![(0, BlockId(2)), (1, BlockId(3))],
                        otherwise: BlockId(1),
                        exhaustive_enum_unreachable: true,
                        span: SourceSpan::default(),
                    },
                },
                // bb1: unreachable
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Unreachable },
                // bb2 (fuel Z): _4 = discriminant((*_2)); switch [(0 -> bb4 A), (1 -> bb5 B)]
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![assign(
                        Place::local(4),
                        Rvalue::Discriminant(Place {
                            local: 2,
                            projections: vec![Projection::Deref],
                        }),
                    )],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Move(Place::local(4)),
                        targets: vec![(0, BlockId(4)), (1, BlockId(5))],
                        otherwise: BlockId(1),
                        exhaustive_enum_unreachable: true,
                        span: SourceSpan::default(),
                    },
                },
                // bb3 (fuel S): _5 = ((*_1 as S).0);
                //               _6 = discriminant((*_2)); switch [(0 -> bb6 A), (1 -> bb7 B)]
                BasicBlock {
                    id: BlockId(3),
                    stmts: vec![
                        assign(
                            Place::local(5),
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
                            Place::local(6),
                            Rvalue::Discriminant(Place {
                                local: 2,
                                projections: vec![Projection::Deref],
                            }),
                        ),
                    ],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Move(Place::local(6)),
                        targets: vec![(0, BlockId(6)), (1, BlockId(7))],
                        otherwise: BlockId(1),
                        exhaustive_enum_unreachable: true,
                        span: SourceSpan::default(),
                    },
                },
                // bb4 (base A): _0 = Expr::A; goto bb9
                BasicBlock {
                    id: BlockId(4),
                    stmts: vec![assign(Place::local(0), adt("expr::Expr", 0, vec![]))],
                    terminator: Terminator::Goto(BlockId(9)),
                },
                // bb5 (base B): _7 = ((*_2 as B).0); _0 = Expr::B(copy _7); goto bb9
                BasicBlock {
                    id: BlockId(5),
                    stmts: vec![
                        assign(
                            Place::local(7),
                            Rvalue::Use(Operand::Copy(Place {
                                local: 2,
                                projections: vec![
                                    Projection::Deref,
                                    Projection::Downcast(1),
                                    Projection::Field(0),
                                ],
                            })),
                        ),
                        assign(
                            Place::local(0),
                            adt("expr::Expr", 1, vec![Operand::Copy(Place::local(7))]),
                        ),
                    ],
                    terminator: Terminator::Goto(BlockId(9)),
                },
                // bb6 (step A): _0 = Expr::A; goto bb9
                BasicBlock {
                    id: BlockId(6),
                    stmts: vec![assign(Place::local(0), adt("expr::Expr", 0, vec![]))],
                    terminator: Terminator::Goto(BlockId(9)),
                },
                // bb7 (step B): _8 = ((*_2 as B).0); _9 = &(*_5); _10 = &(*_8);
                //               callee(move _9, move _10) -> _11, bb8
                BasicBlock {
                    id: BlockId(7),
                    stmts: vec![
                        assign(
                            Place::local(8),
                            Rvalue::Use(Operand::Copy(Place {
                                local: 2,
                                projections: vec![
                                    Projection::Deref,
                                    Projection::Downcast(1),
                                    Projection::Field(0),
                                ],
                            })),
                        ),
                        assign(
                            Place::local(9),
                            Rvalue::Ref {
                                mutable: false,
                                place: Place { local: 5, projections: vec![Projection::Deref] },
                            },
                        ),
                        assign(
                            Place::local(10),
                            Rvalue::Ref {
                                mutable: false,
                                place: Place { local: 8, projections: vec![Projection::Deref] },
                            },
                        ),
                    ],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: callee.to_string(),
                        args: vec![Operand::Move(Place::local(9)), Operand::Move(Place::local(10))],
                        dest: Place::local(11),
                        target: Some(BlockId(8)),
                        span: SourceSpan::default(),
                        atomic: None,
                    },
                },
                // bb8: _12 = &raw const _11; _0 = Expr::B(copy _12); goto bb9
                BasicBlock {
                    id: BlockId(8),
                    stmts: vec![
                        assign(Place::local(12), Rvalue::AddressOf(false, Place::local(11))),
                        assign(
                            Place::local(0),
                            adt("expr::Expr", 1, vec![Operand::Copy(Place::local(12))]),
                        ),
                    ],
                    terminator: Terminator::Goto(BlockId(9)),
                },
                // bb9: return
                BasicBlock { id: BlockId(9), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 2,
            return_ty: e_dt(),
        };
        VerifiableFunction {
            name: name.to_string(),
            def_path: name.to_string(),
            span: SourceSpan::default(),
            body,
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![post],
            spec: Default::default(),
        }
    }

    fn identity_cluster() -> Vec<VerifiableFunction> {
        vec![
            cluster_member("fm", "gm", identity_post()),
            cluster_member("gm", "fm", identity_post()),
        ]
    }

    fn properties(vcs: &[VerificationCondition]) -> Vec<String> {
        vcs.iter()
            .map(|vc| match &vc.kind {
                VcKind::FunctionalCorrectness { property, .. } => property.clone(),
                other => panic!("expected FunctionalCorrectness, got {other:?}"),
            })
            .collect()
    }

    // ── Test 1: the mutual bundle shape ──────────────────────────────────────────

    #[test]
    fn test_mutual_cluster_emits_bundle() {
        let funcs = identity_cluster();
        let vcs = mutual_recursive_datatype_functional_vcs(&funcs);
        assert_eq!(
            properties(&vcs),
            vec![
                "mutual_recursive_datatype_functional_base::fm::A",
                "mutual_recursive_datatype_functional_base::fm::B",
                "mutual_recursive_datatype_functional_case::fm::A[calls=]",
                "mutual_recursive_datatype_functional_case::fm::B[calls=gm]",
                "mutual_recursive_datatype_functional_base::gm::A",
                "mutual_recursive_datatype_functional_base::gm::B",
                "mutual_recursive_datatype_functional_case::gm::A[calls=]",
                "mutual_recursive_datatype_functional_case::gm::B[calls=fm]",
                "mutual_recursive_datatype_functional_conclusion[mutual-induction:\
                 fuel=fuel::Fuel:Z|S;data=expr::Expr;members=fm,gm;bases=4;cases=4]",
            ],
            "bundle: {vcs:#?}"
        );

        // Base B arm: `Forall [__fld_B_0] Eq(B(f), B(f))` — identity rebuild.
        let Formula::Forall(binders, body) = &vcs[1].formula else {
            panic!("base B case must be a Forall, got {:?}", vcs[1].formula);
        };
        assert_eq!(binders.iter().map(|(s, _)| s.as_str()).collect::<Vec<_>>(), vec!["__fld_B_0"]);
        let Formula::Eq(lhs, rhs) = body.as_ref() else {
            panic!("base B body must be Eq, got {body:?}");
        };
        let (Formula::Ctor { ctor: lc, args: la, .. }, Formula::Ctor { ctor: rc, args: ra, .. }) =
            (lhs.as_ref(), rhs.as_ref())
        else {
            panic!("base B sides must be Ctor, got {lhs:?} / {rhs:?}");
        };
        assert_eq!((lc.as_str(), rc.as_str()), ("B", "B"));
        assert_eq!(la[0].var_name(), Some("__fld_B_0"));
        assert_eq!(ra[0].var_name(), Some("__fld_B_0"));

        // Step B arm of fm: the CROSS-MEMBER IH — the callee gm's postcondition
        // assumed at the smaller fuel:
        // `Forall [__fld_S_0, __fld_B_0, __ih0]
        //    (Implies (Eq(__ih0, __fld_B_0)) (Eq(B(__ih0), B(__fld_B_0))))`.
        let Formula::Forall(binders, body) = &vcs[3].formula else {
            panic!("step B case must be a Forall, got {:?}", vcs[3].formula);
        };
        assert_eq!(
            binders.iter().map(|(s, _)| s.as_str()).collect::<Vec<_>>(),
            vec!["__fld_S_0", "__fld_B_0", "__ih0"],
            "fuel binder, then pattern field, then IH result"
        );
        let Formula::Implies(ih, concl) = body.as_ref() else {
            panic!("step B body must be IH => conclusion, got {body:?}");
        };
        let Formula::Eq(ih_l, ih_r) = ih.as_ref() else {
            panic!("IH atom must be Eq, got {ih:?}");
        };
        assert_eq!(ih_l.var_name(), Some("__ih0"));
        assert_eq!(ih_r.var_name(), Some("__fld_B_0"));
        let Formula::Eq(c_l, c_r) = concl.as_ref() else {
            panic!("conclusion must be Eq, got {concl:?}");
        };
        let (Formula::Ctor { args: cla, .. }, Formula::Ctor { args: cra, .. }) =
            (c_l.as_ref(), c_r.as_ref())
        else {
            panic!("conclusion sides must be Ctor, got {c_l:?} / {c_r:?}");
        };
        assert_eq!(cla[0].var_name(), Some("__ih0"));
        assert_eq!(cra[0].var_name(), Some("__fld_B_0"));

        // Joint conclusion: `And [Forall [fuel, e] Eq(_0, e); x2]`.
        let Formula::And(conjuncts) = &vcs[8].formula else {
            panic!("conclusion must be an And, got {:?}", vcs[8].formula);
        };
        assert_eq!(conjuncts.len(), 2);
        for conj in conjuncts {
            let Formula::Forall(binders, body) = conj else {
                panic!("conjunct must be Forall, got {conj:?}");
            };
            assert_eq!(
                binders.iter().map(|(s, _)| s.as_str()).collect::<Vec<_>>(),
                vec!["fuel", "e"]
            );
            let Formula::Eq(l0, le) = body.as_ref() else {
                panic!("conjunct body must be Eq, got {body:?}");
            };
            assert_eq!(l0.var_name(), Some("_0"), "the output slot stays free");
            assert_eq!(le.var_name(), Some("e"));
        }
    }

    // ── Test 2: emission is spec-driven ─────────────────────────────────────────

    #[test]
    fn test_wrong_post_on_one_member_emits_its_bundle() {
        let funcs = vec![
            cluster_member("fm", "gm", identity_post()),
            cluster_member("gm", "fm", wrong_b_post()),
        ];
        let vcs = mutual_recursive_datatype_functional_vcs(&funcs);
        assert_eq!(vcs.len(), 9, "emission is spec-driven; truth is the discharger's job");
        // gm's base A case is now the FALSE `Eq(A, B(A))`.
        let Formula::Eq(lhs, rhs) = &vcs[4].formula else {
            panic!("gm base A must be a bare Eq, got {:?}", vcs[4].formula);
        };
        let Formula::Ctor { ctor: lc, .. } = lhs.as_ref() else { panic!() };
        let Formula::Ctor { ctor: rc, args, .. } = rhs.as_ref() else { panic!() };
        assert_eq!((lc.as_str(), rc.as_str()), ("A", "B"));
        let Formula::Ctor { ctor: inner, .. } = &args[0] else {
            panic!("wrong-post gm base A rhs must be B(A), got {args:?}");
        };
        assert_eq!(inner, "A");
        // fm's step B IH atom is now gm's WRONG postcondition at the call:
        // `Eq(__ih0, B(__fld_B_0))` — the atom is the CALLEE's spec.
        let Formula::Forall(_, body) = &vcs[3].formula else { panic!() };
        let Formula::Implies(ih, _) = body.as_ref() else { panic!() };
        let Formula::Eq(_, ih_r) = ih.as_ref() else { panic!() };
        let Formula::Ctor { ctor, .. } = ih_r.as_ref() else {
            panic!("fm's IH atom must carry gm's wrong post, got {ih_r:?}");
        };
        assert_eq!(ctor, "B");
    }

    // ── Test 3: gates fail closed ────────────────────────────────────────────────

    #[test]
    fn test_self_recursive_scc_of_one_emits_nothing() {
        // fm calls itself: an SCC of size 1 — the sibling lane's job.
        let funcs = vec![cluster_member("fm", "fm", identity_post())];
        assert!(
            mutual_recursive_datatype_functional_vcs(&funcs).is_empty(),
            "SCC-of-1 belongs to recursive_datatype_functional, not the mutual lane"
        );
    }

    #[test]
    fn test_missing_postcondition_fails_closed() {
        let mut funcs = identity_cluster();
        funcs[1].postconditions.clear();
        assert!(mutual_recursive_datatype_functional_vcs(&funcs).is_empty());
    }

    #[test]
    fn test_u8_wraparound_postcondition_emits_visible_unsupported_row() {
        let mut funcs = identity_cluster();
        funcs[0].postconditions = vec![u8_wraparound_post()];
        let vcs = mutual_recursive_datatype_functional_vcs(&funcs);
        assert_eq!(vcs.len(), 1, "the arithmetic gap must be one visible report row");
        assert!(matches!(
            &vcs[0].kind,
            VcKind::UnsupportedMir { kind, detail }
                if kind == crate::contracts::SPEC_UNVERIFIABLE_KIND
                    && detail.contains("mutual recursive-datatype functional induction")
                    && detail.contains("unsupported_machine_arithmetic")
        ));
        assert_eq!(vcs[0].formula, Formula::Bool(true), "the gap must not be solver-provable");
    }

    #[test]
    fn test_u8_wraparound_postcondition_outside_lane_shape_emits_nothing() {
        let mut funcs = identity_cluster();
        funcs[0].postconditions = vec![u8_wraparound_post()];
        funcs[0].body.arg_count = 1;
        assert!(
            mutual_recursive_datatype_functional_vcs(&funcs).is_empty(),
            "arithmetic must not make an out-of-shape SCC appear owned by this lane"
        );
    }

    #[test]
    fn test_call_outside_cluster_fails_closed() {
        let funcs = vec![
            cluster_member("fm", "gm", identity_post()),
            cluster_member("gm", "other", identity_post()),
        ];
        // gm -> other breaks the SCC: {fm, gm} is no longer strongly connected.
        assert!(mutual_recursive_datatype_functional_vcs(&funcs).is_empty());
    }

    #[test]
    fn test_non_decreasing_fuel_call_fails_closed() {
        // Rewire fm's cluster call to pass the WHOLE fuel parameter instead of
        // the one-step-smaller `k`: the induction tag would be a lie.
        let mut funcs = identity_cluster();
        for block in &mut funcs[0].body.blocks {
            if block.id == BlockId(7) {
                block.stmts[1] = assign(
                    Place::local(9),
                    Rvalue::Ref {
                        mutable: false,
                        place: Place { local: 1, projections: vec![Projection::Deref] },
                    },
                );
            }
        }
        assert!(
            mutual_recursive_datatype_functional_vcs(&funcs).is_empty(),
            "a cluster call that does not decrease fuel must not emit a mutual bundle"
        );
    }

    #[test]
    fn test_missing_payload_arm_fails_closed() {
        let mut funcs = identity_cluster();
        // Drop the A target from gm's STEP payload switch.
        for block in &mut funcs[1].body.blocks {
            if block.id == BlockId(3) {
                if let Terminator::SwitchInt { targets, .. } = &mut block.terminator {
                    targets.retain(|(tag, _)| *tag != 0);
                }
            }
        }
        assert!(
            mutual_recursive_datatype_functional_vcs(&funcs).is_empty(),
            "a bundle that does not cover every payload constructor must not be emitted"
        );
    }

    #[test]
    fn test_call_in_base_arm_fails_closed() {
        // Redirect the fuel-Z target to the STEP payload switch block, so the
        // base arm contains a cluster call (no smaller fuel exists at Z).
        let mut funcs = identity_cluster();
        for block in &mut funcs[0].body.blocks {
            if block.id == BlockId(0) {
                if let Terminator::SwitchInt { targets, .. } = &mut block.terminator {
                    for (tag, target) in targets.iter_mut() {
                        if *tag == 0 {
                            *target = BlockId(3);
                        }
                    }
                }
            }
        }
        assert!(
            mutual_recursive_datatype_functional_vcs(&funcs).is_empty(),
            "a base (fuel = 0) arm with a cluster call must not emit a mutual bundle"
        );
    }
}

#[cfg(test)]
mod literal_cluster_tests {
    //! The three LITERAL-CLUSTER items at the emission level, over the
    //! 3-constructor slice `t::T = A | M(*const T, *const T) | P(Name)`:
    //! multi-IH constructors (M — two cluster calls per step arm), opaque
    //! payload fields (P's `name::Name` field), and function-vs-function
    //! postconditions (`_0 = FnApp(ref, [fuel, e])` with reference
    //! definitional VCs).

    use trust_types::UnwindEdge;
    use trust_types::{
        AggregateKind, BasicBlock, LocalDecl, Operand, Rvalue, SourceSpan, Statement,
        VerifiableBody,
    };

    use super::*;

    fn fuel_ref() -> Ty {
        Ty::Datatype { name: "fuel::Fuel".to_string(), variants: Vec::new() }
    }

    fn fuel_dt() -> Ty {
        Ty::Datatype {
            name: "fuel::Fuel".to_string(),
            variants: vec![
                ("Z".to_string(), vec![]),
                ("S".to_string(), vec![("0".to_string(), fuel_ref())]),
            ],
        }
    }

    fn t_ref() -> Ty {
        Ty::Datatype { name: "t::T".to_string(), variants: Vec::new() }
    }

    fn name_adt() -> Ty {
        Ty::adt("name::Name", vec![])
    }

    /// The payload datatype, with a configurable P-field type (the opaque
    /// gate's negative control swaps in a non-Adt scalar).
    fn t_dt_with(p_field: Ty) -> Ty {
        Ty::Datatype {
            name: "t::T".to_string(),
            variants: vec![
                ("A".to_string(), vec![]),
                ("M".to_string(), vec![("0".to_string(), t_ref()), ("1".to_string(), t_ref())]),
                ("P".to_string(), vec![("0".to_string(), p_field)]),
            ],
        }
    }

    fn t_dt() -> Ty {
        t_dt_with(name_adt())
    }

    fn t_sort() -> Sort {
        crate::sort_for_ty(&t_dt())
    }

    fn fuel_sort() -> Sort {
        crate::sort_for_ty(&fuel_dt())
    }

    fn local(index: usize, ty: Ty, name: Option<&str>) -> LocalDecl {
        LocalDecl { index, ty, name: name.map(str::to_string) }
    }

    fn assign(place: Place, rvalue: Rvalue) -> Statement {
        Statement::Assign { place, rvalue, span: SourceSpan::default() }
    }

    /// `m fuel e = e` — the identity postcondition.
    fn identity_post() -> Formula {
        Formula::Eq(
            Box::new(Formula::var_owned("_0".to_string(), t_sort())),
            Box::new(Formula::var_owned("e".to_string(), t_sort())),
        )
    }

    /// `m fuel e = FnApp(r, [fuel, e])` — the model=reference postcondition.
    fn ref_post(r: &str) -> Formula {
        Formula::Eq(
            Box::new(Formula::var_owned("_0".to_string(), t_sort())),
            Box::new(Formula::FnApp {
                func: r.to_string(),
                args: vec![
                    Formula::var_owned("fuel".to_string(), fuel_sort()),
                    Formula::var_owned("e".to_string(), t_sort()),
                ],
                sort: t_sort(),
            }),
        )
    }

    /// One fuel-indexed function over `t::T` in the extracted MIR shape.
    /// `direct_base`: the fuel-Z arm returns `e` directly (the reference
    /// style) instead of the per-constructor rebuild. The step-M arm makes
    /// TWO calls to `callee` (fields 0 and 1, at fuel k).
    #[allow(clippy::too_many_lines)]
    fn cluster_fn(
        name: &str,
        callee: &str,
        post: Vec<Formula>,
        direct_base: bool,
        p_field: Ty,
    ) -> VerifiableFunction {
        let t_full = t_dt_with(p_field.clone());
        let raw_fuel = Ty::RawPtr { mutable: false, pointee: Box::new(fuel_dt()) };
        let raw_t = Ty::RawPtr { mutable: false, pointee: Box::new(t_full.clone()) };
        let adt = |variant: usize, ops: Vec<Operand>| {
            Rvalue::Aggregate(
                AggregateKind::Adt { name: "t::T".to_string(), variant, active_field: None, args: None },
                ops,
            )
        };
        let disc = |dst: usize, of: usize| {
            assign(
                Place::local(dst),
                Rvalue::Discriminant(Place { local: of, projections: vec![Projection::Deref] }),
            )
        };
        let read_field = |dst: usize, of: usize, variant: usize, field: usize| {
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
        let reborrow = |dst: usize, of: usize| {
            assign(
                Place::local(dst),
                Rvalue::Ref {
                    mutable: false,
                    place: Place { local: of, projections: vec![Projection::Deref] },
                },
            )
        };
        let call = |a: usize, b: usize, dst: usize, next: usize| Terminator::Call {
            unwind: UnwindEdge::Unreachable,
            is_unsafe_sig: false,
            is_foreign: false,
            func: callee.to_string(),
            args: vec![Operand::Move(Place::local(a)), Operand::Move(Place::local(b))],
            dest: Place::local(dst),
            target: Some(BlockId(next)),
            span: SourceSpan::default(),
            atomic: None,
        };
        let switch = |d: usize, targets: Vec<(u128, BlockId)>| Terminator::SwitchInt {
            discr: Operand::Move(Place::local(d)),
            targets,
            otherwise: BlockId(1),
            exhaustive_enum_unreachable: true,
            span: SourceSpan::default(),
        };
        // Base (fuel = Z) arm: either the per-ctor rebuild (bb2 switches to
        // bb4/bb5/bb6) or the direct return of `e`.
        let base_block = if direct_base {
            BasicBlock {
                id: BlockId(2),
                stmts: vec![assign(
                    Place::local(0),
                    Rvalue::Use(Operand::Copy(Place {
                        local: 2,
                        projections: vec![Projection::Deref],
                    })),
                )],
                terminator: Terminator::Goto(BlockId(13)),
            }
        } else {
            BasicBlock {
                id: BlockId(2),
                stmts: vec![disc(4, 2)],
                terminator: switch(4, vec![(0, BlockId(4)), (1, BlockId(5)), (2, BlockId(6))]),
            }
        };
        let body = VerifiableBody {
            locals: vec![
                local(0, t_full.clone(), None),
                local(1, Ty::Ref { mutable: false, inner: Box::new(fuel_dt()) }, Some("fuel")),
                local(2, Ty::Ref { mutable: false, inner: Box::new(t_full) }, Some("e")),
                local(3, Ty::Int { width: 64, signed: true }, None), // fuel disc
                local(4, Ty::Int { width: 64, signed: true }, None), // base payload disc
                local(5, raw_fuel, None),                            // k read
                local(6, Ty::Int { width: 64, signed: true }, None), // step payload disc
                local(7, raw_t.clone(), None),                       // base M.0
                local(8, raw_t.clone(), None),                       // base M.1
                local(9, p_field.clone(), None),                     // base P.0
                local(10, raw_t.clone(), None),                      // step M.0
                local(11, raw_t.clone(), None),                      // step M.1
                local(12, Ty::Ref { mutable: false, inner: Box::new(fuel_dt()) }, None),
                local(13, Ty::Ref { mutable: false, inner: Box::new(t_dt()) }, None),
                local(14, t_dt(), Some("m1")), // first call dest
                local(15, Ty::Ref { mutable: false, inner: Box::new(fuel_dt()) }, None),
                local(16, Ty::Ref { mutable: false, inner: Box::new(t_dt()) }, None),
                local(17, t_dt(), Some("m2")), // second call dest
                local(18, raw_t.clone(), None),
                local(19, raw_t, None),
                local(20, p_field, None), // step P.0
            ],
            blocks: vec![
                // bb0: fuel switch.
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![disc(3, 1)],
                    terminator: switch(3, vec![(0, BlockId(2)), (1, BlockId(3))]),
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Unreachable },
                // bb2: base arm (per-ctor or direct — see above).
                base_block,
                // bb3 (fuel S): read k; step payload switch.
                BasicBlock {
                    id: BlockId(3),
                    stmts: vec![read_field(5, 1, 1, 0), disc(6, 2)],
                    terminator: switch(6, vec![(0, BlockId(7)), (1, BlockId(8)), (2, BlockId(9))]),
                },
                // bb4 (base A): _0 = A.
                BasicBlock {
                    id: BlockId(4),
                    stmts: vec![assign(Place::local(0), adt(0, vec![]))],
                    terminator: Terminator::Goto(BlockId(13)),
                },
                // bb5 (base M): rebuild M from both fields.
                BasicBlock {
                    id: BlockId(5),
                    stmts: vec![
                        read_field(7, 2, 1, 0),
                        read_field(8, 2, 1, 1),
                        assign(
                            Place::local(0),
                            adt(
                                1,
                                vec![
                                    Operand::Copy(Place::local(7)),
                                    Operand::Copy(Place::local(8)),
                                ],
                            ),
                        ),
                    ],
                    terminator: Terminator::Goto(BlockId(13)),
                },
                // bb6 (base P): rebuild P from the opaque field.
                BasicBlock {
                    id: BlockId(6),
                    stmts: vec![
                        read_field(9, 2, 2, 0),
                        assign(Place::local(0), adt(2, vec![Operand::Copy(Place::local(9))])),
                    ],
                    terminator: Terminator::Goto(BlockId(13)),
                },
                // bb7 (step A): _0 = A.
                BasicBlock {
                    id: BlockId(7),
                    stmts: vec![assign(Place::local(0), adt(0, vec![]))],
                    terminator: Terminator::Goto(BlockId(13)),
                },
                // bb8 (step M): first call — callee(k, M.0).
                BasicBlock {
                    id: BlockId(8),
                    stmts: vec![
                        read_field(10, 2, 1, 0),
                        read_field(11, 2, 1, 1),
                        reborrow(12, 5),
                        reborrow(13, 10),
                    ],
                    terminator: call(12, 13, 14, 10),
                },
                // bb9 (step P): rebuild P from the opaque field.
                BasicBlock {
                    id: BlockId(9),
                    stmts: vec![
                        read_field(20, 2, 2, 0),
                        assign(Place::local(0), adt(2, vec![Operand::Copy(Place::local(20))])),
                    ],
                    terminator: Terminator::Goto(BlockId(13)),
                },
                // bb10: second call — callee(k, M.1).
                BasicBlock {
                    id: BlockId(10),
                    stmts: vec![reborrow(15, 5), reborrow(16, 11)],
                    terminator: call(15, 16, 17, 11),
                },
                // bb11: _0 = M(&raw m1, &raw m2).
                BasicBlock {
                    id: BlockId(11),
                    stmts: vec![
                        assign(Place::local(18), Rvalue::AddressOf(false, Place::local(14))),
                        assign(Place::local(19), Rvalue::AddressOf(false, Place::local(17))),
                        assign(
                            Place::local(0),
                            adt(
                                1,
                                vec![
                                    Operand::Copy(Place::local(18)),
                                    Operand::Copy(Place::local(19)),
                                ],
                            ),
                        ),
                    ],
                    terminator: Terminator::Goto(BlockId(13)),
                },
                // bb12: (unused spare, keeps ids stable)
                BasicBlock { id: BlockId(12), stmts: vec![], terminator: Terminator::Unreachable },
                // bb13: return.
                BasicBlock { id: BlockId(13), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 2,
            return_ty: t_dt(),
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

    fn properties(vcs: &[VerificationCondition]) -> Vec<String> {
        vcs.iter()
            .map(|vc| match &vc.kind {
                VcKind::FunctionalCorrectness { property, .. } => property.clone(),
                other => panic!("expected FunctionalCorrectness, got {other:?}"),
            })
            .collect()
    }

    // ── Item 1 + 2: multi-IH arms and opaque payload fields ─────────────────────

    #[test]
    fn test_multi_ih_opaque_cluster_emits_bundle() {
        let funcs = vec![
            cluster_fn("fm", "gm", vec![identity_post()], false, name_adt()),
            cluster_fn("gm", "fm", vec![identity_post()], false, name_adt()),
        ];
        let vcs = mutual_recursive_datatype_functional_vcs(&funcs);
        assert_eq!(
            properties(&vcs),
            vec![
                "mutual_recursive_datatype_functional_base::fm::A",
                "mutual_recursive_datatype_functional_base::fm::M",
                "mutual_recursive_datatype_functional_base::fm::P",
                "mutual_recursive_datatype_functional_case::fm::A[calls=]",
                "mutual_recursive_datatype_functional_case::fm::M[calls=gm,gm]",
                "mutual_recursive_datatype_functional_case::fm::P[calls=]",
                "mutual_recursive_datatype_functional_base::gm::A",
                "mutual_recursive_datatype_functional_base::gm::M",
                "mutual_recursive_datatype_functional_base::gm::P",
                "mutual_recursive_datatype_functional_case::gm::A[calls=]",
                "mutual_recursive_datatype_functional_case::gm::M[calls=fm,fm]",
                "mutual_recursive_datatype_functional_case::gm::P[calls=]",
                "mutual_recursive_datatype_functional_conclusion[mutual-induction:\
                 fuel=fuel::Fuel:Z|S;data=t::T;members=fm,gm;bases=6;cases=6]",
            ],
            "bundle: {vcs:#?}"
        );

        // The step-M arm: TWO IH atoms (one per cluster call), in call order.
        let Formula::Forall(binders, body) = &vcs[4].formula else {
            panic!("step M case must be a Forall, got {:?}", vcs[4].formula);
        };
        assert_eq!(
            binders.iter().map(|(s, _)| s.as_str()).collect::<Vec<_>>(),
            vec!["__fld_S_0", "__fld_M_0", "__fld_M_1", "__ih0", "__ih1"],
            "fuel binder, both pattern fields, then BOTH IH results"
        );
        let Formula::Implies(ih, concl) = body.as_ref() else {
            panic!("step M body must be IHs => conclusion, got {body:?}");
        };
        let Formula::And(atoms) = ih.as_ref() else {
            panic!("two-call arm must carry an And of two IH atoms, got {ih:?}");
        };
        assert_eq!(atoms.len(), 2);
        let Formula::Eq(l0, r0) = &atoms[0] else { panic!("atom 0 must be Eq") };
        assert_eq!((l0.var_name(), r0.var_name()), (Some("__ih0"), Some("__fld_M_0")));
        let Formula::Eq(l1, r1) = &atoms[1] else { panic!("atom 1 must be Eq") };
        assert_eq!((l1.var_name(), r1.var_name()), (Some("__ih1"), Some("__fld_M_1")));
        let Formula::Eq(c_l, _) = concl.as_ref() else { panic!("conclusion must be Eq") };
        let Formula::Ctor { ctor, args, .. } = c_l.as_ref() else {
            panic!("conclusion lhs must be the rebuilt M, got {c_l:?}");
        };
        assert_eq!(ctor, "M");
        assert_eq!(args[0].var_name(), Some("__ih0"));
        assert_eq!(args[1].var_name(), Some("__ih1"));

        // The base-P arm binds the OPAQUE field with its by-name Adt sort.
        let Formula::Forall(binders, _) = &vcs[2].formula else {
            panic!("base P case must be a Forall, got {:?}", vcs[2].formula);
        };
        let [(name, sort)] = binders.as_slice() else {
            panic!("base P case must bind exactly the opaque field");
        };
        assert_eq!(name.as_str(), "__fld_P_0");
        assert_eq!(
            sort,
            &Sort::Datatype { name: "name::Name".to_string(), constructors: vec![] },
            "the opaque field's binder sort is the by-name uninterpreted datatype"
        );
    }

    /// A payload constructor field of a NON-Adt, non-datatype type (a raw
    /// scalar) is out of scope: the bundle fails closed.
    #[test]
    fn test_non_adt_opaque_field_fails_closed() {
        let scalar = Ty::Int { width: 64, signed: false };
        let funcs = vec![
            cluster_fn("fm", "gm", vec![identity_post()], false, scalar.clone()),
            cluster_fn("gm", "fm", vec![identity_post()], false, scalar),
        ];
        assert!(
            mutual_recursive_datatype_functional_vcs(&funcs).is_empty(),
            "a scalar payload field must not emit a mutual bundle"
        );
    }

    // ── Item 3: function-vs-function postconditions ─────────────────────────────

    fn model_vs_reference_funcs() -> Vec<VerifiableFunction> {
        vec![
            cluster_fn("fm", "gm", vec![ref_post("fr")], false, name_adt()),
            cluster_fn("gm", "fm", vec![ref_post("gr")], false, name_adt()),
            // References: DIRECT base return, no postconditions of their own.
            cluster_fn("fr", "gr", vec![], true, name_adt()),
            cluster_fn("gr", "fr", vec![], true, name_adt()),
        ]
    }

    #[test]
    fn test_ref_mode_emits_definitional_bundle() {
        // Give the reference functions a postcondition-free ride: members
        // still need posts (the gate), refs must not.
        let mut funcs = model_vs_reference_funcs();
        // The SCC machinery only clusters {fm, gm}; {fr, gr} has no posts and
        // emits nothing of its own.
        let vcs = mutual_recursive_datatype_functional_vcs(&funcs);
        assert_eq!(
            properties(&vcs),
            vec![
                "mutual_recursive_datatype_functional_base::fm::A",
                "mutual_recursive_datatype_functional_base::fm::M",
                "mutual_recursive_datatype_functional_base::fm::P",
                "mutual_recursive_datatype_functional_case::fm::A[calls=]",
                "mutual_recursive_datatype_functional_case::fm::M[calls=gm,gm]",
                "mutual_recursive_datatype_functional_case::fm::P[calls=]",
                "mutual_recursive_datatype_functional_base::gm::A",
                "mutual_recursive_datatype_functional_base::gm::M",
                "mutual_recursive_datatype_functional_base::gm::P",
                "mutual_recursive_datatype_functional_case::gm::A[calls=]",
                "mutual_recursive_datatype_functional_case::gm::M[calls=fm,fm]",
                "mutual_recursive_datatype_functional_case::gm::P[calls=]",
                "mutual_recursive_datatype_functional_refbase::fr",
                "mutual_recursive_datatype_functional_refstep::fr::A[calls=]",
                "mutual_recursive_datatype_functional_refstep::fr::M[calls=gr,gr]",
                "mutual_recursive_datatype_functional_refstep::fr::P[calls=]",
                "mutual_recursive_datatype_functional_refbase::gr",
                "mutual_recursive_datatype_functional_refstep::gr::A[calls=]",
                "mutual_recursive_datatype_functional_refstep::gr::M[calls=fr,fr]",
                "mutual_recursive_datatype_functional_refstep::gr::P[calls=]",
                "mutual_recursive_datatype_functional_conclusion[mutual-induction:\
                 fuel=fuel::Fuel:Z|S;data=t::T;members=fm,gm;bases=6;cases=6;\
                 refs=fr,gr;refbases=2;refcases=6]",
            ],
            "bundle: {vcs:#?}"
        );

        // The reference DIRECT base is the definitional transport equation
        // `Forall [e] Eq(FnApp(fr, [Z, e]), e)`.
        let Formula::Forall(binders, body) = &vcs[12].formula else {
            panic!("refbase fr must be a Forall, got {:?}", vcs[12].formula);
        };
        assert_eq!(binders.iter().map(|(s, _)| s.as_str()).collect::<Vec<_>>(), vec!["e"]);
        let Formula::Eq(lhs, rhs) = body.as_ref() else {
            panic!("refbase body must be Eq, got {body:?}");
        };
        let Formula::FnApp { func, args, .. } = lhs.as_ref() else {
            panic!("refbase lhs must be the definitional FnApp, got {lhs:?}");
        };
        assert_eq!(func, "fr");
        let Formula::Ctor { ctor, .. } = &args[0] else { panic!("fuel must be the Z ctor") };
        assert_eq!(ctor, "Z");
        assert_eq!(args[1].var_name(), Some("e"));
        assert_eq!(rhs.var_name(), Some("e"), "direct return transports the variable");

        // The member step-M IH atoms carry the CALLEE's REFERENCE at fuel k.
        let Formula::Forall(_, body) = &vcs[4].formula else { panic!() };
        let Formula::Implies(ih, _) = body.as_ref() else { panic!() };
        let Formula::And(atoms) = ih.as_ref() else { panic!() };
        let Formula::Eq(_, atom_rhs) = &atoms[0] else { panic!() };
        let Formula::FnApp { func, args, .. } = atom_rhs.as_ref() else {
            panic!("the IH atom must be the callee's reference application, got {atom_rhs:?}");
        };
        assert_eq!(func, "gr", "fm's callee gm has reference gr");
        assert_eq!(args[0].var_name(), Some("__fld_S_0"), "at the one-step-smaller fuel");
        assert_eq!(args[1].var_name(), Some("__fld_M_0"));

        // The refs themselves emitted nothing extra (no posts, no own bundle).
        funcs.truncate(2);
        assert!(
            mutual_recursive_datatype_functional_vcs(&funcs).is_empty(),
            "without the reference functions in scope the ref-mode bundle must fail closed"
        );
    }

    #[test]
    fn test_mixed_post_modes_fail_closed() {
        let funcs = vec![
            cluster_fn("fm", "gm", vec![ref_post("fr")], false, name_adt()),
            cluster_fn("gm", "fm", vec![identity_post()], false, name_adt()),
            cluster_fn("fr", "gr", vec![], true, name_adt()),
            cluster_fn("gr", "fr", vec![], true, name_adt()),
        ];
        assert!(
            mutual_recursive_datatype_functional_vcs(&funcs).is_empty(),
            "mixed constructor-tree / reference postconditions must fail closed"
        );
    }

    #[test]
    fn test_reference_naming_a_member_fails_closed() {
        // fm's "reference" is the other MEMBER gm: the reference set must be
        // disjoint from the cluster.
        let funcs = vec![
            cluster_fn("fm", "gm", vec![ref_post("gm")], false, name_adt()),
            cluster_fn("gm", "fm", vec![ref_post("gm")], false, name_adt()),
        ];
        assert!(
            mutual_recursive_datatype_functional_vcs(&funcs).is_empty(),
            "a member cannot serve as a reference"
        );
    }

    #[test]
    fn test_reference_with_non_decreasing_fuel_fails_closed() {
        // Rewire fr's first M call to pass the WHOLE fuel instead of k: the
        // transported definition would not be fuel-founded.
        let mut funcs = model_vs_reference_funcs();
        for block in &mut funcs[2].body.blocks {
            if block.id == BlockId(8) {
                block.stmts[2] = assign(
                    Place::local(12),
                    Rvalue::Ref {
                        mutable: false,
                        place: Place { local: 1, projections: vec![Projection::Deref] },
                    },
                );
            }
        }
        assert!(
            mutual_recursive_datatype_functional_vcs(&funcs).is_empty(),
            "a reference call that does not decrease fuel must fail the whole bundle closed"
        );
    }
}
