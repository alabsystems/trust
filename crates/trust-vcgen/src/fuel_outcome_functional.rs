// trust-vcgen/fuel_outcome_functional.rs: SN-vs-fuel RESOLUTION items 2+3 —
// fail-closed EXHAUSTION arms with Done-conditional postconditions, and the
// loop -> fuel-model per-iteration SIMULATION VCs.
//
// The real kernel cluster's budget mechanism is fail-closed at exhaustion:
// whnf returns the input unreduced, is_def_eq returns false, infer returns
// Err. The whnf shape is a reflexive 0-step acceptance (its exhaustion
// identity SATISFIES the reduction postcondition — modeled by the threaded
// lane's pinned `Mk(Z, e)` exhaustion, item 1). The false/Err shapes yield NO
// result, so their functional postconditions become DONE-CONDITIONAL:
//
//   model fuel x = Done r  ->  P(r)
//
// with `Done | Exhausted` a modeled OUTCOME datatype (`Exhausted` nullary for
// the false/Err markers, or unary carrying the PARTIAL value — the
// whnf_outer_loop bail). THIS lane (item 2) emits the fuel-induction bundle
// for a SELF-recursive outcome-returning fuel model, and its trust-certify
// twin discharges it, machine-builds the FUEL-MONOTONICITY lane lemma
// (Done at f -> the same Done at every f' >= f), and kernel-witnesses the
// negative control (a postcondition that holds only on the Exhausted arm must
// NOT certify unconditionally).
//
// SHAPE DETECTED (fail-closed outside it): a SELF-recursive (call-graph SCC
// of size 1) function of the extracted TAIL form
//
//   fn m(fuel: &Fuel, e: &E) -> O {         // O = Done(E) | Exh[(E)]
//       match fuel {
//           Fuel::Z    => O::Exh[(e)]       // fail-closed exhaustion arm
//           Fuel::S(k) => match e {
//               C(..) => O::Done(<tree over fields>)   // COMPLETE arm
//               D(x)  => m(k, x)                       // TAIL (continue) arm
//           }
//       }
//   }
//
// The TAIL form is exactly the whnf_outer_loop model shape (item 3): the loop
// with an in-program counter decrement and an exhausted-bail returning the
// partial converts to this fuel-indexed tail recursion. `loop_fuel_sim_vcs`
// is the item-3 DETECTOR: it recognizes the LOOP MIR (loop head switching on
// a counter local, in-program decrement `b = k`, exhausted-bail, per-ctor
// done/continue arms with the back edge) and emits the PER-ITERATION
// SIMULATION VCs — one defining equation of the fuel model per loop path:
//
//   bail:      Forall [c]         model(Z, c)        = Exh[(c)]
//   done C:    Forall [k, fields] model(S k, C(..))  = Done(tree)
//   continue D:Forall [k, fields] model(S k, D(x))   = model(k, x)
//
// tagged `loop_fuel_sim_*::<loop>` plus a `[loop-fuel-sim:..]` conclusion
// binding loop name, model name, and the path census. trust-certify
// discharges them definitionally against the SAME rebuilt model that carries
// the induction bundle — the extraction-serialization-style honest handoff
// (the loop-body emission path inside trust-mir-extract is the named
// follow-up; this lane PROVES the discharge shape on the hand-modeled pair).
//
// EMITTED INDUCTION BUNDLE (per function):
//   * `fuel_outcome_functional_base::<m>`
//       `Forall [e] post[fuel := Z, _0 := Exh[(e)]]`   (the exhaustion arm —
//     under a Done-conditional post this leg is VACUOUSLY true, which the
//     discharge must witness through the kernel, not assume);
//   * `fuel_outcome_functional_case::<m>::<C>[calls=]` (complete arms)
//       `Forall [k, fields] post[fuel := S k, e := pattern, _0 := Done(tree)]`
//   * `fuel_outcome_functional_case::<m>::<C>[calls=<m>]` (tail arms)
//       `Forall [k, fields, __ih0] (Implies post[fuel := k, e := field,
//        _0 := __ih0] post[fuel := S k, e := pattern, _0 := __ih0])`
//   * `fuel_outcome_functional_conclusion[fuel-outcome-induction:fuel=..;
//      out=<O>:<Done>|<Exh>:<exh_arity>;data=..;member=<m>;bases=1;cases=<n>]`
//       `Forall [fuel, e] post`   (`_0` free — the output slot).
//
// SOUNDNESS: this module only PRODUCES proof obligations; it discharges none.
// Emission is spec-driven — a false postcondition emits ITS bundle and the
// kernel rejects the generated discharge (trust-certify twin).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::HashMap;

use trust_types::{
    BlockId, Formula, Operand, Place, Projection, Rvalue, Sort, Statement, Terminator, Ty, VcKind,
    VerifiableFunction, VerificationCondition,
};

use crate::call_graph::{build_call_graph, is_self_recursive};
use crate::mutual_recursive_datatype_functional::{
    is_marker_safe_path, is_marker_safe_segment, nat_shape,
};
use crate::recursive_datatype_functional::{
    WalkState, apply_stmt, conjoin_all, discriminant_place, local_ty, peel_indirection,
    resolve_operand, resolve_place, subst_post, subst_vars,
};

/// Property tag prefix of the BASE (exhaustion) VC.
pub const OUTCOME_BASE_PROPERTY_PREFIX: &str = "fuel_outcome_functional_base::";
/// Property tag prefix of a STEP case VC.
pub const OUTCOME_CASE_PROPERTY_PREFIX: &str = "fuel_outcome_functional_case::";
/// Property tag prefix of the conclusion VC.
pub const OUTCOME_CONCLUSION_PROPERTY_PREFIX: &str = "fuel_outcome_functional_conclusion";
/// Property tag prefixes of the loop -> fuel-model SIMULATION VCs.
pub const LOOP_SIM_BAIL_PROPERTY_PREFIX: &str = "loop_fuel_sim_bail::";
pub const LOOP_SIM_DONE_PROPERTY_PREFIX: &str = "loop_fuel_sim_done::";
pub const LOOP_SIM_CONTINUE_PROPERTY_PREFIX: &str = "loop_fuel_sim_continue::";
pub const LOOP_SIM_CONCLUSION_PROPERTY_PREFIX: &str = "loop_fuel_sim_conclusion";

const FUEL_LOCAL: usize = 1;
const PAYLOAD_LOCAL: usize = 2;

/// The outcome datatype's classified shape.
struct OutcomeShape {
    /// `(tag, ctor)` of the Done constructor (unary, payload field).
    done: (usize, String),
    /// `(tag, ctor, arity)` of the Exhausted constructor (arity 0 or 1).
    exh: (usize, String, usize),
}

/// Classify `out` given which constructor the exhaustion arm returns.
fn outcome_shape(out: &Ty, payload_name: &str, exh_ctor: &str) -> Option<OutcomeShape> {
    let Ty::Datatype { variants, .. } = out else {
        return None;
    };
    if variants.len() != 2 {
        return None;
    }
    let field_is_payload = |fields: &[(String, Ty)]| {
        fields.iter().all(|(_, fty)| {
            matches!(peel_indirection(fty), Ty::Datatype { name, .. } if name == payload_name)
        })
    };
    let exh_tag = variants.iter().position(|(c, _)| c == exh_ctor)?;
    let done_tag = 1 - exh_tag;
    let (exh_name, exh_fields) = &variants[exh_tag];
    let (done_name, done_fields) = &variants[done_tag];
    if exh_fields.len() > 1 || !field_is_payload(exh_fields) {
        return None;
    }
    if done_fields.len() != 1 || !field_is_payload(done_fields) {
        return None;
    }
    Some(OutcomeShape {
        done: (done_tag, done_name.clone()),
        exh: (exh_tag, exh_name.clone(), exh_fields.len()),
    })
}

/// Which fuel arm the walk is currently under.
#[derive(Clone, Copy, PartialEq, Eq)]
enum FuelLayer {
    None,
    Base,
    Step,
}

struct ArmRec {
    tag: usize,
    ctor: String,
    /// `Some(field index)` iff the arm is the TAIL (continue) shape — the
    /// pattern field the self-call recursed on (travels in the property tag:
    /// `[calls=<m>:<field>]`; the VC formula cannot carry it because the
    /// gated postcondition never mentions the payload).
    tail: Option<usize>,
    formula: Formula,
}

#[derive(Default)]
struct FnOut {
    fuel_dt: Option<Ty>,
    fuel_z: Option<(usize, String)>,
    fuel_s: Option<(usize, String)>,
    payload_dt: Option<Ty>,
    /// The exhaustion constructor name observed at the base return.
    exh_ctor: Option<String>,
    base: Vec<Formula>,
    steps: Vec<ArmRec>,
}

/// Emit the fuel-outcome induction bundle for `func`. Empty (fail-closed)
/// outside the supported shape.
#[must_use]
#[allow(clippy::too_many_lines)]
pub fn fuel_outcome_functional_vcs(func: &VerifiableFunction) -> Vec<VerificationCondition> {
    let Some(vcs) = emit_bundle(func) else {
        return Vec::new();
    };
    if let Some(gap) = crate::contracts::functional_lane_unmodeled_postcondition_vc(
        func,
        "fuel-outcome functional induction",
    ) {
        return vec![gap];
    }
    vcs
}

#[allow(clippy::too_many_lines)]
fn emit_bundle(func: &VerifiableFunction) -> Option<Vec<VerificationCondition>> {
    if func.postconditions.is_empty()
        || func.body.arg_count != 2
        || !is_marker_safe_segment(&func.name)
    {
        return None;
    }
    let graph = build_call_graph(std::slice::from_ref(func));
    if !is_self_recursive(&graph, &func.def_path) {
        return None;
    }
    let post = conjoin_all(func.postconditions.clone());
    let entry = func.body.blocks.first()?;

    let mut out = FnOut::default();
    let mut ih_counter = 0usize;
    let ok = owalk(
        func,
        &post,
        entry.id,
        WalkState::default(),
        OArmCx::default(),
        FuelLayer::None,
        0,
        &mut ih_counter,
        &mut out,
    );
    if !ok {
        return None;
    }

    let fuel_dt = out.fuel_dt.clone()?;
    let Ty::Datatype { name: fuel_name, .. } = &fuel_dt else {
        return None;
    };
    let (fuel_z, fuel_s) = (out.fuel_z.clone()?, out.fuel_s.clone()?);
    let payload_dt = out.payload_dt.clone()?;
    let Ty::Datatype { name: payload_name, variants: payload_variants } = &payload_dt else {
        return None;
    };
    let out_dt = peel_indirection(&func.body.return_ty).clone();
    let Ty::Datatype { name: out_name, .. } = &out_dt else {
        return None;
    };
    let shape = outcome_shape(&out_dt, payload_name, out.exh_ctor.as_deref()?)?;
    if fuel_name == payload_name
        || fuel_name == out_name
        || payload_name == out_name
        || payload_variants.is_empty()
    {
        return None;
    }
    if !is_marker_safe_path(fuel_name)
        || !is_marker_safe_path(payload_name)
        || !is_marker_safe_path(out_name)
        || !is_marker_safe_segment(&fuel_z.1)
        || !is_marker_safe_segment(&fuel_s.1)
        || !is_marker_safe_segment(&shape.done.1)
        || !is_marker_safe_segment(&shape.exh.1)
        || !payload_variants.iter().all(|(c, _)| is_marker_safe_segment(c))
    {
        return None;
    }
    // Payload fields must be recursive payload fields only.
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
    // Coverage: one base, step arms cover every payload constructor once.
    out.steps.sort_by_key(|a| a.tag);
    let tags: Vec<usize> = out.steps.iter().map(|a| a.tag).collect();
    if out.base.len() != 1 || tags != (0..payload_variants.len()).collect::<Vec<_>>() {
        return None;
    }

    let name = func.name.as_str();
    let mk = |property: String, formula: Formula| VerificationCondition {
        kind: VcKind::FunctionalCorrectness { property, context: name.to_string() },
        function: name.into(),
        location: func.span.clone(),
        formula,
        contract_metadata: None,
    };
    let mut vcs = Vec::new();
    let e_name = crate::place_to_var_name(func, &Place::local(PAYLOAD_LOCAL));
    let e_sort = crate::sort_for_ty(&payload_dt);
    vcs.push(mk(
        format!("{OUTCOME_BASE_PROPERTY_PREFIX}{name}"),
        Formula::forall(&[(e_name.as_str(), e_sort.clone())], out.base[0].clone()),
    ));
    for arm in &out.steps {
        let calls = match arm.tail {
            Some(field) => format!("{name}:{field}"),
            None => String::new(),
        };
        vcs.push(mk(
            format!("{OUTCOME_CASE_PROPERTY_PREFIX}{name}::{}[calls={calls}]", arm.ctor),
            arm.formula.clone(),
        ));
    }
    let fuel_var_name = crate::place_to_var_name(func, &Place::local(FUEL_LOCAL));
    let conclusion = Formula::forall(
        &[(fuel_var_name.as_str(), crate::sort_for_ty(&fuel_dt)), (e_name.as_str(), e_sort)],
        post,
    );
    vcs.push(mk(
        format!(
            "{OUTCOME_CONCLUSION_PROPERTY_PREFIX}[fuel-outcome-induction:fuel={fuel_name}:{}|{};\
             out={out_name}:{}|{}:{};data={payload_name};member={name};bases=1;cases={}]",
            fuel_z.1,
            fuel_s.1,
            shape.done.1,
            shape.exh.1,
            shape.exh.2,
            out.steps.len()
        ),
        conclusion,
    ));
    Some(vcs)
}

/// Per-arm walk context.
#[derive(Clone, Default)]
struct OArmCx {
    k_name: Option<String>,
    field_names: Vec<String>,
    /// The tail call's IH variable and recursed-on field index, if the arm
    /// has called.
    ih_var: Option<(String, usize)>,
}

/// Validate a COMPLETE arm's Done payload tree: leaves are pattern fields;
/// nodes are payload constructors at arity.
fn valid_done_tree(f: &Formula, fields: &[String], payload_dt: &Ty) -> bool {
    if let Some(name) = f.var_name() {
        return fields.iter().any(|n| n == name);
    }
    let Formula::Ctor { ctor, args, .. } = f else {
        return false;
    };
    let Ty::Datatype { variants, .. } = payload_dt else {
        return false;
    };
    let Some((_, ctor_fields)) = variants.iter().find(|(c, _)| c == ctor) else {
        return false;
    };
    args.len() == ctor_fields.len() && args.iter().all(|a| valid_done_tree(a, fields, payload_dt))
}

/// Bounded CFG walk (the outcome twin of the threaded walk; single function).
#[allow(clippy::too_many_arguments, clippy::too_many_lines)]
fn owalk(
    func: &VerifiableFunction,
    post: &Formula,
    block_id: BlockId,
    mut state: WalkState,
    mut arm: OArmCx,
    fuel: FuelLayer,
    depth: usize,
    ih_counter: &mut usize,
    out: &mut FnOut,
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
            let Some(result) = resolve_place(func, &state, &Place::local(0)) else {
                return false;
            };
            match (fuel, state.ctor.clone()) {
                (FuelLayer::None, _) => false,
                (FuelLayer::Base, None) => {
                    // Exhaustion arm: `Exh` (nullary) or `Exh(e)` — pinned.
                    if !state.binders.is_empty() || !state.ih_atoms.is_empty() {
                        return false;
                    }
                    let Formula::Ctor { ctor, args, .. } = &result else {
                        return false;
                    };
                    let e_name = crate::place_to_var_name(func, &Place::local(PAYLOAD_LOCAL));
                    let args_ok = match args.as_slice() {
                        [] => true,
                        [only] => only.var_name() == Some(e_name.as_str()),
                        _ => false,
                    };
                    if !args_ok {
                        return false;
                    }
                    out.exh_ctor = Some(ctor.clone());
                    out.base.push(subst_post(func, post, &state, result.clone()));
                    out.base.len() == 1
                }
                (FuelLayer::Base, Some(_)) | (FuelLayer::Step, None) => false,
                (FuelLayer::Step, Some((tag, ctor_name))) => {
                    let tail = match (&arm.ih_var, &result) {
                        // TAIL arm: the result IS the self-call's output.
                        (Some((ih, field)), r) if r.var_name() == Some(ih.as_str()) => Some(*field),
                        // COMPLETE arm: no call; result = Done(tree).
                        (None, Formula::Ctor { args, .. }) => {
                            let [tree] = args.as_slice() else {
                                return false;
                            };
                            let Some(payload_dt) = out.payload_dt.clone() else {
                                return false;
                            };
                            if !valid_done_tree(tree, &arm.field_names, &payload_dt) {
                                return false;
                            }
                            None
                        }
                        _ => return false,
                    };
                    // For COMPLETE arms the returned ctor must be the OTHER
                    // (Done) constructor — checked at bundle level via
                    // outcome_shape; here record the arm.
                    if tail.is_none() {
                        let Formula::Ctor { ctor, .. } = &result else {
                            return false;
                        };
                        if Some(ctor) == out.exh_ctor.as_ref() {
                            return false; // a step arm may not fake exhaustion
                        }
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
                        tail,
                        formula: Formula::forall(&refs, body),
                    });
                    true
                }
            }
        }
        Terminator::Goto(target) => {
            owalk(func, post, *target, state, arm, fuel, depth + 1, ih_counter, out)
        }
        Terminator::Assert { target, .. } | Terminator::Drop { target, .. } => {
            owalk(func, post, *target, state, arm, fuel, depth + 1, ih_counter, out)
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
                        if !owalk(
                            func,
                            post,
                            *target,
                            arm_state,
                            arm_cx,
                            layer,
                            depth + 1,
                            ih_counter,
                            out,
                        ) {
                            return false;
                        }
                    }
                    true
                }
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
                        if !owalk(
                            func,
                            post,
                            *target,
                            arm_state,
                            arm_cx,
                            fuel,
                            depth + 1,
                            ih_counter,
                            out,
                        ) {
                            return false;
                        }
                    }
                    true
                }
                _ => false,
            }
        }
        Terminator::Call { func: callee, args, dest, target, .. } => {
            // TAIL self-call only: once per arm, at `(k, field)`.
            if fuel != FuelLayer::Step || state.ctor.is_none() || arm.ih_var.is_some() {
                return false;
            }
            if callee != &func.name && callee != &func.def_path {
                return false;
            }
            let Some(k_name) = arm.k_name.clone() else {
                return false;
            };
            let Some(target) = target else {
                return false;
            };
            if args.len() != 2 || !dest.projections.is_empty() {
                return false;
            }
            let Some(fuel_arg) = resolve_operand(func, &state, &args[0]) else {
                return false;
            };
            if fuel_arg.var_name() != Some(k_name.as_str()) {
                return false;
            }
            let Some(payload_arg) = resolve_operand(func, &state, &args[1]) else {
                return false;
            };
            let Some(field_idx) =
                payload_arg.var_name().and_then(|n| arm.field_names.iter().position(|f| f == n))
            else {
                return false;
            };
            let ih_name = format!("__ih{ih_counter}");
            *ih_counter += 1;
            let ret_sort = crate::sort_for_ty(peel_indirection(&func.body.return_ty));
            let ih_var = Formula::var_owned(ih_name.clone(), ret_sort.clone());
            state.binders.push((ih_name.clone(), ret_sort));
            state.store.insert(dest.local, ih_var.clone());
            let mut map: HashMap<String, Formula> = HashMap::new();
            map.insert(crate::place_to_var_name(func, &Place::local(FUEL_LOCAL)), fuel_arg);
            map.insert(crate::place_to_var_name(func, &Place::local(PAYLOAD_LOCAL)), payload_arg);
            map.insert("_0".to_string(), ih_var);
            state.ih_atoms.push(subst_vars(post.clone(), &map));
            arm.ih_var = Some((ih_name, field_idx));
            owalk(func, post, *target, state, arm, fuel, depth + 1, ih_counter, out)
        }
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// Item 3: the loop -> fuel-model per-iteration SIMULATION detector.
// ---------------------------------------------------------------------------

/// One classified loop payload arm.
enum LoopArm {
    /// `_0 = Done(tree)` then exit.
    Done(Formula),
    /// `cur = <field i>` then the back edge.
    Continue(usize),
}

/// Emit the per-iteration SIMULATION VCs for `loop_fn` against the fuel model
/// named by `model_fn`. Empty (fail-closed) unless `loop_fn` has the
/// whnf_outer_loop shape (counter switch at the loop head, in-program
/// decrement, exhausted-bail, per-ctor done/continue arms with the back
/// edge) and both functions share the fuel/payload/outcome signature.
#[must_use]
pub fn loop_fuel_sim_vcs(
    loop_fn: &VerifiableFunction,
    model_fn: &VerifiableFunction,
) -> Vec<VerificationCondition> {
    let Some(vcs) = emit_loop_sim(loop_fn, model_fn) else {
        return Vec::new();
    };
    vcs
}

#[allow(clippy::too_many_lines)]
fn emit_loop_sim(
    loop_fn: &VerifiableFunction,
    model_fn: &VerifiableFunction,
) -> Option<Vec<VerificationCondition>> {
    if loop_fn.body.arg_count != 2
        || model_fn.body.arg_count != 2
        || !is_marker_safe_segment(&loop_fn.name)
        || !is_marker_safe_segment(&model_fn.name)
        || loop_fn.name == model_fn.name
    {
        return None;
    }
    // Shared signature: (&Fuel, &E) -> O on both sides.
    let fuel_dt = peel_indirection(local_ty(loop_fn, FUEL_LOCAL)?).clone();
    let payload_dt = peel_indirection(local_ty(loop_fn, PAYLOAD_LOCAL)?).clone();
    let out_dt = peel_indirection(&loop_fn.body.return_ty).clone();
    if peel_indirection(local_ty(model_fn, FUEL_LOCAL)?) != &fuel_dt
        || peel_indirection(local_ty(model_fn, PAYLOAD_LOCAL)?) != &payload_dt
        || peel_indirection(&model_fn.body.return_ty) != &out_dt
    {
        return None;
    }
    let ((z_tag, z_ctor), (s_tag, s_ctor)) = nat_shape(&fuel_dt)?;
    let (Ty::Datatype { name: fuel_name, .. }, Ty::Datatype { name: payload_name, variants }) =
        (&fuel_dt, &payload_dt)
    else {
        return None;
    };
    let Ty::Datatype { name: out_name, .. } = &out_dt else {
        return None;
    };
    if variants.is_empty() {
        return None;
    }

    // ── Entry block: cur := *e; b := *fuel; goto head. ──────────────────────
    let entry = loop_fn.body.blocks.first()?;
    let mut cur_local: Option<usize> = None;
    let mut b_local: Option<usize> = None;
    for stmt in &entry.stmts {
        let Statement::Assign { place, rvalue, .. } = stmt else {
            return None;
        };
        if !place.projections.is_empty() {
            return None;
        }
        let Rvalue::Use(Operand::Copy(src) | Operand::Move(src)) = rvalue else {
            return None;
        };
        if src.projections != vec![Projection::Deref] {
            return None;
        }
        match src.local {
            PAYLOAD_LOCAL if cur_local.is_none() => cur_local = Some(place.local),
            FUEL_LOCAL if b_local.is_none() => b_local = Some(place.local),
            _ => return None,
        }
    }
    let (cur, b) = (cur_local?, b_local?);
    if peel_indirection(local_ty(loop_fn, cur)?) != &payload_dt
        || peel_indirection(local_ty(loop_fn, b)?) != &fuel_dt
    {
        return None;
    }
    let Terminator::Goto(head_id) = entry.terminator else {
        return None;
    };

    // ── Loop head: switch on the counter's discriminant. ────────────────────
    let head = loop_fn.body.blocks.iter().find(|blk| blk.id == head_id)?;
    let [Statement::Assign { place: d_place, rvalue: Rvalue::Discriminant(d_of), .. }] =
        head.stmts.as_slice()
    else {
        return None;
    };
    if !d_place.projections.is_empty() || d_of != &Place::local(b) {
        return None;
    }
    let Terminator::SwitchInt { discr, targets, .. } = &head.terminator else {
        return None;
    };
    let discr_ok = matches!(discr, Operand::Copy(p) | Operand::Move(p)
        if p == d_place);
    if !discr_ok {
        return None;
    }
    let mut sorted_tags: Vec<usize> = targets.iter().map(|(t, _)| *t as usize).collect();
    sorted_tags.sort_unstable();
    let mut expected = vec![z_tag, s_tag];
    expected.sort_unstable();
    if sorted_tags != expected {
        return None;
    }
    let z_target = targets.iter().find(|(t, _)| *t as usize == z_tag)?.1;
    let s_target = targets.iter().find(|(t, _)| *t as usize == s_tag)?.1;

    let fuel_sort = crate::sort_for_ty(&fuel_dt);
    let payload_sort = crate::sort_for_ty(&payload_dt);
    let out_sort = crate::sort_for_ty(&out_dt);
    let model_app = |fuel_arg: Formula, payload_arg: Formula| Formula::FnApp {
        func: model_fn.name.clone(),
        args: vec![fuel_arg, payload_arg],
        sort: out_sort.clone(),
    };
    let z_val = Formula::Ctor { ctor: z_ctor.clone(), args: vec![], sort: fuel_sort.clone() };
    let c_var = Formula::var_owned("__c".to_string(), payload_sort.clone());
    let k_var = Formula::var_owned("__k".to_string(), fuel_sort.clone());
    let s_k =
        Formula::Ctor { ctor: s_ctor.clone(), args: vec![k_var.clone()], sort: fuel_sort.clone() };

    // A block terminated by Return, or by Goto to an empty Return block.
    let exits = |blk: &trust_types::BasicBlock| -> bool {
        match blk.terminator {
            Terminator::Return => true,
            Terminator::Goto(t) => loop_fn.body.blocks.iter().any(|b2| {
                b2.id == t && b2.stmts.is_empty() && matches!(b2.terminator, Terminator::Return)
            }),
            _ => false,
        }
    };

    // ── Bail arm (counter = Z): _0 := Exh[(cur)], exit. ─────────────────────
    let bail = loop_fn.body.blocks.iter().find(|blk| blk.id == z_target)?;
    if !exits(bail) {
        return None;
    }
    let (exh_ctor, exh_arity) = {
        let mut state = WalkState::default();
        state.store.insert(cur, c_var.clone());
        for stmt in &bail.stmts {
            apply_stmt(loop_fn, &mut state, stmt);
        }
        let result = state.store.get(&0)?.clone();
        let Formula::Ctor { ctor, args, .. } = &result else {
            return None;
        };
        let arity_ok = match args.as_slice() {
            [] => true,
            [only] => only == &c_var,
            _ => false,
        };
        if !arity_ok {
            return None;
        }
        (ctor.clone(), args.len())
    };
    let shape = outcome_shape(&out_dt, payload_name, &exh_ctor)?;
    let exh_val = |carried: Formula| Formula::Ctor {
        ctor: exh_ctor.clone(),
        args: if exh_arity == 1 { vec![carried] } else { vec![] },
        sort: out_sort.clone(),
    };

    // ── Body arm (counter = S k): decrement then switch on cur. ─────────────
    let body = loop_fn.body.blocks.iter().find(|blk| blk.id == s_target)?;
    let (cur_switch_targets, decremented) = {
        let mut state = WalkState::default();
        state.store.insert(cur, c_var.clone());
        state.store.insert(
            b,
            Formula::Ctor {
                ctor: s_ctor.clone(),
                args: vec![k_var.clone()],
                sort: fuel_sort.clone(),
            },
        );
        for stmt in &body.stmts {
            apply_stmt(loop_fn, &mut state, stmt);
        }
        // The IN-PROGRAM DECREMENT: after the body's prologue the counter
        // local must hold exactly `k`.
        let decremented = state.store.get(&b) == Some(&k_var);
        let Terminator::SwitchInt { discr, targets, .. } = &body.terminator else {
            return None;
        };
        let matched = discriminant_place(&state, discr)?;
        if matched != Place::local(cur) {
            return None;
        }
        (targets.clone(), decremented)
    };
    if !decremented {
        return None;
    }
    let mut arm_tags: Vec<usize> = cur_switch_targets.iter().map(|(t, _)| *t as usize).collect();
    arm_tags.sort_unstable();
    if arm_tags != (0..variants.len()).collect::<Vec<_>>() {
        return None;
    }

    // ── Per-constructor arms. ────────────────────────────────────────────────
    let mut arms: Vec<(String, Vec<Formula>, LoopArm)> = Vec::new();
    for (tag, target) in &cur_switch_targets {
        let tag = *tag as usize;
        let (ctor, fields) = variants.get(tag)?.clone();
        let mut state = WalkState::default();
        let mut field_vars = Vec::with_capacity(fields.len());
        for (i, (_, fty)) in fields.iter().enumerate() {
            let v = Formula::var_owned(
                format!("__fld_{ctor}_{i}"),
                crate::sort_for_ty(peel_indirection(fty)),
            );
            field_vars.push(v);
        }
        state.store.insert(
            cur,
            Formula::Ctor {
                ctor: ctor.clone(),
                args: field_vars.clone(),
                sort: payload_sort.clone(),
            },
        );
        state.store.insert(b, k_var.clone());
        let blk = loop_fn.body.blocks.iter().find(|b2| &b2.id == target)?;
        for stmt in &blk.stmts {
            apply_stmt(loop_fn, &mut state, stmt);
        }
        let arm = if exits(blk) {
            // DONE arm: _0 = Done(tree over fields).
            let result = state.store.get(&0)?.clone();
            let Formula::Ctor { ctor: rctor, args, .. } = &result else {
                return None;
            };
            if rctor != &shape.done.1 {
                return None;
            }
            let [tree] = args.as_slice() else {
                return None;
            };
            let names: Vec<String> =
                field_vars.iter().filter_map(|v| v.var_name().map(str::to_string)).collect();
            if !valid_done_tree(tree, &names, &payload_dt) {
                return None;
            }
            LoopArm::Done(tree.clone())
        } else if matches!(blk.terminator, Terminator::Goto(t) if t == head_id) {
            // CONTINUE arm: the BACK EDGE. cur must now hold one field; the
            // counter must be untouched (still the decremented k).
            let new_cur = state.store.get(&cur)?.clone();
            if state.store.get(&b) != Some(&k_var) {
                return None;
            }
            let idx = field_vars.iter().position(|v| v == &new_cur)?;
            LoopArm::Continue(idx)
        } else {
            return None;
        };
        arms.push((ctor, field_vars, arm));
    }
    arms.sort_by(|(a, _, _), (b2, _, _)| {
        let pa = variants.iter().position(|(c, _)| c == a);
        let pb = variants.iter().position(|(c, _)| c == b2);
        pa.cmp(&pb)
    });

    // ── Emit the simulation equations. ──────────────────────────────────────
    let lname = loop_fn.name.as_str();
    let mk = |property: String, formula: Formula| VerificationCondition {
        kind: VcKind::FunctionalCorrectness { property, context: lname.to_string() },
        function: lname.into(),
        location: loop_fn.span.clone(),
        formula,
        contract_metadata: None,
    };
    let mut vcs = Vec::new();
    let mut equations = Vec::new();
    let bail_eq = Formula::forall(
        &[("__c", payload_sort.clone())],
        Formula::Eq(
            Box::new(model_app(z_val.clone(), c_var.clone())),
            Box::new(exh_val(c_var.clone())),
        ),
    );
    vcs.push(mk(format!("{LOOP_SIM_BAIL_PROPERTY_PREFIX}{lname}"), bail_eq.clone()));
    equations.push(bail_eq);
    let mut n_dones = 0usize;
    let mut n_continues = 0usize;
    for (ctor, field_vars, arm) in &arms {
        let mut binders: Vec<(&str, Sort)> = vec![("__k", fuel_sort.clone())];
        let names: Vec<String> =
            field_vars.iter().filter_map(|v| v.var_name().map(str::to_string)).collect();
        let sorts: Vec<Sort> = vec![payload_sort.clone(); names.len()];
        for (n, s) in names.iter().zip(&sorts) {
            binders.push((n.as_str(), s.clone()));
        }
        let pattern = Formula::Ctor {
            ctor: ctor.clone(),
            args: field_vars.clone(),
            sort: payload_sort.clone(),
        };
        let lhs = model_app(s_k.clone(), pattern);
        let (prop, rhs) = match arm {
            LoopArm::Done(tree) => {
                n_dones += 1;
                (
                    format!("{LOOP_SIM_DONE_PROPERTY_PREFIX}{lname}::{ctor}"),
                    Formula::Ctor {
                        ctor: shape.done.1.clone(),
                        args: vec![tree.clone()],
                        sort: out_sort.clone(),
                    },
                )
            }
            LoopArm::Continue(idx) => {
                n_continues += 1;
                (
                    format!("{LOOP_SIM_CONTINUE_PROPERTY_PREFIX}{lname}::{ctor}"),
                    model_app(k_var.clone(), field_vars[*idx].clone()),
                )
            }
        };
        let eq = Formula::forall(&binders, Formula::Eq(Box::new(lhs), Box::new(rhs)));
        vcs.push(mk(prop, eq.clone()));
        equations.push(eq);
    }
    vcs.push(mk(
        format!(
            "{LOOP_SIM_CONCLUSION_PROPERTY_PREFIX}[loop-fuel-sim:loop={lname};model={};\
             fuel={fuel_name}:{z_ctor}|{s_ctor};out={out_name}:{}|{}:{};data={payload_name};\
             bails=1;dones={n_dones};continues={n_continues}]",
            model_fn.name, shape.done.1, exh_ctor, exh_arity
        ),
        Formula::And(equations),
    ));
    Some(vcs)
}

/// HAND-BUILT fixture builders (the PEELER model + the whnf_outer_loop-shaped
/// LOOP twin) — shared by the unit tests below and by trust-integration-tests'
/// end-to-end drive of the literal emitted bundles. Not a public API surface.
#[doc(hidden)]
pub mod fixtures {
    use trust_types::{AggregateKind, BasicBlock, LocalDecl, SourceSpan, VerifiableBody};

    use super::*;

    // ── The PEELER fixture: the whnf_outer_loop shape in miniature ──────────────
    //
    // `peel_model : (&Fuel, &E) -> O` over `fuel::Fuel = Z | S(*const Fuel)`,
    // `expr::E = A | B(*const E)`, `outcome::O = Done(E) | Exh(E)`:
    //   peel_model(Z, e)      = Exh(e)         (exhausted-bail: the PARTIAL)
    //   peel_model(S k, A)    = Done(A)        (head-normal: complete)
    //   peel_model(S k, B x)  = peel_model(k, x)   (TAIL: peel one wrapper)
    // and `peel_loop`, the SAME computation as a loop with an in-program
    // counter decrement + exhausted-bail (the hand-modeled item-3 pair).

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
            ],
        }
    }

    pub fn o_dt() -> Ty {
        Ty::Datatype {
            name: "outcome::O".to_string(),
            variants: vec![
                ("Done".to_string(), vec![("0".to_string(), e_dt())]),
                ("Exh".to_string(), vec![("0".to_string(), e_dt())]),
            ],
        }
    }

    pub fn e_sort() -> Sort {
        crate::sort_for_ty(&e_dt())
    }

    pub fn o_sort() -> Sort {
        crate::sort_for_ty(&o_dt())
    }

    fn local(index: usize, ty: Ty, name: Option<&str>) -> LocalDecl {
        LocalDecl { index, ty, name: name.map(str::to_string) }
    }

    fn assign(place: Place, rvalue: Rvalue) -> Statement {
        Statement::Assign { place, rvalue, span: SourceSpan::default() }
    }

    /// The TRUE Done-conditional postcondition:
    /// `forall r, _0 = Done r -> r = A` — completion implies head-normal.
    pub fn done_conditional_post() -> Formula {
        Formula::forall(
            &[("r", e_sort())],
            Formula::Implies(
                Box::new(Formula::Eq(
                    Box::new(Formula::var_owned("_0".to_string(), o_sort())),
                    Box::new(Formula::Ctor {
                        ctor: "Done".to_string(),
                        args: vec![Formula::var_owned("r".to_string(), e_sort())],
                        sort: o_sort(),
                    }),
                )),
                Box::new(Formula::Eq(
                    Box::new(Formula::var_owned("r".to_string(), e_sort())),
                    Box::new(Formula::Ctor { ctor: "A".to_string(), args: vec![], sort: e_sort() }),
                )),
            ),
        )
    }

    /// The NEGATIVE-control postcondition: unconditional `_0 = Exh(..)` —
    /// TRUE on the exhaustion arm ONLY; must never certify for all fuel.
    /// (Stated with the ground witness `Exh(A)` so it is closed over `_0`.)
    pub fn exhausted_only_post() -> Formula {
        Formula::Eq(
            Box::new(Formula::var_owned("_0".to_string(), o_sort())),
            Box::new(Formula::Ctor {
                ctor: "Exh".to_string(),
                args: vec![Formula::Ctor { ctor: "A".to_string(), args: vec![], sort: e_sort() }],
                sort: o_sort(),
            }),
        )
    }

    /// A FALSE Done-conditional postcondition: `_0 = Done r -> r = B(A)`.
    pub fn wrong_done_post() -> Formula {
        Formula::forall(
            &[("r", e_sort())],
            Formula::Implies(
                Box::new(Formula::Eq(
                    Box::new(Formula::var_owned("_0".to_string(), o_sort())),
                    Box::new(Formula::Ctor {
                        ctor: "Done".to_string(),
                        args: vec![Formula::var_owned("r".to_string(), e_sort())],
                        sort: o_sort(),
                    }),
                )),
                Box::new(Formula::Eq(
                    Box::new(Formula::var_owned("r".to_string(), e_sort())),
                    Box::new(Formula::Ctor {
                        ctor: "B".to_string(),
                        args: vec![Formula::Ctor {
                            ctor: "A".to_string(),
                            args: vec![],
                            sort: e_sort(),
                        }],
                        sort: e_sort(),
                    }),
                )),
            ),
        )
    }

    /// The tail-recursive PEELER model in the extracted MIR shape.
    #[allow(clippy::too_many_lines)]
    pub fn peel_model_fn(name: &str, post: Vec<Formula>) -> VerifiableFunction {
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
        let reborrow = |dst: usize, of: usize| {
            assign(
                Place::local(dst),
                Rvalue::Ref {
                    mutable: false,
                    place: Place { local: of, projections: vec![Projection::Deref] },
                },
            )
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
                local(0, o_dt(), None),
                local(1, Ty::Ref { mutable: false, inner: Box::new(fuel_dt()) }, Some("fuel")),
                local(2, Ty::Ref { mutable: false, inner: Box::new(e_dt()) }, Some("e")),
                local(3, Ty::Int { width: 64, signed: true }, None), // fuel disc
                local(4, e_dt(), None),                              // e copy (bail)
                local(5, Ty::RawPtr { mutable: false, pointee: Box::new(fuel_dt()) }, None), // k
                local(6, Ty::Int { width: 64, signed: true }, None), // payload disc
                local(7, e_dt(), None),                              // A value
                local(8, raw_e, None),                               // B.x read
                local(9, Ty::Ref { mutable: false, inner: Box::new(fuel_dt()) }, None),
                local(10, Ty::Ref { mutable: false, inner: Box::new(e_dt()) }, None),
                local(11, o_dt(), Some("m")), // tail-call dest
            ],
            blocks: vec![
                // bb0: fuel switch.
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![disc(3, 1)],
                    terminator: switch(3, vec![(0, BlockId(2)), (1, BlockId(3))]),
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Unreachable },
                // bb2 (fuel Z): _0 = Exh(*e) — the exhausted-bail PARTIAL.
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![
                        assign(
                            Place::local(4),
                            Rvalue::Use(Operand::Copy(Place {
                                local: 2,
                                projections: vec![Projection::Deref],
                            })),
                        ),
                        assign(
                            Place::local(0),
                            adt("outcome::O", 1, vec![Operand::Move(Place::local(4))]),
                        ),
                    ],
                    terminator: Terminator::Goto(BlockId(7)),
                },
                // bb3 (fuel S): read k; payload switch.
                BasicBlock {
                    id: BlockId(3),
                    stmts: vec![deref_field(5, 1, 1, 0), disc(6, 2)],
                    terminator: switch(6, vec![(0, BlockId(4)), (1, BlockId(5))]),
                },
                // bb4 (step A): _0 = Done(A).
                BasicBlock {
                    id: BlockId(4),
                    stmts: vec![
                        assign(Place::local(7), adt("expr::E", 0, vec![])),
                        assign(
                            Place::local(0),
                            adt("outcome::O", 0, vec![Operand::Move(Place::local(7))]),
                        ),
                    ],
                    terminator: Terminator::Goto(BlockId(7)),
                },
                // bb5 (step B): TAIL self-call m(k, x) -> bb6.
                BasicBlock {
                    id: BlockId(5),
                    stmts: vec![deref_field(8, 2, 1, 0), reborrow(9, 5), reborrow(10, 8)],
                    terminator: Terminator::Call {
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: name.to_string(),
                        args: vec![Operand::Move(Place::local(9)), Operand::Move(Place::local(10))],
                        dest: Place::local(11),
                        target: Some(BlockId(6)),
                        span: SourceSpan::default(),
                        atomic: None,
                        unwind: trust_types::UnwindEdge::Unreachable,
                    },
                },
                // bb6: _0 = m (tail propagation).
                BasicBlock {
                    id: BlockId(6),
                    stmts: vec![assign(
                        Place::local(0),
                        Rvalue::Use(Operand::Move(Place::local(11))),
                    )],
                    terminator: Terminator::Goto(BlockId(7)),
                },
                // bb7: return.
                BasicBlock { id: BlockId(7), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 2,
            return_ty: o_dt(),
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

    /// The SAME computation as a LOOP: in-program counter decrement +
    /// exhausted-bail returning the partial + the back edge.
    #[allow(clippy::too_many_lines)]
    pub fn peel_loop_fn(name: &str, decrement: bool) -> VerifiableFunction {
        let adt = |dt: &str, variant: usize, ops: Vec<Operand>| {
            Rvalue::Aggregate(
                AggregateKind::Adt { name: dt.to_string(), variant, active_field: None, args: None },
                ops,
            )
        };
        let assign = |place: Place, rvalue: Rvalue| Statement::Assign {
            place,
            rvalue,
            span: SourceSpan::default(),
        };
        let switch = |d: usize, targets: Vec<(u128, BlockId)>| Terminator::SwitchInt {
            discr: Operand::Move(Place::local(d)),
            targets,
            otherwise: BlockId(2),
            exhaustive_enum_unreachable: true,
            span: SourceSpan::default(),
        };
        let body = VerifiableBody {
            locals: vec![
                local(0, o_dt(), None),
                local(1, Ty::Ref { mutable: false, inner: Box::new(fuel_dt()) }, Some("fuel")),
                local(2, Ty::Ref { mutable: false, inner: Box::new(e_dt()) }, Some("e")),
                local(3, e_dt(), Some("cur")), // the loop's current value
                local(4, fuel_dt(), Some("b")), // the in-program COUNTER
                local(5, Ty::Int { width: 64, signed: true }, None), // b disc
                local(6, fuel_dt(), None),     // k read (decrement source)
                local(7, Ty::Int { width: 64, signed: true }, None), // cur disc
                local(8, e_dt(), None),        // A value
                local(9, e_dt(), None),        // B.x read
            ],
            blocks: vec![
                // bb0 (entry): cur = *e; b = *fuel; goto head.
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![
                        assign(
                            Place::local(3),
                            Rvalue::Use(Operand::Copy(Place {
                                local: 2,
                                projections: vec![Projection::Deref],
                            })),
                        ),
                        assign(
                            Place::local(4),
                            Rvalue::Use(Operand::Copy(Place {
                                local: 1,
                                projections: vec![Projection::Deref],
                            })),
                        ),
                    ],
                    terminator: Terminator::Goto(BlockId(1)),
                },
                // bb1 (LOOP HEAD): switch on the counter.
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![assign(Place::local(5), Rvalue::Discriminant(Place::local(4)))],
                    terminator: switch(5, vec![(0, BlockId(3)), (1, BlockId(4))]),
                },
                BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Unreachable },
                // bb3 (bail): _0 = Exh(cur); exit — the PARTIAL result.
                BasicBlock {
                    id: BlockId(3),
                    stmts: vec![assign(
                        Place::local(0),
                        adt("outcome::O", 1, vec![Operand::Copy(Place::local(3))]),
                    )],
                    terminator: Terminator::Goto(BlockId(7)),
                },
                // bb4 (body): k = (b as S).0; b = k (the DECREMENT);
                //             switch on cur.
                BasicBlock {
                    id: BlockId(4),
                    stmts: {
                        let mut stmts = vec![assign(
                            Place::local(6),
                            Rvalue::Use(Operand::Copy(Place {
                                local: 4,
                                projections: vec![Projection::Downcast(1), Projection::Field(0)],
                            })),
                        )];
                        if decrement {
                            stmts.push(assign(
                                Place::local(4),
                                Rvalue::Use(Operand::Copy(Place::local(6))),
                            ));
                        }
                        stmts.push(assign(Place::local(7), Rvalue::Discriminant(Place::local(3))));
                        stmts
                    },
                    terminator: switch(7, vec![(0, BlockId(5)), (1, BlockId(6))]),
                },
                // bb5 (cur = A): _0 = Done(A); exit.
                BasicBlock {
                    id: BlockId(5),
                    stmts: vec![
                        assign(Place::local(8), adt("expr::E", 0, vec![])),
                        assign(
                            Place::local(0),
                            adt("outcome::O", 0, vec![Operand::Move(Place::local(8))]),
                        ),
                    ],
                    terminator: Terminator::Goto(BlockId(7)),
                },
                // bb6 (cur = B x): cur = x; BACK EDGE to the head.
                BasicBlock {
                    id: BlockId(6),
                    stmts: vec![
                        assign(
                            Place::local(9),
                            Rvalue::Use(Operand::Copy(Place {
                                local: 3,
                                projections: vec![Projection::Downcast(1), Projection::Field(0)],
                            })),
                        ),
                        assign(Place::local(3), Rvalue::Use(Operand::Copy(Place::local(9)))),
                    ],
                    terminator: Terminator::Goto(BlockId(1)),
                },
                // bb7: return.
                BasicBlock { id: BlockId(7), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 2,
            return_ty: o_dt(),
        };
        VerifiableFunction {
            name: name.to_string(),
            def_path: name.to_string(),
            span: SourceSpan::default(),
            body,
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }
}

#[cfg(test)]
mod tests {
    use trust_types::{AggregateKind, SourceSpan};

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

    // ── Test 1: the outcome bundle shape ─────────────────────────────────────────

    #[test]
    fn test_peeler_emits_outcome_bundle() {
        let f = peel_model_fn("peel_model", vec![done_conditional_post()]);
        let vcs = fuel_outcome_functional_vcs(&f);
        assert_eq!(
            properties(&vcs),
            vec![
                "fuel_outcome_functional_base::peel_model",
                "fuel_outcome_functional_case::peel_model::A[calls=]",
                "fuel_outcome_functional_case::peel_model::B[calls=peel_model:0]",
                "fuel_outcome_functional_conclusion[fuel-outcome-induction:\
                 fuel=fuel::Fuel:Z|S;out=outcome::O:Done|Exh:1;data=expr::E;\
                 member=peel_model;bases=1;cases=2]",
            ],
            "bundle: {vcs:#?}"
        );

        // Base: `Forall [e] (Forall [r] (Exh(e) = Done r -> r = A))` — the
        // Done-conditional post instantiated at the exhaustion arm (VACUOUS).
        let Formula::Forall(binders, body) = &vcs[0].formula else { panic!() };
        assert_eq!(binders.iter().map(|(s, _)| s.as_str()).collect::<Vec<_>>(), vec!["e"]);
        let Formula::Forall(inner, guard) = body.as_ref() else {
            panic!("base body must keep the post's Done binder, got {body:?}");
        };
        assert_eq!(inner.iter().map(|(s, _)| s.as_str()).collect::<Vec<_>>(), vec!["r"]);
        let Formula::Implies(hyp, _) = guard.as_ref() else { panic!() };
        let Formula::Eq(lhs, _) = hyp.as_ref() else { panic!() };
        let Formula::Ctor { ctor, args, .. } = lhs.as_ref() else {
            panic!("base guard lhs must be the exhaustion value, got {lhs:?}");
        };
        assert_eq!(ctor, "Exh");
        assert_eq!(args[0].var_name(), Some("e"), "the bail carries the PARTIAL input");

        // Tail arm: `IH => conclusion` with BOTH sides the post at `__ih0`.
        let Formula::Forall(binders, body) = &vcs[2].formula else { panic!() };
        assert_eq!(
            binders.iter().map(|(s, _)| s.as_str()).collect::<Vec<_>>(),
            vec!["__fld_S_0", "__fld_B_0", "__ih0"],
        );
        let Formula::Implies(ih, concl) = body.as_ref() else { panic!() };
        for side in [ih.as_ref(), concl.as_ref()] {
            let Formula::Forall(_, g) = side else { panic!("post shape survives, got {side:?}") };
            let Formula::Implies(hyp, _) = g.as_ref() else { panic!() };
            let Formula::Eq(l, _) = hyp.as_ref() else { panic!() };
            assert_eq!(l.var_name(), Some("__ih0"), "tail arms propagate the callee outcome");
        }
    }

    #[test]
    fn test_u8_wraparound_postcondition_emits_visible_unsupported_row() {
        let f = peel_model_fn("peel_model", vec![u8_wraparound_post()]);
        let vcs = fuel_outcome_functional_vcs(&f);
        assert_eq!(vcs.len(), 1, "the arithmetic gap must be one visible report row");
        assert!(matches!(
            &vcs[0].kind,
            VcKind::UnsupportedMir { kind, detail }
                if kind == crate::contracts::SPEC_UNVERIFIABLE_KIND
                    && detail.contains("fuel-outcome functional induction")
                    && detail.contains("unsupported_machine_arithmetic")
        ));
        assert_eq!(vcs[0].formula, Formula::Bool(true), "the gap must not be solver-provable");
    }

    #[test]
    fn test_u8_wraparound_postcondition_outside_lane_shape_emits_nothing() {
        let mut f = peel_model_fn("peel_model", vec![u8_wraparound_post()]);
        f.body.arg_count = 1;
        assert!(
            fuel_outcome_functional_vcs(&f).is_empty(),
            "arithmetic must not make an out-of-shape function appear owned by this lane"
        );
    }

    #[test]
    fn test_emission_is_spec_driven() {
        for post in [exhausted_only_post(), wrong_done_post()] {
            let f = peel_model_fn("peel_model", vec![post]);
            assert_eq!(
                fuel_outcome_functional_vcs(&f).len(),
                4,
                "emission is spec-driven; truth is the discharger's job"
            );
        }
    }

    #[test]
    fn test_non_tail_result_fails_closed() {
        // Rewire bb6 to wrap the tail result: _0 = Done(..) built from the
        // call dest is NOT the tail shape (the callee outcome must propagate).
        let mut f = peel_model_fn("peel_model", vec![done_conditional_post()]);
        for b in &mut f.body.blocks {
            if b.id == BlockId(6) {
                b.stmts = vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Aggregate(
                        AggregateKind::Adt {
                            name: "outcome::O".to_string(),
                            variant: 0,
                            active_field: None,
                            args: None,
                        },
                        vec![Operand::Move(Place::local(11))],
                    ),
                    span: SourceSpan::default(),
                }];
            }
        }
        assert!(fuel_outcome_functional_vcs(&f).is_empty());
    }

    #[test]
    fn test_no_postcondition_emits_nothing() {
        let f = peel_model_fn("peel_model", vec![]);
        assert!(fuel_outcome_functional_vcs(&f).is_empty());
    }

    // ── Test 2: the loop -> fuel-model simulation detector ───────────────────────

    #[test]
    fn test_loop_sim_equations() {
        let lp = peel_loop_fn("peel_loop", true);
        let model = peel_model_fn("peel_model", vec![done_conditional_post()]);
        let vcs = loop_fuel_sim_vcs(&lp, &model);
        assert_eq!(
            properties(&vcs),
            vec![
                "loop_fuel_sim_bail::peel_loop",
                "loop_fuel_sim_done::peel_loop::A",
                "loop_fuel_sim_continue::peel_loop::B",
                "loop_fuel_sim_conclusion[loop-fuel-sim:loop=peel_loop;model=peel_model;\
                 fuel=fuel::Fuel:Z|S;out=outcome::O:Done|Exh:1;data=expr::E;\
                 bails=1;dones=1;continues=1]",
            ],
            "sim: {vcs:#?}"
        );
        // continue B: `Forall [__k, __fld_B_0]
        //   model(S __k, B(x)) = model(__k, x)` — the PER-ITERATION SIMULATION.
        let Formula::Forall(_, body) = &vcs[2].formula else { panic!() };
        let Formula::Eq(lhs, rhs) = body.as_ref() else { panic!() };
        let Formula::FnApp { func, args, .. } = lhs.as_ref() else { panic!() };
        assert_eq!(func, "peel_model");
        let Formula::Ctor { ctor, .. } = &args[0] else { panic!() };
        assert_eq!(ctor, "S");
        let Formula::FnApp { func, args, .. } = rhs.as_ref() else {
            panic!("continue rhs must be the model one step later, got {rhs:?}");
        };
        assert_eq!(func, "peel_model");
        assert_eq!(args[0].var_name(), Some("__k"), "the model consumes the decremented fuel");
        assert_eq!(args[1].var_name(), Some("__fld_B_0"));
    }

    #[test]
    fn test_loop_without_decrement_fails_closed() {
        // The body never reassigns the counter: no in-program decrement, no
        // fuel-model simulation.
        let lp = peel_loop_fn("peel_loop", false);
        let model = peel_model_fn("peel_model", vec![done_conditional_post()]);
        assert!(
            loop_fuel_sim_vcs(&lp, &model).is_empty(),
            "a loop that does not decrement its counter must not emit sim VCs"
        );
    }
}
