// trust-certify: FUEL-OUTCOME discharge lane — SN-vs-fuel RESOLUTION items
// 2+3 (fail-closed exhaustion arms with Done-conditional postconditions;
// loop -> fuel-model per-iteration simulation).
//
// THIS lane consumes the bundle trust-vcgen's `fuel_outcome_functional` lane
// emits for a self-recursive outcome-returning fuel model
//
//   m : Fuel -> E -> O        O = Done(E) | Exh[(E)]
//   m Z e         = Exh[(e)]                  (the fail-closed exhaustion arm:
//                                              is_def_eq's false / infer's Err
//                                              marker, or the loop bail
//                                              carrying the PARTIAL)
//   m (S k) C(..) = Done(tree)                (complete arms)
//   m (S k) D(x)  = m k x                     (tail/continue arms)
//
// and machine-builds the kernel discharge of the DONE-CONDITIONAL
// postcondition
//
//   forall fuel e, (forall r, m fuel e = Done r -> t1(r) = t2(r))
//
// by ONE `Fuel.rec` induction: the BASE leg is the exhaustion arm's VACUITY,
// witnessed THROUGH the kernel (a two-constructor discriminator `O -> Prop`
// transported along the impossible `Exh[..] = Done r` into `False`, then
// `False.elim`) — never assumed; complete-arm minors transport the
// postcondition instance along Done-INJECTIVITY (a `congrArg` out-projection);
// tail-arm minors ARE the fuel IH applied at the recursed field (the
// tail-propagated outcome makes both sides definitionally equal).
//
// FUEL-MONOTONICITY (the item-2 lane lemma, machine-built + kernel-checked by
// `fuel_monotonicity_is_machine_built`):
//
//   forall f' f, f <= f' -> forall e r, m f e = Done r -> m f' e = Done r
//
// with `<=` a RECURSIVELY DEFINED bound predicate (`le Z f := f = Z;
// le (S k) f := f = S k \/ le k f` — recursion on the BOUND, so the proof
// needs neither inversion lemmas nor `Acc`): the lemma composes the
// SUCC-monotonicity induction (Done at m -> Done at S m, where complete arms
// are fuel-independent and tail arms are the IH) along the `<=` recursion.
// Reflexivity and `n <= S n` witnesses are checked too, so the bound
// predicate is demonstrably non-vacuous; the DOWNWARD (false) monotonicity
// statement is checked REJECTED against the same proof term.
//
// ITEM 3 — `certify_loop_fuel_sim`: consumes the per-iteration SIMULATION VCs
// trust-vcgen's loop detector emits for a whnf_outer_loop-shaped LOOP
// (in-program counter decrement + exhausted-bail returning the partial),
// CROSS-CHECKS them arm-by-arm against the model's own induction bundle (the
// honest handoff: the loop's per-path equations and the model's arms must be
// the SAME shape), and discharges each equation DEFINITIONALLY against the
// SAME rebuilt model — every loop path is one iota-step of the fold the
// induction ran on. The full trust-mir-extract loop-model EMISSION path is
// the named follow-up; this lane proves the discharge shape.
//
// NO MASQUERADE (kernel-witnessed):
//   * the Exhausted-only postcondition (`_0 = Exh(..)` — true ONLY on the
//     exhaustion arm) parses, builds, and is KERNEL-REJECTED at the complete
//     arm (the named negative control: a postcondition that holds only on the
//     Exhausted arm must NOT certify unconditionally);
//   * a FALSE Done-conditional postcondition is KERNEL-REJECTED at the
//     complete arm's transport base;
//   * the refl-only pseudo-proof of the true goal is REJECTED
//     (`fuel_outcome_induction_is_load_bearing`).
//
// SOUNDNESS (fail-closed, never a false `Certified`): evidence is minted ONLY
// when the clean kernel certifies `proof : goal`; env = `init_eq` +
// `init_true_false` + `init_or` + `init_and` + the reconstructed inductives +
// the model definition (no smuggled axioms), closed context; digest-bound and
// independently re-checked; every unsupported shape returns `None`.
//
// HONEST SCOPE: this certifies the reconstructed kernel model represented by
// the supplied typed VC bundles. Absent the named extraction/provenance bridge,
// it does NOT prove that those bundles came from a literal Rust/TrustIR
// recursion or loop implementation.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use clean_auto::bridge::ay_contract::{deserialize_term, serialize_term};
use clean_kernel::name::Name;
use clean_kernel::{
    BinderInfo, Constructor, Declaration, Environment, Expr, InductiveDecl, InductiveType, Level,
    LocalContext, TypeChecker,
};
use sha2::{Digest, Sha256};
use trust_types::{Formula, Sort, VcKind, VerificationCondition};

/// Lineage domain tags — distinct from every sibling lane.
const OUTCOME_LINEAGE_DOMAIN: &str = "trust-certify.cleancic.fuel-outcome-functional.v2";
const LOOP_SIM_LINEAGE_DOMAIN: &str = "trust-certify.cleancic.loop-fuel-sim.v2";

const BASE_PROPERTY_PREFIX: &str = "fuel_outcome_functional_base::";
const CASE_PROPERTY_PREFIX: &str = "fuel_outcome_functional_case::";
const CONCLUSION_PROPERTY_PREFIX: &str = "fuel_outcome_functional_conclusion";
const SIM_BAIL_PREFIX: &str = "loop_fuel_sim_bail::";
const SIM_DONE_PREFIX: &str = "loop_fuel_sim_done::";
const SIM_CONTINUE_PREFIX: &str = "loop_fuel_sim_continue::";
const SIM_CONCLUSION_PREFIX: &str = "loop_fuel_sim_conclusion";

// ---------------------------------------------------------------------------
// Bundle parsing.
// ---------------------------------------------------------------------------

/// A payload tree over an allowed variable set (by index into it).
#[derive(Clone, Debug, PartialEq, Eq)]
enum DTree {
    Var(usize),
    Node { ctor: String, args: Vec<DTree> },
}

/// The gated postcondition shapes.
#[derive(Clone, Debug, PartialEq, Eq)]
enum PostPlan {
    /// `forall r, _0 = Done r -> t1(r) = t2(r)` — trees over the single
    /// variable `r`.
    DoneCond { r: String, t1: DTree, t2: DTree },
    /// `_0 = <ground outcome value>` (outcome ctor over ground payload
    /// trees) — the Exhausted-only negative control rides this shape to the
    /// kernel.
    Ground { ctor: String, args: Vec<DTree> },
}

/// One step arm.
#[derive(Clone, Debug, PartialEq, Eq)]
enum OArm {
    /// `Done(tree)` — tree over the arm's pattern fields.
    Done(DTree),
    /// The tail self-call on pattern field `field`.
    Tail { field: usize },
}

struct OutcomePlan {
    fuel: String,
    fuel_z: String,
    fuel_s: String,
    out: String,
    done: String,
    exh: String,
    exh_arity: usize,
    data: String,
    fuel_full: String,
    out_full: String,
    data_full: String,
    member: String,
    ctors: Vec<(String, usize)>,
    arms: Vec<OArm>,
    post: PostPlan,
    label: String,
}

struct Marker {
    fuel_full: String,
    fuel_z: String,
    fuel_s: String,
    out_full: String,
    done: String,
    exh: String,
    exh_arity: usize,
    data_full: String,
    member: String,
    bases: usize,
    cases: usize,
}

fn parse_marker(property: &str) -> Option<Marker> {
    let marker = property.strip_prefix(CONCLUSION_PROPERTY_PREFIX)?;
    let marker = marker.strip_prefix("[fuel-outcome-induction:")?.strip_suffix(']')?;
    let mut fuel = None;
    let mut out = None;
    let mut data = None;
    let mut member = None;
    let mut bases = None;
    let mut cases = None;
    for field in marker.split(';') {
        let (key, value) = field.split_once('=')?;
        match key {
            "fuel" => {
                let (dt, ctors) = value.rsplit_once(':')?;
                let (z, s) = ctors.split_once('|')?;
                fuel = Some((dt.to_string(), z.to_string(), s.to_string()));
            }
            "out" => {
                // `<O>:<Done>|<Exh>:<arity>`.
                let (rest, arity) = value.rsplit_once(':')?;
                let (dt, ctors) = rest.rsplit_once(':')?;
                let (done, exh) = ctors.split_once('|')?;
                out = Some((
                    dt.to_string(),
                    done.to_string(),
                    exh.to_string(),
                    arity.parse::<usize>().ok()?,
                ));
            }
            "data" => data = Some(value.to_string()),
            "member" => member = Some(value.to_string()),
            "bases" => bases = value.parse().ok(),
            "cases" => cases = value.parse().ok(),
            _ => return None,
        }
    }
    let (fuel_full, fuel_z, fuel_s) = fuel?;
    let (out_full, done, exh, exh_arity) = out?;
    if exh_arity > 1 || done == exh {
        return None;
    }
    Some(Marker {
        fuel_full,
        fuel_z,
        fuel_s,
        out_full,
        done,
        exh,
        exh_arity,
        data_full: data?,
        member: member?,
        bases: bases?,
        cases: cases?,
    })
}

fn short_name(full: &str) -> Option<String> {
    let seg = full.rsplit("::").next()?;
    (!seg.is_empty() && seg.chars().all(|c| c.is_alphanumeric() || c == '_'))
        .then(|| seg.to_string())
}

fn split_forall(f: &Formula) -> (Vec<(String, Sort)>, &Formula) {
    match f {
        Formula::Forall(binders, body) => (
            binders.iter().map(|(sym, sort)| (sym.as_str().to_string(), sort.clone())).collect(),
            body.as_ref(),
        ),
        other => (Vec::new(), other),
    }
}

fn is_datatype_sort(sort: &Sort, dt: &str) -> bool {
    matches!(sort, Sort::Datatype { name, .. } if name == dt)
}

/// Parse a payload tree over `allowed` variables against the ctor table.
fn parse_dtree(f: &Formula, allowed: &[&str], ctors: &[(String, usize)]) -> Option<DTree> {
    if let Some(name) = f.var_name() {
        return Some(DTree::Var(allowed.iter().position(|a| *a == name)?));
    }
    let Formula::Ctor { ctor, args, .. } = f else {
        return None;
    };
    let (_, arity) = ctors.iter().find(|(c, _)| c == ctor)?;
    if args.len() != *arity {
        return None;
    }
    let out = args.iter().map(|a| parse_dtree(a, allowed, ctors)).collect::<Option<Vec<_>>>()?;
    Some(DTree::Node { ctor: ctor.clone(), args: out })
}

/// The `_0`-instance value check: `f` is the given outcome value.
enum InstValue<'a> {
    /// `Exh` / `Exh(<payload var>)`.
    Exh { arity: usize, exh: &'a str, carried: Option<&'a str> },
    /// `Done(tree over fields)` — returns the parsed tree via `out_tree`.
    Done { done: &'a str },
    /// A plain variable (the tail arm's `__ih`).
    Var(&'a str),
}

/// Check `body` is the plan's postcondition instantiated at `_0 := value`;
/// for `Done` values the payload tree is parsed against `fields` and
/// returned. `done_name` pins the guard's Done constructor to the plan's.
fn post_instance(
    body: &Formula,
    post: &PostPlan,
    value: &InstValue<'_>,
    fields: &[&str],
    ctors: &[(String, usize)],
    done_name: &str,
) -> Option<Option<DTree>> {
    // Match the `_0`-slot against `value`; `Done` yields the tree.
    let match_value = |slot: &Formula| -> Option<Option<DTree>> {
        match value {
            InstValue::Var(name) => (slot.var_name() == Some(name)).then_some(None),
            InstValue::Exh { arity, exh, carried } => {
                let Formula::Ctor { ctor, args, .. } = slot else {
                    return None;
                };
                if ctor != exh || args.len() != *arity {
                    return None;
                }
                match (args.as_slice(), carried) {
                    ([], None) => Some(None),
                    ([only], Some(c)) => (only.var_name() == Some(c)).then_some(None),
                    _ => None,
                }
            }
            InstValue::Done { done } => {
                let Formula::Ctor { ctor, args, .. } = slot else {
                    return None;
                };
                if ctor != *done {
                    return None;
                }
                let [tree] = args.as_slice() else {
                    return None;
                };
                Some(Some(parse_dtree(tree, fields, ctors)?))
            }
        }
    };
    match post {
        PostPlan::DoneCond { r, t1, t2 } => {
            let (binders, guarded) = split_forall(body);
            let [(r2, _)] = binders.as_slice() else {
                return None;
            };
            if r2 != r {
                return None;
            }
            let Formula::Implies(hyp, concl) = guarded else {
                return None;
            };
            let Formula::Eq(slot, done_r) = hyp.as_ref() else {
                return None;
            };
            let done_ok = matches!(done_r.as_ref(), Formula::Ctor { ctor, args, .. }
                if ctor == done_name
                    && args.len() == 1
                    && args[0].var_name() == Some(r2.as_str()));
            if !done_ok {
                return None;
            }
            let Formula::Eq(a, b) = concl.as_ref() else {
                return None;
            };
            let allowed = [r2.as_str()];
            if &parse_dtree(a, &allowed, ctors)? != t1 || &parse_dtree(b, &allowed, ctors)? != t2 {
                return None;
            }
            match_value(slot)
        }
        PostPlan::Ground { ctor, args } => {
            let Formula::Eq(slot, ground) = body else {
                return None;
            };
            let Formula::Ctor { ctor: gc, args: ga, .. } = ground.as_ref() else {
                return None;
            };
            if gc != ctor || ga.len() != args.len() {
                return None;
            }
            for (g, want) in ga.iter().zip(args) {
                if &parse_dtree(g, &[], ctors)? != want {
                    return None;
                }
            }
            match_value(slot)
        }
    }
}

/// Parse the emitted fuel-outcome bundle.
#[allow(clippy::too_many_lines)]
fn parse_bundle(vcs: &[VerificationCondition]) -> Option<OutcomePlan> {
    let mut conclusion: Option<&VerificationCondition> = None;
    let mut base: Option<&VerificationCondition> = None;
    let mut cases: Vec<(&str, &str, &VerificationCondition)> = Vec::new();
    let mut properties: Vec<String> = Vec::new();
    let mut member: Option<&str> = None;
    for vc in vcs {
        let VcKind::FunctionalCorrectness { property, context } = &vc.kind else {
            return None;
        };
        properties.push(property.clone());
        if let Some(m) = property.strip_prefix(BASE_PROPERTY_PREFIX) {
            if context != m || base.replace(vc).is_some() {
                return None;
            }
            match member {
                None => member = Some(m),
                Some(prev) if prev == m => {}
                _ => return None,
            }
        } else if let Some(rest) = property.strip_prefix(CASE_PROPERTY_PREFIX) {
            let (m, rest) = rest.split_once("::")?;
            let rest = rest.strip_suffix(']')?;
            let (ctor, calls) = rest.split_once("[calls=")?;
            if context != m {
                return None;
            }
            match member {
                None => member = Some(m),
                Some(prev) if prev == m => {}
                _ => return None,
            }
            cases.push((ctor, calls, vc));
        } else if property.starts_with(CONCLUSION_PROPERTY_PREFIX) {
            if conclusion.replace(vc).is_some() {
                return None;
            }
        } else {
            return None;
        }
    }
    let (conclusion, base) = (conclusion?, base?);
    let VcKind::FunctionalCorrectness { property: c_prop, context: c_ctx } = &conclusion.kind
    else {
        return None;
    };
    let marker = parse_marker(c_prop)?;
    if member != Some(marker.member.as_str()) || c_ctx != &marker.member {
        return None;
    }
    if marker.bases != 1 || marker.cases != cases.len() {
        return None;
    }
    let fuel = short_name(&marker.fuel_full)?;
    let out = short_name(&marker.out_full)?;
    let data = short_name(&marker.data_full)?;
    {
        let mut shorts = vec![fuel.as_str(), out.as_str(), data.as_str()];
        shorts.sort_unstable();
        let mut dedup = shorts.clone();
        dedup.dedup();
        if dedup.len() != shorts.len()
            || marker.fuel_z == marker.fuel_s
            || !marker.member.chars().all(|c| c.is_alphanumeric() || c == '_')
        {
            return None;
        }
    }

    // Constructor table from the case binders (ctor order = case order).
    let mut ctors: Vec<(String, usize)> = Vec::new();
    for (ctor, _, vc) in &cases {
        let (binders, _) = split_forall(&vc.formula);
        let mut fields = 0usize;
        for (name, sort) in &binders {
            if is_datatype_sort(sort, &marker.data_full) && name.starts_with("__fld_") {
                fields += 1;
            }
        }
        ctors.push(((*ctor).to_string(), fields));
    }
    {
        let mut names: Vec<&str> = ctors.iter().map(|(c, _)| c.as_str()).collect();
        names.sort_unstable();
        names.dedup();
        if names.len() != ctors.len() || ctors.is_empty() {
            return None;
        }
    }
    if ctors.iter().any(|(c, _)| c == &marker.done || c == &marker.exh) {
        return None;
    }

    // The conclusion: `Forall [fuel, e] post` (`_0` free).
    let (c_binders, post_formula) = split_forall(&conclusion.formula);
    let [(_, f_sort), (e_var, e_sort)] = c_binders.as_slice() else {
        return None;
    };
    if !is_datatype_sort(f_sort, &marker.fuel_full) || !is_datatype_sort(e_sort, &marker.data_full)
    {
        return None;
    }
    // Post grammar A (Done-conditional) or B (ground).
    let post = 'post: {
        if let Formula::Forall(binders, guarded) = post_formula {
            let [(r, r_sort)] = binders.as_slice() else {
                return None;
            };
            let r = r.as_str().to_string();
            if !is_datatype_sort(r_sort, &marker.data_full) || r == "_0" || &r == e_var {
                return None;
            }
            let Formula::Implies(hyp, concl) = guarded.as_ref() else {
                return None;
            };
            let Formula::Eq(slot, done_r) = hyp.as_ref() else {
                return None;
            };
            if slot.var_name() != Some("_0") {
                return None;
            }
            let done_ok = matches!(done_r.as_ref(), Formula::Ctor { ctor, args, .. }
                if ctor == &marker.done && args.len() == 1
                    && args[0].var_name() == Some(r.as_str()));
            if !done_ok {
                return None;
            }
            let Formula::Eq(a, b) = concl.as_ref() else {
                return None;
            };
            let allowed = [r.as_str()];
            let t1 = parse_dtree(a, &allowed, &ctors)?;
            let t2 = parse_dtree(b, &allowed, &ctors)?;
            break 'post PostPlan::DoneCond { r, t1, t2 };
        }
        let Formula::Eq(slot, ground) = post_formula else {
            return None;
        };
        if slot.var_name() != Some("_0") {
            return None;
        }
        let Formula::Ctor { ctor, args, .. } = ground.as_ref() else {
            return None;
        };
        let arity_ok = (ctor == &marker.done && args.len() == 1)
            || (ctor == &marker.exh && args.len() == marker.exh_arity);
        if !arity_ok {
            return None;
        }
        let args = args.iter().map(|a| parse_dtree(a, &[], &ctors)).collect::<Option<Vec<_>>>()?;
        PostPlan::Ground { ctor: ctor.clone(), args }
    };

    // Base VC: `Forall [e] post[_0 := Exh[(e)]]`.
    {
        let (b_binders, b_body) = split_forall(&base.formula);
        let [(be, be_sort)] = b_binders.as_slice() else {
            return None;
        };
        if !is_datatype_sort(be_sort, &marker.data_full) {
            return None;
        }
        let carried = (marker.exh_arity == 1).then_some(be.as_str());
        let inst = InstValue::Exh { arity: marker.exh_arity, exh: &marker.exh, carried };
        if post_instance(b_body, &post, &inst, &[], &ctors, &marker.done)?.is_some() {
            return None; // Exh never yields a tree
        }
    }

    // Case VCs.
    let mut arms: Vec<OArm> = Vec::with_capacity(cases.len());
    for ((ctor, calls, vc), (_, arity)) in cases.iter().zip(&ctors) {
        let (binders, body) = split_forall(&vc.formula);
        let mut k = None;
        let mut fields: Vec<String> = Vec::new();
        let mut ih: Option<String> = None;
        for (name, sort) in &binders {
            if is_datatype_sort(sort, &marker.fuel_full) {
                if k.replace(name.clone()).is_some() {
                    return None;
                }
            } else if is_datatype_sort(sort, &marker.data_full) && name.starts_with("__fld_") {
                fields.push(name.clone());
            } else if is_datatype_sort(sort, &marker.out_full) && name.starts_with("__ih") {
                if ih.replace(name.clone()).is_some() {
                    return None;
                }
            } else {
                return None;
            }
        }
        k?;
        if fields.len() != *arity {
            return None;
        }
        let field_refs: Vec<&str> = fields.iter().map(String::as_str).collect();
        if calls.is_empty() {
            // COMPLETE arm.
            if ih.is_some() {
                return None;
            }
            let tree = post_instance(
                body,
                &post,
                &InstValue::Done { done: &marker.done },
                &field_refs,
                &ctors,
                &marker.done,
            )??;
            arms.push(OArm::Done(tree));
        } else {
            // TAIL arm: `[calls=<member>:<field>]`.
            let (callee, field) = calls.split_once(':')?;
            if callee != marker.member {
                return None;
            }
            let field: usize = field.parse().ok()?;
            if field >= *arity {
                return None;
            }
            let ih = ih?;
            let Formula::Implies(p1, p2) = body else {
                return None;
            };
            if p1 != p2 {
                return None;
            }
            if post_instance(p1, &post, &InstValue::Var(&ih), &field_refs, &ctors, &marker.done)?
                .is_some()
            {
                return None;
            }
            let _ = ctor;
            arms.push(OArm::Tail { field });
        }
    }

    let label = format!(
        "fuel_outcome_functional:{}:[{}]:{:?}",
        marker.member,
        properties.join(";"),
        conclusion.formula
    );
    Some(OutcomePlan {
        fuel,
        fuel_z: marker.fuel_z.clone(),
        fuel_s: marker.fuel_s.clone(),
        out,
        done: marker.done.clone(),
        exh: marker.exh.clone(),
        exh_arity: marker.exh_arity,
        data,
        fuel_full: marker.fuel_full.clone(),
        out_full: marker.out_full.clone(),
        data_full: marker.data_full.clone(),
        member: marker.member.clone(),
        ctors,
        arms,
        post,
        label,
    })
}

// ---------------------------------------------------------------------------
// CIC construction.
// ---------------------------------------------------------------------------

fn level1() -> Level {
    Level::succ(Level::zero())
}

impl OutcomePlan {
    fn fuel_expr(&self) -> Expr {
        Expr::const_(Name::from_string(&self.fuel), Vec::new())
    }

    fn data_expr(&self) -> Expr {
        Expr::const_(Name::from_string(&self.data), Vec::new())
    }

    fn out_expr(&self) -> Expr {
        Expr::const_(Name::from_string(&self.out), Vec::new())
    }

    fn fuel_z_expr(&self) -> Expr {
        Expr::const_(Name::from_string(&format!("{}.{}", self.fuel, self.fuel_z)), Vec::new())
    }

    fn fuel_s_expr(&self) -> Expr {
        Expr::const_(Name::from_string(&format!("{}.{}", self.fuel, self.fuel_s)), Vec::new())
    }

    fn done_expr(&self) -> Expr {
        Expr::const_(Name::from_string(&format!("{}.{}", self.out, self.done)), Vec::new())
    }

    fn exh_expr(&self) -> Expr {
        Expr::const_(Name::from_string(&format!("{}.{}", self.out, self.exh)), Vec::new())
    }

    fn e_ctor(&self, ctor: &str) -> Option<Expr> {
        self.ctors.iter().find(|(c, _)| c == ctor)?;
        Some(Expr::const_(Name::from_string(&format!("{}.{ctor}", self.data)), Vec::new()))
    }

    fn model_expr(&self) -> Expr {
        Expr::const_(Name::from_string("__fo_model"), Vec::new())
    }

    fn le_expr(&self) -> Expr {
        Expr::const_(Name::from_string("__fo_le"), Vec::new())
    }

    /// `Eq.{1} <carrier> a b`.
    fn eq_of(&self, carrier: Expr, a: Expr, b: Expr) -> Expr {
        Expr::apps(Expr::const_(Name::from_string("Eq"), vec![level1()]), [carrier, a, b])
    }

    fn refl_of(&self, carrier: Expr, t: Expr) -> Expr {
        Expr::apps(Expr::const_(Name::from_string("Eq.refl"), vec![level1()]), [carrier, t])
    }

    /// `Exh[(payload)]` — the exhaustion value.
    fn exh_val(&self, payload: Option<Expr>) -> Expr {
        match (self.exh_arity, payload) {
            (0, _) => self.exh_expr(),
            (1, Some(p)) => Expr::app(self.exh_expr(), p),
            _ => self.exh_expr(), // unreachable by construction
        }
    }

    fn dtree_expr(&self, t: &DTree, var_at: &dyn Fn(usize) -> Expr) -> Option<Expr> {
        match t {
            DTree::Var(p) => Some(var_at(*p)),
            DTree::Node { ctor, args } => {
                let mut expr = self.e_ctor(ctor)?;
                for a in args {
                    expr = Expr::app(expr, self.dtree_expr(a, var_at)?);
                }
                Some(expr)
            }
        }
    }

    // ── Inductives + the model ───────────────────────────────────────────────

    fn fuel_inductive(&self) -> InductiveDecl {
        let fuel = self.fuel_expr();
        InductiveDecl {
            level_params: vec![],
            num_params: 0,
            types: vec![InductiveType {
                name: Name::from_string(&self.fuel),
                type_: Expr::type_(),
                constructors: vec![
                    Constructor {
                        name: Name::from_string(&format!("{}.{}", self.fuel, self.fuel_z)),
                        type_: fuel.clone(),
                    },
                    Constructor {
                        name: Name::from_string(&format!("{}.{}", self.fuel, self.fuel_s)),
                        type_: Expr::pi(BinderInfo::Default, fuel.clone(), fuel),
                    },
                ],
            }],
        }
    }

    fn data_inductive(&self) -> InductiveDecl {
        let data = self.data_expr();
        let constructors = self
            .ctors
            .iter()
            .map(|(ctor, arity)| Constructor {
                name: Name::from_string(&format!("{}.{ctor}", self.data)),
                type_: (0..*arity)
                    .fold(data.clone(), |acc, _| Expr::pi(BinderInfo::Default, data.clone(), acc)),
            })
            .collect();
        InductiveDecl {
            level_params: vec![],
            num_params: 0,
            types: vec![InductiveType {
                name: Name::from_string(&self.data),
                type_: Expr::type_(),
                constructors,
            }],
        }
    }

    /// `O = Done(E) | Exh[(E)]` — Done first, Exh second (recursor minor
    /// order follows).
    fn out_inductive(&self) -> InductiveDecl {
        let o = self.out_expr();
        let done_ty = Expr::pi(BinderInfo::Default, self.data_expr(), o.clone());
        let exh_ty = if self.exh_arity == 1 {
            Expr::pi(BinderInfo::Default, self.data_expr(), o.clone())
        } else {
            o.clone()
        };
        InductiveDecl {
            level_params: vec![],
            num_params: 0,
            types: vec![InductiveType {
                name: Name::from_string(&self.out),
                type_: Expr::type_(),
                constructors: vec![
                    Constructor {
                        name: Name::from_string(&format!("{}.{}", self.out, self.done)),
                        type_: done_ty,
                    },
                    Constructor {
                        name: Name::from_string(&format!("{}.{}", self.out, self.exh)),
                        type_: exh_ty,
                    },
                ],
            }],
        }
    }

    /// `__fo_model : Fuel -> E -> O` — the tail fold.
    fn model_def(&self) -> Option<Declaration> {
        // Base sheet: fun (e : E) => Exh[(e)] (formed under n, e — depth 2).
        let base =
            Expr::lam(BinderInfo::Default, self.data_expr(), self.exh_val(Some(Expr::bvar(0))));
        // Step: fun (k : Fuel) (prev : E -> O) (e : E) => E.rec ... e.
        // Levels: n = 0, k = 1, prev = 2, e = 3; E.rec applied at depth 4.
        let erec_depth = 4usize;
        let mut rec_args = vec![Expr::lam(BinderInfo::Default, self.data_expr(), self.out_expr())];
        for (arm, (_, arity)) in self.arms.iter().zip(&self.ctors) {
            let a = *arity;
            let body_depth = erec_depth + 2 * a;
            let field = |p: usize| Expr::bvar((body_depth - 1 - (erec_depth + p)) as u32);
            let body = match arm {
                OArm::Done(tree) => Expr::app(self.done_expr(), self.dtree_expr(tree, &field)?),
                OArm::Tail { field: f } => {
                    if *f >= a {
                        return None;
                    }
                    let prev = Expr::bvar((body_depth - 1 - 2) as u32);
                    Expr::app(prev, field(*f))
                }
            };
            let mut minor = body;
            for _ in 0..a {
                minor = Expr::lam(BinderInfo::Default, self.out_expr(), minor); // junk IHs
            }
            for _ in 0..a {
                minor = Expr::lam(BinderInfo::Default, self.data_expr(), minor); // fields
            }
            rec_args.push(minor);
        }
        rec_args.push(Expr::bvar(0)); // e at level 3 -> bvar(4-1-3)
        let e_rec = Expr::apps(
            Expr::const_(Name::from_string(&format!("{}.rec", self.data)), vec![level1()]),
            rec_args,
        );
        let step = Expr::lam(
            BinderInfo::Default,
            self.fuel_expr(),
            Expr::lam(
                BinderInfo::Default,
                Expr::pi(BinderInfo::Default, self.data_expr(), self.out_expr()),
                Expr::lam(BinderInfo::Default, self.data_expr(), e_rec),
            ),
        );
        let rec = Expr::apps(
            Expr::const_(Name::from_string(&format!("{}.rec", self.fuel)), vec![level1()]),
            [
                Expr::lam(
                    BinderInfo::Default,
                    self.fuel_expr(),
                    Expr::pi(BinderInfo::Default, self.data_expr(), self.out_expr()),
                ),
                base,
                step,
                Expr::bvar(0),
            ],
        );
        Some(Declaration::Definition {
            name: Name::from_string("__fo_model"),
            level_params: vec![],
            type_: Expr::pi(
                BinderInfo::Default,
                self.fuel_expr(),
                Expr::pi(BinderInfo::Default, self.data_expr(), self.out_expr()),
            ),
            value: Expr::lam(BinderInfo::Default, self.fuel_expr(), rec),
            is_reducible: true,
        })
    }

    fn build_env(&self) -> Option<Environment> {
        let mut env = Environment::default();
        env.init_eq().ok()?;
        env.init_and().ok()?;
        env.init_true_false().ok()?;
        env.init_or().ok()?;
        env.add_inductive(self.fuel_inductive()).ok()?;
        env.add_inductive(self.data_inductive()).ok()?;
        env.add_inductive(self.out_inductive()).ok()?;
        env.add_decl(self.model_def()?).ok()?;
        Some(env)
    }

    // ── The goal + proof ─────────────────────────────────────────────────────

    fn model_app(&self, fuel: Expr, e: Expr) -> Expr {
        Expr::apps(self.model_expr(), [fuel, e])
    }

    /// The postcondition proposition at `_0 := m0`, formed at depth `d`
    /// (`m0_at(at)` provides the value at any inner depth).
    fn post_prop(&self, m0_at: &dyn Fn(usize) -> Expr, d: usize) -> Option<Expr> {
        match &self.post {
            PostPlan::DoneCond { t1, t2, .. } => {
                // Pi (r : E). Pi (_ : Eq O m0 (Done r)). Eq E t1[r] t2[r].
                let hyp = self.eq_of(
                    self.out_expr(),
                    m0_at(d + 1),
                    Expr::app(self.done_expr(), Expr::bvar(0)),
                );
                let r_inner = |_: usize| Expr::bvar(1); // r under the hyp binder
                let concl = self.eq_of(
                    self.data_expr(),
                    self.dtree_expr(t1, &r_inner)?,
                    self.dtree_expr(t2, &r_inner)?,
                );
                Some(Expr::pi(
                    BinderInfo::Default,
                    self.data_expr(),
                    Expr::pi(BinderInfo::Default, hyp, concl),
                ))
            }
            PostPlan::Ground { ctor, args } => {
                let mut ground =
                    if ctor == &self.done { self.done_expr() } else { self.exh_expr() };
                for a in args {
                    ground = Expr::app(ground, self.dtree_expr(a, &|_| Expr::bvar(0))?);
                    // ground args are closed trees (no vars) — the var_at
                    // closure is never consulted for a well-parsed plan.
                }
                Some(self.eq_of(self.out_expr(), m0_at(d), ground))
            }
        }
    }

    /// `forall fuel e, post[model fuel e]`.
    fn goal(&self) -> Option<Expr> {
        let body = self.post_prop(
            &|at| self.model_app(Expr::bvar((at - 1) as u32), Expr::bvar((at - 2) as u32)),
            2,
        )?;
        Some(Expr::pi(
            BinderInfo::Default,
            self.fuel_expr(),
            Expr::pi(BinderInfo::Default, self.data_expr(), body),
        ))
    }

    /// The two-constructor discriminator `fun (o : O) => O.rec (Done ↦ False,
    /// Exh ↦ True) o` (a closed term).
    fn disc_lam(&self) -> Expr {
        let false_c = Expr::const_(Name::from_string("False"), Vec::new());
        let true_c = Expr::const_(Name::from_string("True"), Vec::new());
        let done_minor = Expr::lam(BinderInfo::Default, self.data_expr(), false_c);
        let exh_minor = if self.exh_arity == 1 {
            Expr::lam(BinderInfo::Default, self.data_expr(), true_c)
        } else {
            true_c
        };
        let rec = Expr::apps(
            Expr::const_(Name::from_string(&format!("{}.rec", self.out)), vec![level1()]),
            [
                Expr::lam(BinderInfo::Default, self.out_expr(), Expr::prop()),
                done_minor,
                exh_minor,
                Expr::bvar(0),
            ],
        );
        Expr::lam(BinderInfo::Default, self.out_expr(), rec)
    }

    /// From `h : Eq O <exh-value> (Done r)` conclude `goal_prop` (vacuity):
    /// transport `True.intro : disc(exh)` along `h` into `disc(Done r) = False`
    /// then `False.elim`. All exprs formed at depth `d`.
    fn vacuity(&self, exh_value: Expr, done_r: Expr, h: Expr, goal_prop: Expr) -> Expr {
        let transported = Expr::apps(
            Expr::const_(Name::from_string("Eq.ndrec"), vec![Level::zero(), level1()]),
            [
                self.out_expr(),
                exh_value,
                self.disc_lam(),
                Expr::const_(Name::from_string("True.intro"), Vec::new()),
                done_r,
                h,
            ],
        );
        Expr::apps(
            Expr::const_(Name::from_string("False.elim"), vec![Level::zero()]),
            [goal_prop, transported],
        )
    }

    /// The out-projection `fun (o : O) => O.rec (Done x ↦ x, Exh ↦ default)`;
    /// `default` must be a valid `E` at the USE depth + 1 (inside the lambda).
    fn out_proj_lam(&self, default_inside: Expr) -> Expr {
        let done_minor = Expr::lam(BinderInfo::Default, self.data_expr(), Expr::bvar(0));
        let exh_minor = if self.exh_arity == 1 {
            Expr::lam(BinderInfo::Default, self.data_expr(), Expr::bvar(0))
        } else {
            default_inside
        };
        let rec = Expr::apps(
            Expr::const_(Name::from_string(&format!("{}.rec", self.out)), vec![level1()]),
            [
                Expr::lam(BinderInfo::Default, self.out_expr(), self.data_expr()),
                done_minor,
                exh_minor,
                Expr::bvar(0),
            ],
        );
        Expr::lam(BinderInfo::Default, self.out_expr(), rec)
    }

    /// The joint induction proof.
    #[allow(clippy::too_many_lines)]
    fn proof(&self) -> Option<Expr> {
        // motive = fun (w : Fuel) => forall (e : E), post[model w e] (closed).
        let motive = {
            let body = self.post_prop(
                &|at| self.model_app(Expr::bvar((at - 1) as u32), Expr::bvar((at - 2) as u32)),
                2,
            )?;
            Expr::lam(
                BinderInfo::Default,
                self.fuel_expr(),
                Expr::pi(BinderInfo::Default, self.data_expr(), body),
            )
        };
        // Base leg (closed): fun (e : E) => <post at model Z e>.
        let base = match &self.post {
            PostPlan::DoneCond { t1, t2, .. } => {
                // fun e r (h : model Z e = Done r) => vacuity.
                let m0 =
                    |at: usize| self.model_app(self.fuel_z_expr(), Expr::bvar((at - 1) as u32));
                let h_ty =
                    self.eq_of(self.out_expr(), m0(2), Expr::app(self.done_expr(), Expr::bvar(0)));
                // Body at depth 3: e(0), r(1), h(2).
                let r_at3 = Expr::bvar(1);
                let goal_prop = self.eq_of(
                    self.data_expr(),
                    self.dtree_expr(t1, &|_| r_at3.clone())?,
                    self.dtree_expr(t2, &|_| r_at3.clone())?,
                );
                let body = self.vacuity(
                    self.model_app(self.fuel_z_expr(), Expr::bvar(2)),
                    Expr::app(self.done_expr(), r_at3.clone()),
                    Expr::bvar(0),
                    goal_prop,
                );
                Expr::lam(
                    BinderInfo::Default,
                    self.data_expr(),
                    Expr::lam(
                        BinderInfo::Default,
                        self.data_expr(),
                        Expr::lam(BinderInfo::Default, h_ty, body),
                    ),
                )
            }
            PostPlan::Ground { .. } => {
                // fun e => refl (model Z e) — kernel judges the ground value.
                Expr::lam(
                    BinderInfo::Default,
                    self.data_expr(),
                    self.refl_of(
                        self.out_expr(),
                        self.model_app(self.fuel_z_expr(), Expr::bvar(0)),
                    ),
                )
            }
        };
        // Step leg (closed): fun (k) (ih : forall e, post[model k e]) (e) =>
        //   E.rec (motive fun y => post[model (S k) y]) <minors> e.
        let step = {
            let k_at = |at: usize| Expr::bvar((at - 1) as u32);
            let s_k = |at: usize| Expr::app(self.fuel_s_expr(), k_at(at));
            let ih_ty = {
                // forall e, post[model k e] — at depth 1 (under k).
                let body = self.post_prop(
                    &|at| self.model_app(Expr::bvar((at - 1) as u32), Expr::bvar((at - 2) as u32)),
                    2,
                )?;
                Expr::pi(BinderInfo::Default, self.data_expr(), body)
            };
            // E.rec applied at depth 3 (k, ih, e).
            let erec_depth = 3usize;
            let e_motive = {
                // fun (y : E) => post[model (S k) y] — at depth 4.
                let body = self.post_prop(
                    &|at| self.model_app(s_k(at), Expr::bvar((at - 1 - erec_depth) as u32)),
                    erec_depth + 1,
                )?;
                Expr::lam(BinderInfo::Default, self.data_expr(), body)
            };
            let mut rec_args = vec![e_motive];
            for (arm, (ctor, arity)) in self.arms.iter().zip(&self.ctors) {
                let a = *arity;
                let body_depth = erec_depth + 2 * a;
                let field = |p: usize, at: usize| Expr::bvar((at - 1 - (erec_depth + p)) as u32);
                let pattern = |at: usize| -> Option<Expr> {
                    let mut expr = self.e_ctor(ctor)?;
                    for p in 0..a {
                        expr = Expr::app(expr, field(p, at));
                    }
                    Some(expr)
                };
                // Junk payload-IH binder types: motive applied at the field.
                let eih_ty = |ty_depth: usize, p: usize| -> Option<Expr> {
                    self.post_prop(&|at| self.model_app(s_k(at), field(p, at)), ty_depth)
                };
                let body = match arm {
                    OArm::Tail { field: f } => {
                        // ih applied at the recursed field: defeq to the goal
                        // via one iota step of the fold.
                        let ih = Expr::bvar((body_depth - 1 - 1) as u32);
                        Expr::app(ih, field(*f, body_depth))
                    }
                    OArm::Done(tree) => match &self.post {
                        PostPlan::Ground { .. } => self.refl_of(
                            self.out_expr(),
                            self.model_app(s_k(body_depth), pattern(body_depth)?),
                        ),
                        PostPlan::DoneCond { t1, t2, .. } => {
                            // fun (r : E) (h : model (S k) C(f) = Done r) =>
                            //   transport along Done-injectivity.
                            let d = body_depth;
                            let h_ty = self.eq_of(
                                self.out_expr(),
                                self.model_app(s_k(d + 1), pattern(d + 1)?),
                                Expr::app(self.done_expr(), Expr::bvar(0)),
                            );
                            // Inside: depth d+2; r = bvar(1), h = bvar(0).
                            let d2 = d + 2;
                            let tree_inst = self.dtree_expr(tree, &|p| field(p, d2))?;
                            // outp's Exh default sits one binder deeper.
                            let tree_inst_in = self.dtree_expr(tree, &|p| field(p, d2 + 1))?;
                            let outp = self.out_proj_lam(tree_inst_in);
                            let h_e = Expr::apps(
                                Expr::const_(
                                    Name::from_string("congrArg"),
                                    vec![level1(), level1()],
                                ),
                                [
                                    self.out_expr(),
                                    self.data_expr(),
                                    Expr::app(self.done_expr(), tree_inst.clone()),
                                    Expr::app(self.done_expr(), Expr::bvar(1)),
                                    outp,
                                    Expr::bvar(0),
                                ],
                            );
                            // motiveP = fun (x : E) => Eq E t1[x] t2[x].
                            let motive_p = {
                                let t1e = self.dtree_expr(t1, &|_| Expr::bvar(0))?;
                                let t2e = self.dtree_expr(t2, &|_| Expr::bvar(0))?;
                                Expr::lam(
                                    BinderInfo::Default,
                                    self.data_expr(),
                                    self.eq_of(self.data_expr(), t1e, t2e),
                                )
                            };
                            let base_refl = self.refl_of(
                                self.data_expr(),
                                self.dtree_expr(t1, &|_| tree_inst.clone())?,
                            );
                            let transported = Expr::apps(
                                Expr::const_(
                                    Name::from_string("Eq.ndrec"),
                                    vec![Level::zero(), level1()],
                                ),
                                [
                                    self.data_expr(),
                                    tree_inst,
                                    motive_p,
                                    base_refl,
                                    Expr::bvar(1),
                                    h_e,
                                ],
                            );
                            Expr::lam(
                                BinderInfo::Default,
                                self.data_expr(),
                                Expr::lam(BinderInfo::Default, h_ty, transported),
                            )
                        }
                    },
                };
                let mut minor = body;
                for q in (0..a).rev() {
                    minor = Expr::lam(BinderInfo::Default, eih_ty(erec_depth + a + q, q)?, minor);
                }
                for _ in 0..a {
                    minor = Expr::lam(BinderInfo::Default, self.data_expr(), minor);
                }
                rec_args.push(minor);
            }
            rec_args.push(Expr::bvar(0)); // e at level 2 -> bvar(3-1-2)
            let e_rec = Expr::apps(
                Expr::const_(Name::from_string(&format!("{}.rec", self.data)), vec![Level::zero()]),
                rec_args,
            );
            Expr::lam(
                BinderInfo::Default,
                self.fuel_expr(),
                Expr::lam(
                    BinderInfo::Default,
                    ih_ty,
                    Expr::lam(BinderInfo::Default, self.data_expr(), e_rec),
                ),
            )
        };
        let rec = Expr::apps(
            Expr::const_(Name::from_string(&format!("{}.rec", self.fuel)), vec![Level::zero()]),
            [motive, base, step, Expr::bvar(0)],
        );
        Some(Expr::lam(BinderInfo::Default, self.fuel_expr(), rec))
    }

    /// The refl-only pseudo-proof of the DONE-CONDITIONAL goal:
    /// `fun fuel e r h => Eq.ndrec (refl t1[r]) ..`? — no: the honest pseudo
    /// candidate is `fun fuel e r h => <refl at t1[r]>`, which only checks if
    /// `t1[r] ≡ t2[r]` for FREE r — i.e. without consuming the induction. For
    /// the Ground shape it is `fun fuel e => refl (model fuel e)`.
    fn refl_only_pseudo_proof(&self) -> Option<Expr> {
        let inner = match &self.post {
            PostPlan::DoneCond { t1, t2, .. } => {
                let _ = t2;
                // fun (r) (h) => Eq.refl E t1[r] : t1[r] = t2[r]?
                let h_ty = self.eq_of(
                    self.out_expr(),
                    self.model_app(Expr::bvar(2), Expr::bvar(1)),
                    Expr::app(self.done_expr(), Expr::bvar(0)),
                );
                let refl = self.refl_of(self.data_expr(), self.dtree_expr(t1, &|_| Expr::bvar(1))?);
                Expr::lam(
                    BinderInfo::Default,
                    self.data_expr(),
                    Expr::lam(BinderInfo::Default, h_ty, refl),
                )
            }
            PostPlan::Ground { .. } => {
                self.refl_of(self.out_expr(), self.model_app(Expr::bvar(1), Expr::bvar(0)))
            }
        };
        Some(Expr::lam(
            BinderInfo::Default,
            self.fuel_expr(),
            Expr::lam(BinderInfo::Default, self.data_expr(), inner),
        ))
    }

    // ── Fuel monotonicity (the item-2 lane lemma) ────────────────────────────

    /// `__fo_le : Fuel -> Fuel -> Prop` — `le Z f := f = Z;
    /// le (S k) f := (f = S k) \/ le k f` (recursion on the BOUND).
    fn le_def(&self) -> Declaration {
        let eq_fuel = |a: Expr, b: Expr| self.eq_of(self.fuel_expr(), a, b);
        // z-case: fun (m : Fuel) => m = Z (under n — depth 2 inside).
        let z_case = Expr::lam(
            BinderInfo::Default,
            self.fuel_expr(),
            eq_fuel(Expr::bvar(0), self.fuel_z_expr()),
        );
        // s-case: fun (kk) (prevP : Fuel -> Prop) (m) =>
        //   Or (m = S kk) (prevP m).
        let or_c = Expr::const_(Name::from_string("Or"), Vec::new());
        let s_case = Expr::lam(
            BinderInfo::Default,
            self.fuel_expr(),
            Expr::lam(
                BinderInfo::Default,
                Expr::pi(BinderInfo::Default, self.fuel_expr(), Expr::prop()),
                Expr::lam(
                    BinderInfo::Default,
                    self.fuel_expr(),
                    Expr::apps(
                        or_c,
                        [
                            eq_fuel(Expr::bvar(0), Expr::app(self.fuel_s_expr(), Expr::bvar(2))),
                            Expr::app(Expr::bvar(1), Expr::bvar(0)),
                        ],
                    ),
                ),
            ),
        );
        let rec = Expr::apps(
            Expr::const_(Name::from_string(&format!("{}.rec", self.fuel)), vec![level1()]),
            [
                Expr::lam(
                    BinderInfo::Default,
                    self.fuel_expr(),
                    Expr::pi(BinderInfo::Default, self.fuel_expr(), Expr::prop()),
                ),
                z_case,
                s_case,
                Expr::bvar(0),
            ],
        );
        Declaration::Definition {
            name: Name::from_string("__fo_le"),
            level_params: vec![],
            type_: Expr::pi(
                BinderInfo::Default,
                self.fuel_expr(),
                Expr::pi(BinderInfo::Default, self.fuel_expr(), Expr::prop()),
            ),
            value: Expr::lam(BinderInfo::Default, self.fuel_expr(), rec),
            is_reducible: true,
        }
    }

    fn le_app(&self, bound: Expr, m: Expr) -> Expr {
        Expr::apps(self.le_expr(), [bound, m])
    }

    /// `Done at f -> Done at f' >= f` statements. `downward = true` builds the
    /// FALSE inverted statement (the witness's negative).
    fn mono_type(&self, downward: bool) -> Expr {
        // Pi (f' f : Fuel), le f' f -> Pi (e r : E),
        //   model <src> e = Done r -> model <dst> e = Done r
        // where upward: src = f (the smaller), dst = f'.
        let eq_o = |a: Expr, b: Expr| self.eq_of(self.out_expr(), a, b);
        // Binders: f'(0), f(1), hle(2), e(3), r(4), h(5); body depth 6.
        let at = |level: usize, depth: usize| Expr::bvar((depth - 1 - level) as u32);
        let src_at = |depth: usize| if downward { at(0, depth) } else { at(1, depth) };
        let dst_at = |depth: usize| if downward { at(1, depth) } else { at(0, depth) };
        let hyp = eq_o(self.model_app(src_at(5), at(3, 5)), Expr::app(self.done_expr(), at(4, 5)));
        let concl =
            eq_o(self.model_app(dst_at(6), at(3, 6)), Expr::app(self.done_expr(), at(4, 6)));
        Expr::pi(
            BinderInfo::Default,
            self.fuel_expr(),
            Expr::pi(
                BinderInfo::Default,
                self.fuel_expr(),
                Expr::pi(
                    BinderInfo::Default,
                    self.le_app(at(0, 2), at(1, 2)),
                    Expr::pi(
                        BinderInfo::Default,
                        self.data_expr(),
                        Expr::pi(
                            BinderInfo::Default,
                            self.data_expr(),
                            Expr::pi(BinderInfo::Default, hyp, concl),
                        ),
                    ),
                ),
            ),
        )
    }

    /// `succ_mono : Pi (m : Fuel) (e r : E),
    ///    model m e = Done r -> model (S m) e = Done r` — the term.
    fn succ_mono_term(&self) -> Option<Expr> {
        let eq_o = |a: Expr, b: Expr| self.eq_of(self.out_expr(), a, b);
        let at = |level: usize, depth: usize| Expr::bvar((depth - 1 - level) as u32);
        // motive = fun (w : Fuel) => Pi (e r), model w e = Done r ->
        //   model (S w) e = Done r  (closed).
        let motive = {
            // w(0), e(1), r(2), h(3).
            let hyp =
                eq_o(self.model_app(at(0, 3), at(1, 3)), Expr::app(self.done_expr(), at(2, 3)));
            let concl = eq_o(
                self.model_app(Expr::app(self.fuel_s_expr(), at(0, 4)), at(1, 4)),
                Expr::app(self.done_expr(), at(2, 4)),
            );
            Expr::lam(
                BinderInfo::Default,
                self.fuel_expr(),
                Expr::pi(
                    BinderInfo::Default,
                    self.data_expr(),
                    Expr::pi(
                        BinderInfo::Default,
                        self.data_expr(),
                        Expr::pi(BinderInfo::Default, hyp, concl),
                    ),
                ),
            )
        };
        // Base (closed): fun (e r) (h : model Z e = Done r) => vacuity into
        // `model (S Z) e = Done r`.
        let base = {
            // e(0), r(1), h(2); body depth 3.
            let h_ty = eq_o(
                self.model_app(self.fuel_z_expr(), at(0, 2)),
                Expr::app(self.done_expr(), at(1, 2)),
            );
            let goal_prop = eq_o(
                self.model_app(Expr::app(self.fuel_s_expr(), self.fuel_z_expr()), at(0, 3)),
                Expr::app(self.done_expr(), at(1, 3)),
            );
            let body = self.vacuity(
                self.model_app(self.fuel_z_expr(), at(0, 3)),
                Expr::app(self.done_expr(), at(1, 3)),
                Expr::bvar(0),
                goal_prop,
            );
            Expr::lam(
                BinderInfo::Default,
                self.data_expr(),
                Expr::lam(
                    BinderInfo::Default,
                    self.data_expr(),
                    Expr::lam(BinderInfo::Default, h_ty, body),
                ),
            )
        };
        // Step (closed): fun (kk) (ihk : motive kk) (e) => E.rec ... e.
        let step = {
            // kk(0), ihk(1), e(2); E.rec at depth 3.
            let s_kk = |depth: usize| Expr::app(self.fuel_s_expr(), at(0, depth));
            let ss_kk = |depth: usize| Expr::app(self.fuel_s_expr(), s_kk(depth));
            let ihk_ty = {
                // motive kk written out: e(1), r(2), h(3) under kk(0).
                let hyp =
                    eq_o(self.model_app(at(0, 3), at(1, 3)), Expr::app(self.done_expr(), at(2, 3)));
                let concl =
                    eq_o(self.model_app(s_kk(4), at(1, 4)), Expr::app(self.done_expr(), at(2, 4)));
                Expr::pi(
                    BinderInfo::Default,
                    self.data_expr(),
                    Expr::pi(
                        BinderInfo::Default,
                        self.data_expr(),
                        Expr::pi(BinderInfo::Default, hyp, concl),
                    ),
                )
            };
            let erec_depth = 3usize;
            let e_motive = {
                // fun (y : E) => Pi (r), model (S kk) y = Done r ->
                //   model (S (S kk)) y = Done r. y(3), r(4), h(5).
                let hyp =
                    eq_o(self.model_app(s_kk(5), at(3, 5)), Expr::app(self.done_expr(), at(4, 5)));
                let concl =
                    eq_o(self.model_app(ss_kk(6), at(3, 6)), Expr::app(self.done_expr(), at(4, 6)));
                Expr::lam(
                    BinderInfo::Default,
                    self.data_expr(),
                    Expr::pi(
                        BinderInfo::Default,
                        self.data_expr(),
                        Expr::pi(BinderInfo::Default, hyp, concl),
                    ),
                )
            };
            let mut rec_args = vec![e_motive];
            for (arm, (ctor, arity)) in self.arms.iter().zip(&self.ctors) {
                let a = *arity;
                let body_depth = erec_depth + 2 * a;
                let field = |p: usize, depth: usize| at(erec_depth + p, depth);
                let pattern = |depth: usize| -> Option<Expr> {
                    let mut expr = self.e_ctor(ctor)?;
                    for p in 0..a {
                        expr = Expr::app(expr, field(p, depth));
                    }
                    Some(expr)
                };
                let eih_ty = |ty_depth: usize, p: usize| {
                    let hyp = eq_o(
                        self.model_app(s_kk(ty_depth + 1), field(p, ty_depth + 1)),
                        Expr::app(self.done_expr(), Expr::bvar(0)),
                    );
                    let concl = eq_o(
                        self.model_app(ss_kk(ty_depth + 2), field(p, ty_depth + 2)),
                        Expr::app(self.done_expr(), Expr::bvar(1)),
                    );
                    Expr::pi(
                        BinderInfo::Default,
                        self.data_expr(),
                        Expr::pi(BinderInfo::Default, hyp, concl),
                    )
                };
                let body = match arm {
                    // Complete arm: fuel-independent — the identity.
                    OArm::Done(_) => {
                        let d = body_depth;
                        let h_ty = eq_o(
                            self.model_app(s_kk(d + 1), pattern(d + 1)?),
                            Expr::app(self.done_expr(), Expr::bvar(0)),
                        );
                        Expr::lam(
                            BinderInfo::Default,
                            self.data_expr(),
                            Expr::lam(BinderInfo::Default, h_ty, Expr::bvar(0)),
                        )
                    }
                    // Tail arm: exactly the fuel IH at the recursed field.
                    OArm::Tail { field: f } => {
                        let ihk = at(1, body_depth);
                        Expr::app(ihk, field(*f, body_depth))
                    }
                };
                let mut minor = body;
                for q in (0..a).rev() {
                    minor = Expr::lam(BinderInfo::Default, eih_ty(erec_depth + a + q, q), minor);
                }
                for _ in 0..a {
                    minor = Expr::lam(BinderInfo::Default, self.data_expr(), minor);
                }
                rec_args.push(minor);
            }
            rec_args.push(Expr::bvar(0));
            let e_rec = Expr::apps(
                Expr::const_(Name::from_string(&format!("{}.rec", self.data)), vec![Level::zero()]),
                rec_args,
            );
            Expr::lam(
                BinderInfo::Default,
                self.fuel_expr(),
                Expr::lam(
                    BinderInfo::Default,
                    ihk_ty,
                    Expr::lam(BinderInfo::Default, self.data_expr(), e_rec),
                ),
            )
        };
        let rec = Expr::apps(
            Expr::const_(Name::from_string(&format!("{}.rec", self.fuel)), vec![Level::zero()]),
            [motive, base, step, Expr::bvar(0)],
        );
        Some(Expr::lam(BinderInfo::Default, self.fuel_expr(), rec))
    }

    fn succ_mono_type(&self) -> Expr {
        let eq_o = |a: Expr, b: Expr| self.eq_of(self.out_expr(), a, b);
        let at = |level: usize, depth: usize| Expr::bvar((depth - 1 - level) as u32);
        // m(0), e(1), r(2), h(3).
        let hyp = eq_o(self.model_app(at(0, 3), at(1, 3)), Expr::app(self.done_expr(), at(2, 3)));
        let concl = eq_o(
            self.model_app(Expr::app(self.fuel_s_expr(), at(0, 4)), at(1, 4)),
            Expr::app(self.done_expr(), at(2, 4)),
        );
        Expr::pi(
            BinderInfo::Default,
            self.fuel_expr(),
            Expr::pi(
                BinderInfo::Default,
                self.data_expr(),
                Expr::pi(
                    BinderInfo::Default,
                    self.data_expr(),
                    Expr::pi(BinderInfo::Default, hyp, concl),
                ),
            ),
        )
    }

    /// The mono proof term (references `__fo_succ_mono`).
    #[allow(clippy::too_many_lines)]
    fn mono_term(&self) -> Expr {
        let eq_o = |a: Expr, b: Expr| self.eq_of(self.out_expr(), a, b);
        let eq_f = |a: Expr, b: Expr| self.eq_of(self.fuel_expr(), a, b);
        let at = |level: usize, depth: usize| Expr::bvar((depth - 1 - level) as u32);
        let succ_mono = Expr::const_(Name::from_string("__fo_succ_mono"), Vec::new());
        // Goal-tail at a given source/destination fuel closure:
        // Pi (e r), model src e = Done r -> model dst e = Done r.
        let goal_tail =
            |src: &dyn Fn(usize) -> Expr, dst: &dyn Fn(usize) -> Expr, d: usize| -> Expr {
                // binders e(d), r(d+1), h(d+2) — depths relative.
                let hyp = eq_o(
                    self.model_app(src(d + 2), at(d, d + 2)),
                    Expr::app(self.done_expr(), at(d + 1, d + 2)),
                );
                let concl = eq_o(
                    self.model_app(dst(d + 3), at(d, d + 3)),
                    Expr::app(self.done_expr(), at(d + 1, d + 3)),
                );
                Expr::pi(
                    BinderInfo::Default,
                    self.data_expr(),
                    Expr::pi(
                        BinderInfo::Default,
                        self.data_expr(),
                        Expr::pi(BinderInfo::Default, hyp, concl),
                    ),
                )
            };
        let id_tail = |src: &dyn Fn(usize) -> Expr, d: usize| -> Expr {
            let hyp = eq_o(
                self.model_app(src(d + 2), at(d, d + 2)),
                Expr::app(self.done_expr(), at(d + 1, d + 2)),
            );
            Expr::lam(
                BinderInfo::Default,
                self.data_expr(),
                Expr::lam(
                    BinderInfo::Default,
                    self.data_expr(),
                    Expr::lam(BinderInfo::Default, hyp, Expr::bvar(0)),
                ),
            )
        };
        // The transport of the identity along `x = <target>` (symm'd):
        // given hle : Eq <x> <target>, produce goal_tail(src = x-var).
        // ndrec: motive Q = fun (v : Fuel) => goal_tail(src = v, dst fixed).
        // motive_m = fun (w) => Pi (f), le w f -> goal_tail(src = f, dst = w).
        let motive_m = {
            // w(0), f(1), hle(2).
            let src = |d: usize| at(1, d);
            let dst = |d: usize| at(0, d);
            Expr::lam(
                BinderInfo::Default,
                self.fuel_expr(),
                Expr::pi(
                    BinderInfo::Default,
                    self.fuel_expr(),
                    Expr::pi(
                        BinderInfo::Default,
                        self.le_app(at(0, 2), at(1, 2)),
                        goal_tail(&src, &dst, 3),
                    ),
                ),
            )
        };
        // base_m: fun (f) (hle : le Z f) => ndrec (Q := fun v =>
        //   goal_tail(src v, dst Z)) (id at Z) (symm hle).
        let base_m = {
            // f(0), hle(1); body depth 2.
            let q = {
                // v(0) inside the lambda.
                let src = |d: usize| at(2, d); // v is at level 2 when Q's
                // lambda is formed at depth 2: binder v -> level 2.
                let dst = |_d: usize| self.fuel_z_expr();
                Expr::lam(BinderInfo::Default, self.fuel_expr(), goal_tail(&src, &dst, 3))
            };
            let id_term = id_tail(&|_d| self.fuel_z_expr(), 2);
            let symm = Expr::apps(
                Expr::const_(Name::from_string("Eq.symm"), vec![level1()]),
                [self.fuel_expr(), at(0, 2), self.fuel_z_expr(), at(1, 2)],
            );
            let nd = Expr::apps(
                Expr::const_(Name::from_string("Eq.ndrec"), vec![Level::zero(), level1()]),
                [self.fuel_expr(), self.fuel_z_expr(), q, id_term, at(0, 2), symm],
            );
            Expr::lam(
                BinderInfo::Default,
                self.fuel_expr(),
                Expr::lam(BinderInfo::Default, self.le_app(self.fuel_z_expr(), Expr::bvar(0)), nd),
            )
        };
        // step_m: fun (kk) (ihw : motive kk) (f) (hle : le (S kk) f) =>
        //   Or.rec A B (fun _ => goal) inl inr hle.
        let step_m = {
            // kk(0), ihw(1), f(2), hle(3); body depth 4.
            let s_kk = |d: usize| Expr::app(self.fuel_s_expr(), at(0, d));
            let ihw_ty = {
                // motive kk written out: f(1), hle(2) under kk(0).
                let src = |d: usize| at(1, d);
                let dst = |d: usize| at(0, d);
                Expr::pi(
                    BinderInfo::Default,
                    self.fuel_expr(),
                    Expr::pi(
                        BinderInfo::Default,
                        self.le_app(at(0, 2), at(1, 2)),
                        goal_tail(&src, &dst, 3),
                    ),
                )
            };
            let hle_ty = self.le_app(s_kk(3), at(2, 3));
            let a_prop = eq_f(at(2, 4), s_kk(4));
            let b_prop = self.le_app(at(0, 4), at(2, 4));
            let goal = goal_tail(&|d| at(2, d), &|d| s_kk(d), 4);
            let or_motive = Expr::lam(
                BinderInfo::Default,
                Expr::apps(
                    Expr::const_(Name::from_string("Or"), Vec::new()),
                    [a_prop.clone(), b_prop.clone()],
                ),
                goal_tail(&|d| at(2, d), &|d| s_kk(d), 5),
            );
            // inl: fun (h1 : f = S kk) => ndrec (Q := fun v => goal_tail(src
            // v, dst (S kk))) (id at S kk) (symm h1).
            let inl = {
                // h1 at level 4; body depth 5.
                let q = {
                    let src = |d: usize| at(5, d); // v bound at level 5
                    let dst = |d: usize| s_kk(d);
                    Expr::lam(BinderInfo::Default, self.fuel_expr(), goal_tail(&src, &dst, 6))
                };
                let id_term = id_tail(&|d| s_kk(d), 5);
                let symm = Expr::apps(
                    Expr::const_(Name::from_string("Eq.symm"), vec![level1()]),
                    [self.fuel_expr(), at(2, 5), s_kk(5), at(4, 5)],
                );
                let nd = Expr::apps(
                    Expr::const_(Name::from_string("Eq.ndrec"), vec![Level::zero(), level1()]),
                    [self.fuel_expr(), s_kk(5), q, id_term, at(2, 5), symm],
                );
                Expr::lam(BinderInfo::Default, a_prop.clone(), nd)
            };
            // inr: fun (h2 : le kk f) (e r) (h) =>
            //   succ_mono kk e r (ihw f h2 e r h).
            let inr = {
                // h2(4), e(5), r(6), h(7); body depth 8.
                let hyp =
                    eq_o(self.model_app(at(2, 7), at(5, 7)), Expr::app(self.done_expr(), at(6, 7)));
                let inner =
                    Expr::apps(at(1, 8), [at(2, 8), at(4, 8), at(5, 8), at(6, 8), at(7, 8)]);
                let body = Expr::apps(succ_mono.clone(), [at(0, 8), at(5, 8), at(6, 8), inner]);
                Expr::lam(
                    BinderInfo::Default,
                    b_prop.clone(),
                    Expr::lam(
                        BinderInfo::Default,
                        self.data_expr(),
                        Expr::lam(
                            BinderInfo::Default,
                            self.data_expr(),
                            Expr::lam(BinderInfo::Default, hyp, body),
                        ),
                    ),
                )
            };
            let _ = goal;
            let or_rec = Expr::apps(
                Expr::const_(Name::from_string("Or.rec"), Vec::new()),
                [a_prop, b_prop, or_motive, inl, inr, at(3, 4)],
            );
            Expr::lam(
                BinderInfo::Default,
                self.fuel_expr(),
                Expr::lam(
                    BinderInfo::Default,
                    ihw_ty,
                    Expr::lam(
                        BinderInfo::Default,
                        self.fuel_expr(),
                        Expr::lam(BinderInfo::Default, hle_ty, or_rec),
                    ),
                ),
            )
        };
        let rec = Expr::apps(
            Expr::const_(Name::from_string(&format!("{}.rec", self.fuel)), vec![Level::zero()]),
            [motive_m, base_m, step_m, Expr::bvar(0)],
        );
        Expr::lam(BinderInfo::Default, self.fuel_expr(), rec)
    }

    /// `le_refl : Pi n, le n n`.
    fn le_refl_term_and_type(&self) -> (Expr, Expr) {
        let ty = Expr::pi(
            BinderInfo::Default,
            self.fuel_expr(),
            self.le_app(Expr::bvar(0), Expr::bvar(0)),
        );
        let motive = Expr::lam(
            BinderInfo::Default,
            self.fuel_expr(),
            self.le_app(Expr::bvar(0), Expr::bvar(0)),
        );
        let base = self.refl_of(self.fuel_expr(), self.fuel_z_expr());
        // step: fun (kk) (ihk : le kk kk) => Or.inl (S kk = S kk) (le kk
        // (S kk)) (refl (S kk)).
        let step = {
            let s_kk = |d: usize| Expr::app(self.fuel_s_expr(), Expr::bvar((d - 1) as u32));
            let a_prop = self.eq_of(self.fuel_expr(), s_kk(2), s_kk(2));
            let b_prop = self.le_app(Expr::bvar(1), s_kk(2));
            let inl = Expr::apps(
                Expr::const_(Name::from_string("Or.inl"), Vec::new()),
                [a_prop, b_prop, self.refl_of(self.fuel_expr(), s_kk(2))],
            );
            Expr::lam(
                BinderInfo::Default,
                self.fuel_expr(),
                Expr::lam(BinderInfo::Default, self.le_app(Expr::bvar(0), Expr::bvar(0)), inl),
            )
        };
        let rec = Expr::apps(
            Expr::const_(Name::from_string(&format!("{}.rec", self.fuel)), vec![Level::zero()]),
            [motive, base, step, Expr::bvar(0)],
        );
        (Expr::lam(BinderInfo::Default, self.fuel_expr(), rec), ty)
    }

    /// `le_succ_self : Pi n, le (S n) n` (n <= S n in bound-first reading).
    fn le_succ_self_term_and_type(&self) -> (Expr, Expr) {
        let s_n = Expr::app(self.fuel_s_expr(), Expr::bvar(0));
        let ty = Expr::pi(
            BinderInfo::Default,
            self.fuel_expr(),
            self.le_app(s_n.clone(), Expr::bvar(0)),
        );
        let (le_refl, _) = self.le_refl_term_and_type();
        let a_prop = self.eq_of(self.fuel_expr(), Expr::bvar(0), s_n.clone());
        let b_prop = self.le_app(Expr::bvar(0), Expr::bvar(0));
        let inr = Expr::apps(
            Expr::const_(Name::from_string("Or.inr"), Vec::new()),
            [a_prop, b_prop, Expr::app(le_refl, Expr::bvar(0))],
        );
        (Expr::lam(BinderInfo::Default, self.fuel_expr(), inr), ty)
    }
}

// ---------------------------------------------------------------------------
// Mint / recheck / witnesses.
// ---------------------------------------------------------------------------

fn kernel_checks_goal(env: &Environment, term: &Expr, goal: &Expr) -> bool {
    TypeChecker::with_context(env, LocalContext::new()).check_type(term, goal).is_ok()
}

fn lineage_digest(
    domain: &str,
    term_bytes: &[u8],
    context_bytes: &[u8],
    label: &str,
    vc_sets: &[&[VerificationCondition]],
) -> Option<trust_ir::ProofDigest> {
    let mut hasher = Sha256::new();
    hasher.update(domain.as_bytes());
    for (tag, field) in [
        (b"term:".as_slice(), term_bytes),
        (b"ctx:".as_slice(), context_bytes),
        (b"label:".as_slice(), label.as_bytes()),
    ] {
        hasher.update(tag);
        hasher.update((field.len() as u64).to_le_bytes());
        hasher.update(field);
    }
    hasher.update((vc_sets.len() as u64).to_le_bytes());
    for vcs in vc_sets {
        let encoded = bincode::serialize(vcs).ok()?;
        hasher.update((encoded.len() as u64).to_le_bytes());
        hasher.update(encoded);
    }
    let digest = hasher.finalize();
    let mut bytes = [0u8; 32];
    bytes.copy_from_slice(&digest);
    Some(trust_ir::ProofDigest::sha256(bytes))
}

/// Mint a kernel-CHECKED `CleanCic` certificate discharging a fuel-outcome
/// bundle by the generated `Fuel.rec` induction (vacuous exhaustion base
/// witnessed through the kernel; Done-injectivity transports; tail arms = the
/// IH). Fail-closed on every count.
#[must_use]
pub fn certify_fuel_outcome_functional(
    vcs: &[VerificationCondition],
) -> Option<trust_ir::ProofEvidence> {
    let plan = parse_bundle(vcs)?;
    let env = plan.build_env()?;
    let goal = plan.goal()?;
    let proof = plan.proof()?;
    if !kernel_checks_goal(&env, &proof, &goal) {
        return None;
    }
    let term_bytes = serialize_term(&proof).ok()?;
    let context_bytes = crate::canonical_empty_context_bytes()?;
    let lineage =
        lineage_digest(OUTCOME_LINEAGE_DOMAIN, &term_bytes, &context_bytes, &plan.label, &[vcs])?;
    if !recheck_fuel_outcome_functional(vcs, &term_bytes, &context_bytes, &lineage) {
        return None;
    }
    Some(trust_ir::ProofEvidence::CleanCic {
        term: term_bytes,
        context: context_bytes,
        lineage,
        kernel_recheck: None,
    })
}

/// Consumer-side re-check.
#[must_use]
pub fn recheck_fuel_outcome_functional(
    vcs: &[VerificationCondition],
    term_bytes: &[u8],
    context_bytes: &[u8],
    lineage: &trust_ir::ProofDigest,
) -> bool {
    if !crate::is_canonical_empty_context(context_bytes) {
        return false;
    }
    let Some(plan) = parse_bundle(vcs) else {
        return false;
    };
    let Some(env) = plan.build_env() else {
        return false;
    };
    let Some(goal) = plan.goal() else {
        return false;
    };
    let Some(canonical_proof) = plan.proof() else {
        return false;
    };
    if !crate::is_canonical_term(term_bytes, &canonical_proof) {
        return false;
    }
    let Ok(term) = deserialize_term(term_bytes) else {
        return false;
    };
    if !kernel_checks_goal(&env, &term, &goal) {
        return false;
    }
    lineage_digest(OUTCOME_LINEAGE_DOMAIN, term_bytes, context_bytes, &plan.label, &[vcs]).as_ref()
        == Some(lineage)
}

/// LOAD-BEARING witness: the generated induction is ACCEPTED and the
/// refl-only pseudo-proof is REJECTED.
#[must_use]
pub fn fuel_outcome_induction_is_load_bearing(vcs: &[VerificationCondition]) -> bool {
    let Some(plan) = parse_bundle(vcs) else {
        return false;
    };
    let (Some(env), Some(goal), Some(proof), Some(pseudo)) =
        (plan.build_env(), plan.goal(), plan.proof(), plan.refl_only_pseudo_proof())
    else {
        return false;
    };
    kernel_checks_goal(&env, &proof, &goal) && !kernel_checks_goal(&env, &pseudo, &goal)
}

/// The item-2 LANE LEMMA witness: machine-build and kernel-check
/// fuel-monotonicity for the bundle's model —
/// `forall f' f, f <= f' -> forall e r, model f e = Done r ->
///  model f' e = Done r` — together with the `<=` reflexivity and
/// `n <= S n` witnesses (the bound predicate is not vacuous), and check the
/// DOWNWARD (false) statement REJECTED against the same proof term.
#[must_use]
pub fn fuel_monotonicity_is_machine_built(vcs: &[VerificationCondition]) -> bool {
    let Some(plan) = parse_bundle(vcs) else {
        return false;
    };
    let Some(mut env) = plan.build_env() else {
        return false;
    };
    if env.add_decl(plan.le_def()).is_err() {
        return false;
    }
    let (le_refl, le_refl_ty) = plan.le_refl_term_and_type();
    let (le_succ, le_succ_ty) = plan.le_succ_self_term_and_type();
    if !kernel_checks_goal(&env, &le_refl, &le_refl_ty)
        || !kernel_checks_goal(&env, &le_succ, &le_succ_ty)
    {
        return false;
    }
    let Some(succ_mono) = plan.succ_mono_term() else {
        return false;
    };
    // Register succ_mono as a checked definition (the mono term names it).
    if env
        .add_decl(Declaration::Definition {
            name: Name::from_string("__fo_succ_mono"),
            level_params: vec![],
            type_: plan.succ_mono_type(),
            value: succ_mono,
            is_reducible: true,
        })
        .is_err()
    {
        return false;
    }
    let mono = plan.mono_term();
    let up = plan.mono_type(false);
    let down = plan.mono_type(true);
    kernel_checks_goal(&env, &mono, &up) && !kernel_checks_goal(&env, &mono, &down)
}

// ---------------------------------------------------------------------------
// Item 3: the loop -> fuel-model SIMULATION discharge.
// ---------------------------------------------------------------------------

/// One parsed simulation equation.
#[derive(Debug, PartialEq, Eq)]
enum SimEq {
    Bail,
    Done { ctor: String, tree: DTree },
    Continue { ctor: String, field: usize },
}

/// The parsed + cross-checked simulation plan (everything else is validated
/// against the model bundle during parsing and not kept).
struct SimPlan {
    eqs: Vec<SimEq>,
    label: String,
}

fn parse_sim_marker(
    property: &str,
) -> Option<(String, String, String, String, String, String, String, usize, usize, usize)> {
    let marker = property.strip_prefix(SIM_CONCLUSION_PREFIX)?;
    let marker = marker.strip_prefix("[loop-fuel-sim:")?.strip_suffix(']')?;
    let mut lp = None;
    let mut model = None;
    let mut fuel = None;
    let mut out = None;
    let mut data = None;
    let mut dones = None;
    let mut continues = None;
    for field in marker.split(';') {
        let (key, value) = field.split_once('=')?;
        match key {
            "loop" => lp = Some(value.to_string()),
            "model" => model = Some(value.to_string()),
            "fuel" => {
                let (dt, _) = value.rsplit_once(':')?;
                fuel = Some(dt.to_string());
            }
            "out" => {
                let (rest, arity) = value.rsplit_once(':')?;
                let (dt, ctors) = rest.rsplit_once(':')?;
                let (done, exh) = ctors.split_once('|')?;
                out = Some((
                    dt.to_string(),
                    done.to_string(),
                    exh.to_string(),
                    arity.parse::<usize>().ok()?,
                ));
            }
            "data" => data = Some(value.to_string()),
            "bails" => {
                if value != "1" {
                    return None;
                }
            }
            "dones" => dones = value.parse().ok(),
            "continues" => continues = value.parse().ok(),
            _ => return None,
        }
    }
    let (out_full, done, exh, exh_arity) = out?;
    Some((lp?, model?, fuel?, out_full, data?, done, exh, exh_arity, dones?, continues?))
}

/// Parse the simulation VC set against the model's OUTCOME plan (the
/// cross-check half of the honest handoff).
#[allow(clippy::too_many_lines)]
fn parse_sim(vcs: &[VerificationCondition], model: &OutcomePlan) -> Option<SimPlan> {
    let mut conclusion: Option<&VerificationCondition> = None;
    let mut rows: Vec<(&str, &VerificationCondition)> = Vec::new();
    let mut properties: Vec<String> = Vec::new();
    for vc in vcs {
        let VcKind::FunctionalCorrectness { property, .. } = &vc.kind else {
            return None;
        };
        properties.push(property.clone());
        if property.starts_with(SIM_CONCLUSION_PREFIX) {
            if conclusion.replace(vc).is_some() {
                return None;
            }
        } else {
            rows.push((property.as_str(), vc));
        }
    }
    let conclusion = conclusion?;
    let VcKind::FunctionalCorrectness { property: c_prop, .. } = &conclusion.kind else {
        return None;
    };
    let (
        loop_name,
        model_name,
        fuel_full,
        out_full,
        data_full,
        done,
        exh,
        exh_arity,
        n_dones,
        n_continues,
    ) = parse_sim_marker(c_prop)?;
    // The handoff cross-checks: same model function, same datatypes, same
    // outcome classification as the INDUCTION bundle's plan.
    if model_name != model.member
        || fuel_full != model.fuel_full
        || out_full != model.out_full
        || data_full != model.data_full
        || done != model.done
        || exh != model.exh
        || exh_arity != model.exh_arity
        || loop_name == model_name
    {
        return None;
    }
    let is_model_app = |f: &Formula| -> Option<(Formula, Formula)> {
        let Formula::FnApp { func, args, .. } = f else {
            return None;
        };
        if func != &model_name {
            return None;
        }
        let [fuel_arg, payload_arg] = args.as_slice() else {
            return None;
        };
        Some((fuel_arg.clone(), payload_arg.clone()))
    };
    let mut eqs: Vec<SimEq> = Vec::new();
    let mut seen_bail = false;
    for (prop, vc) in rows {
        let (binders, body) = split_forall(&vc.formula);
        let Formula::Eq(lhs, rhs) = body else {
            return None;
        };
        let (fuel_arg, payload_arg) = is_model_app(lhs)?;
        if let Some(rest) = prop.strip_prefix(SIM_BAIL_PREFIX) {
            if rest != loop_name || seen_bail {
                return None;
            }
            let [(c, c_sort)] = binders.as_slice() else {
                return None;
            };
            if !is_datatype_sort(c_sort, &data_full) {
                return None;
            }
            let z_ok = matches!(&fuel_arg, Formula::Ctor { ctor, args, .. }
                if ctor == &model.fuel_z && args.is_empty());
            if !z_ok || payload_arg.var_name() != Some(c.as_str()) {
                return None;
            }
            let exh_ok = matches!(rhs.as_ref(), Formula::Ctor { ctor, args, .. }
                if ctor == &exh
                    && args.len() == exh_arity
                    && (exh_arity == 0 || args[0].var_name() == Some(c.as_str())));
            if !exh_ok {
                return None;
            }
            seen_bail = true;
            eqs.push(SimEq::Bail);
            continue;
        }
        let (rest, is_done) = if let Some(rest) = prop.strip_prefix(SIM_DONE_PREFIX) {
            (rest, true)
        } else if let Some(rest) = prop.strip_prefix(SIM_CONTINUE_PREFIX) {
            (rest, false)
        } else {
            return None;
        };
        let (lname, ctor) = rest.split_once("::")?;
        if lname != loop_name {
            return None;
        }
        let (_, arity) = model.ctors.iter().find(|(c, _)| c == ctor)?;
        // Binders: k then the ctor fields.
        let [(k, k_sort), fields @ ..] = binders.as_slice() else {
            return None;
        };
        if !is_datatype_sort(k_sort, &fuel_full) || fields.len() != *arity {
            return None;
        }
        for (_, s) in fields {
            if !is_datatype_sort(s, &data_full) {
                return None;
            }
        }
        let s_ok = matches!(&fuel_arg, Formula::Ctor { ctor, args, .. }
            if ctor == &model.fuel_s && args.len() == 1
                && args[0].var_name() == Some(k.as_str()));
        if !s_ok {
            return None;
        }
        let field_names: Vec<&str> = fields.iter().map(|(n, _)| n.as_str()).collect();
        let pattern_ok = matches!(&payload_arg, Formula::Ctor { ctor: pc, args: pa, .. }
            if pc == ctor && pa.len() == field_names.len()
                && pa.iter().zip(&field_names).all(|(a, f)| a.var_name() == Some(*f)));
        if !pattern_ok {
            return None;
        }
        if is_done {
            let Formula::Ctor { ctor: rc, args: ra, .. } = rhs.as_ref() else {
                return None;
            };
            if rc != &done || ra.len() != 1 {
                return None;
            }
            let tree = parse_dtree(&ra[0], &field_names, &model.ctors)?;
            eqs.push(SimEq::Done { ctor: ctor.to_string(), tree });
        } else {
            let (rf, rp) = is_model_app(rhs)?;
            if rf.var_name() != Some(k.as_str()) {
                return None;
            }
            let field = field_names.iter().position(|f| Some(*f) == rp.var_name())?;
            eqs.push(SimEq::Continue { ctor: ctor.to_string(), field });
        }
    }
    if !seen_bail {
        return None;
    }
    // The conclusion's And carries exactly the row formulas.
    let Formula::And(conjuncts) = &conclusion.formula else {
        return None;
    };
    if conjuncts.len() != eqs.len() {
        return None;
    }
    // Census + ARM-BY-ARM cross-check against the model bundle.
    let dones = eqs.iter().filter(|e| matches!(e, SimEq::Done { .. })).count();
    let continues = eqs.iter().filter(|e| matches!(e, SimEq::Continue { .. })).count();
    if dones != n_dones || continues != n_continues || dones + continues != model.ctors.len() {
        return None;
    }
    for (ctor, _) in &model.ctors {
        let arm = &model.arms[model.ctors.iter().position(|(c, _)| c == ctor)?];
        let sim = eqs.iter().find(|e| match e {
            SimEq::Done { ctor: c, .. } | SimEq::Continue { ctor: c, .. } => c == ctor,
            SimEq::Bail => false,
        })?;
        let matches_arm = match (arm, sim) {
            (OArm::Done(t1), SimEq::Done { tree, .. }) => t1 == tree,
            (OArm::Tail { field }, SimEq::Continue { field: f, .. }) => field == f,
            _ => false,
        };
        if !matches_arm {
            return None;
        }
    }
    let label = format!(
        "loop_fuel_sim:{loop_name}->{model_name}:[{}]:{:?}",
        properties.join(";"),
        conclusion.formula
    );
    Some(SimPlan { eqs, label })
}

impl OutcomePlan {
    /// The CIC statement of one simulation equation (closed).
    fn sim_eq_prop(&self, eq: &SimEq) -> Option<Expr> {
        match eq {
            SimEq::Bail => {
                // Pi (c : E), Eq O (model Z c) Exh[(c)].
                let body = self.eq_of(
                    self.out_expr(),
                    self.model_app(self.fuel_z_expr(), Expr::bvar(0)),
                    self.exh_val(Some(Expr::bvar(0))),
                );
                Some(Expr::pi(BinderInfo::Default, self.data_expr(), body))
            }
            SimEq::Done { ctor, tree } => {
                let (_, arity) = self.ctors.iter().find(|(c, _)| c == ctor)?;
                let a = *arity;
                // Pi (k) (fields), Eq O (model (S k) C(f)) (Done tree).
                let depth = 1 + a;
                let field = |p: usize| Expr::bvar((depth - 1 - (1 + p)) as u32);
                let mut pattern = self.e_ctor(ctor)?;
                for p in 0..a {
                    pattern = Expr::app(pattern, field(p));
                }
                let s_k = Expr::app(self.fuel_s_expr(), Expr::bvar((depth - 1) as u32));
                let body = self.eq_of(
                    self.out_expr(),
                    self.model_app(s_k, pattern),
                    Expr::app(self.done_expr(), self.dtree_expr(tree, &field)?),
                );
                let mut prop = body;
                for _ in 0..a {
                    prop = Expr::pi(BinderInfo::Default, self.data_expr(), prop);
                }
                Some(Expr::pi(BinderInfo::Default, self.fuel_expr(), prop))
            }
            SimEq::Continue { ctor, field: f } => {
                let (_, arity) = self.ctors.iter().find(|(c, _)| c == ctor)?;
                let a = *arity;
                let depth = 1 + a;
                let field = |p: usize| Expr::bvar((depth - 1 - (1 + p)) as u32);
                let mut pattern = self.e_ctor(ctor)?;
                for p in 0..a {
                    pattern = Expr::app(pattern, field(p));
                }
                let k = Expr::bvar((depth - 1) as u32);
                let s_k = Expr::app(self.fuel_s_expr(), k.clone());
                let body = self.eq_of(
                    self.out_expr(),
                    self.model_app(s_k, pattern),
                    self.model_app(k, field(*f)),
                );
                let mut prop = body;
                for _ in 0..a {
                    prop = Expr::pi(BinderInfo::Default, self.data_expr(), prop);
                }
                Some(Expr::pi(BinderInfo::Default, self.fuel_expr(), prop))
            }
        }
    }

    /// The DEFINITIONAL proof of one simulation equation: the lambda-wrapped
    /// `Eq.refl` at the model's own reduct (each loop path is one iota step
    /// of the fold).
    fn sim_eq_proof(&self, eq: &SimEq) -> Option<Expr> {
        match eq {
            SimEq::Bail => Some(Expr::lam(
                BinderInfo::Default,
                self.data_expr(),
                self.refl_of(self.out_expr(), self.model_app(self.fuel_z_expr(), Expr::bvar(0))),
            )),
            SimEq::Done { ctor, .. } | SimEq::Continue { ctor, .. } => {
                let (_, arity) = self.ctors.iter().find(|(c, _)| c == ctor)?;
                let a = *arity;
                let depth = 1 + a;
                let field = |p: usize| Expr::bvar((depth - 1 - (1 + p)) as u32);
                let mut pattern = self.e_ctor(ctor)?;
                for p in 0..a {
                    pattern = Expr::app(pattern, field(p));
                }
                let s_k = Expr::app(self.fuel_s_expr(), Expr::bvar((depth - 1) as u32));
                let mut proof = self.refl_of(self.out_expr(), self.model_app(s_k, pattern));
                for _ in 0..a {
                    proof = Expr::lam(BinderInfo::Default, self.data_expr(), proof);
                }
                Some(Expr::lam(BinderInfo::Default, self.fuel_expr(), proof))
            }
        }
    }
}

/// Right-nested And-chain helpers (free functions — shared by the sim mint).
fn and_chain(props: &[Expr]) -> Expr {
    let and_const = Expr::const_(Name::from_string("And"), Vec::new());
    let mut iter = props.iter().rev();
    let mut acc = iter.next().expect("and_chain over >= 1 props").clone();
    for p in iter {
        acc = Expr::apps(and_const.clone(), [p.clone(), acc]);
    }
    acc
}

fn intro_chain(props: &[Expr], proofs: &[Expr]) -> Expr {
    debug_assert_eq!(props.len(), proofs.len());
    if props.len() == 1 {
        return proofs[0].clone();
    }
    let rest_prop = and_chain(&props[1..]);
    let rest_proof = intro_chain(&props[1..], &proofs[1..]);
    Expr::apps(
        Expr::const_(Name::from_string("And.intro"), Vec::new()),
        [props[0].clone(), rest_prop, proofs[0].clone(), rest_proof],
    )
}

/// Mint a kernel-CHECKED certificate for the loop -> fuel-model SIMULATION:
/// cross-check the sim equations against the model's own induction bundle
/// (`bundle_vcs`), rebuild the SAME model, and kernel-check the conjunction of
/// all per-path equations discharged definitionally. Fail-closed on any
/// mismatch — a loop path that does not simulate one model unfold never
/// certifies.
#[must_use]
pub fn certify_loop_fuel_sim(
    sim_vcs: &[VerificationCondition],
    bundle_vcs: &[VerificationCondition],
) -> Option<trust_ir::ProofEvidence> {
    let plan = parse_bundle(bundle_vcs)?;
    let sim = parse_sim(sim_vcs, &plan)?;
    let env = plan.build_env()?;
    let props = sim.eqs.iter().map(|e| plan.sim_eq_prop(e)).collect::<Option<Vec<_>>>()?;
    let proofs = sim.eqs.iter().map(|e| plan.sim_eq_proof(e)).collect::<Option<Vec<_>>>()?;
    let goal = and_chain(&props);
    let proof = intro_chain(&props, &proofs);
    if !kernel_checks_goal(&env, &proof, &goal) {
        return None;
    }
    let term_bytes = serialize_term(&proof).ok()?;
    let context_bytes = crate::canonical_empty_context_bytes()?;
    let lineage = lineage_digest(
        LOOP_SIM_LINEAGE_DOMAIN,
        &term_bytes,
        &context_bytes,
        &sim.label,
        &[sim_vcs, bundle_vcs],
    )?;
    if !recheck_loop_fuel_sim(sim_vcs, bundle_vcs, &term_bytes, &context_bytes, &lineage) {
        return None;
    }
    Some(trust_ir::ProofEvidence::CleanCic {
        term: term_bytes,
        context: context_bytes,
        lineage,
        kernel_recheck: None,
    })
}

/// Consumer-side re-check of the simulation certificate.
#[must_use]
pub fn recheck_loop_fuel_sim(
    sim_vcs: &[VerificationCondition],
    bundle_vcs: &[VerificationCondition],
    term_bytes: &[u8],
    context_bytes: &[u8],
    lineage: &trust_ir::ProofDigest,
) -> bool {
    if !crate::is_canonical_empty_context(context_bytes) {
        return false;
    }
    let Some(plan) = parse_bundle(bundle_vcs) else {
        return false;
    };
    let Some(sim) = parse_sim(sim_vcs, &plan) else {
        return false;
    };
    let Some(env) = plan.build_env() else {
        return false;
    };
    let Some(props) = sim.eqs.iter().map(|e| plan.sim_eq_prop(e)).collect::<Option<Vec<_>>>()
    else {
        return false;
    };
    let goal = and_chain(&props);
    let Some(proofs) = sim.eqs.iter().map(|e| plan.sim_eq_proof(e)).collect::<Option<Vec<_>>>()
    else {
        return false;
    };
    let canonical_proof = intro_chain(&props, &proofs);
    if !crate::is_canonical_term(term_bytes, &canonical_proof) {
        return false;
    }
    let Ok(term) = deserialize_term(term_bytes) else {
        return false;
    };
    if !kernel_checks_goal(&env, &term, &goal) {
        return false;
    }
    lineage_digest(
        LOOP_SIM_LINEAGE_DOMAIN,
        term_bytes,
        context_bytes,
        &sim.label,
        &[sim_vcs, bundle_vcs],
    )
    .as_ref()
        == Some(lineage)
}

#[cfg(test)]
mod tests {
    use super::*;

    // Hand-built bundles in the exact emitted shape of the PEELER fixture
    // (`peel_model : Fuel -> E -> O`, E = A | B(E), O = Done(E) | Exh(E)); the
    // integration e2e drives the literal trust-vcgen output.

    fn fuel_sort() -> Sort {
        Sort::Datatype { name: "fuel::Fuel".to_string(), constructors: vec![] }
    }

    fn e_sort() -> Sort {
        Sort::Datatype { name: "expr::E".to_string(), constructors: vec![] }
    }

    fn o_sort() -> Sort {
        Sort::Datatype { name: "outcome::O".to_string(), constructors: vec![] }
    }

    fn var(name: &str, sort: Sort) -> Formula {
        Formula::var_owned(name.to_string(), sort)
    }

    fn e_ctor(name: &str, args: Vec<Formula>) -> Formula {
        Formula::Ctor { ctor: name.to_string(), args, sort: e_sort() }
    }

    fn fuel_ctor(name: &str, args: Vec<Formula>) -> Formula {
        Formula::Ctor { ctor: name.to_string(), args, sort: fuel_sort() }
    }

    fn o_ctor(name: &str, args: Vec<Formula>) -> Formula {
        Formula::Ctor { ctor: name.to_string(), args, sort: o_sort() }
    }

    fn vc(property: &str, context: &str, formula: Formula) -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::FunctionalCorrectness {
                property: property.to_string(),
                context: context.to_string(),
            },
            function: context.into(),
            location: trust_types::SourceSpan::default(),
            formula,
            contract_metadata: None,
            obligation: None,
        }
    }

    /// The Done-conditional post `forall r, _0 = Done r -> r = <rhs>` with
    /// `_0` instantiated to `value`.
    fn done_cond_inst(value: Formula, rhs: Formula) -> Formula {
        Formula::forall(
            &[("r", e_sort())],
            Formula::Implies(
                Box::new(Formula::Eq(
                    Box::new(value),
                    Box::new(o_ctor("Done", vec![var("r", e_sort())])),
                )),
                Box::new(Formula::Eq(Box::new(var("r", e_sort())), Box::new(rhs))),
            ),
        )
    }

    /// The TRUE bundle (`post: Done r -> r = A`). `rhs_of_r` swaps the
    /// conclusion's rhs (B(A) = the FALSE variant).
    fn bundle_with(rhs_of_r: Formula) -> Vec<VerificationCondition> {
        let m = "peel_model";
        let post_at = |v: Formula| done_cond_inst(v, rhs_of_r.clone());
        let base =
            Formula::forall(&[("e", e_sort())], post_at(o_ctor("Exh", vec![var("e", e_sort())])));
        let case_a = Formula::forall(
            &[("__fld_S_0", fuel_sort())],
            post_at(o_ctor("Done", vec![e_ctor("A", vec![])])),
        );
        let ih_inst = post_at(var("__ih0", o_sort()));
        let case_b = Formula::forall(
            &[("__fld_S_0", fuel_sort()), ("__fld_B_0", e_sort()), ("__ih0", o_sort())],
            Formula::Implies(Box::new(ih_inst.clone()), Box::new(ih_inst)),
        );
        let conclusion = Formula::forall(
            &[("fuel", fuel_sort()), ("e", e_sort())],
            done_cond_inst(var("_0", o_sort()), rhs_of_r.clone()),
        );
        vec![
            vc(&format!("{BASE_PROPERTY_PREFIX}{m}"), m, base),
            vc(&format!("{CASE_PROPERTY_PREFIX}{m}::A[calls=]"), m, case_a),
            vc(&format!("{CASE_PROPERTY_PREFIX}{m}::B[calls={m}:0]"), m, case_b),
            vc(
                &format!(
                    "{CONCLUSION_PROPERTY_PREFIX}[fuel-outcome-induction:fuel=fuel::Fuel:Z|S;\
                     out=outcome::O:Done|Exh:1;data=expr::E;member={m};bases=1;cases=2]"
                ),
                m,
                conclusion,
            ),
        ]
    }

    fn true_bundle() -> Vec<VerificationCondition> {
        bundle_with(e_ctor("A", vec![]))
    }

    /// The Exhausted-only NEGATIVE control: unconditional `_0 = Exh(A)`.
    fn exhausted_only_bundle() -> Vec<VerificationCondition> {
        let m = "peel_model";
        let ground = || o_ctor("Exh", vec![e_ctor("A", vec![])]);
        let post_at = |v: Formula| Formula::Eq(Box::new(v), Box::new(ground()));
        let base =
            Formula::forall(&[("e", e_sort())], post_at(o_ctor("Exh", vec![var("e", e_sort())])));
        let case_a = Formula::forall(
            &[("__fld_S_0", fuel_sort())],
            post_at(o_ctor("Done", vec![e_ctor("A", vec![])])),
        );
        let ih_inst = post_at(var("__ih0", o_sort()));
        let case_b = Formula::forall(
            &[("__fld_S_0", fuel_sort()), ("__fld_B_0", e_sort()), ("__ih0", o_sort())],
            Formula::Implies(Box::new(ih_inst.clone()), Box::new(ih_inst)),
        );
        let conclusion = Formula::forall(
            &[("fuel", fuel_sort()), ("e", e_sort())],
            post_at(var("_0", o_sort())),
        );
        vec![
            vc(&format!("{BASE_PROPERTY_PREFIX}{m}"), m, base),
            vc(&format!("{CASE_PROPERTY_PREFIX}{m}::A[calls=]"), m, case_a),
            vc(&format!("{CASE_PROPERTY_PREFIX}{m}::B[calls={m}:0]"), m, case_b),
            vc(
                &format!(
                    "{CONCLUSION_PROPERTY_PREFIX}[fuel-outcome-induction:fuel=fuel::Fuel:Z|S;\
                     out=outcome::O:Done|Exh:1;data=expr::E;member={m};bases=1;cases=2]"
                ),
                m,
                conclusion,
            ),
        ]
    }

    fn sim_vcs() -> Vec<VerificationCondition> {
        let l = "peel_loop";
        let m = "peel_model";
        let app = |fuel: Formula, e: Formula| Formula::FnApp {
            func: m.to_string(),
            args: vec![fuel, e],
            sort: o_sort(),
        };
        let bail = Formula::forall(
            &[("__c", e_sort())],
            Formula::Eq(
                Box::new(app(fuel_ctor("Z", vec![]), var("__c", e_sort()))),
                Box::new(o_ctor("Exh", vec![var("__c", e_sort())])),
            ),
        );
        let s_k = || fuel_ctor("S", vec![var("__k", fuel_sort())]);
        let done_a = Formula::forall(
            &[("__k", fuel_sort())],
            Formula::Eq(
                Box::new(app(s_k(), e_ctor("A", vec![]))),
                Box::new(o_ctor("Done", vec![e_ctor("A", vec![])])),
            ),
        );
        let cont_b = Formula::forall(
            &[("__k", fuel_sort()), ("__fld_B_0", e_sort())],
            Formula::Eq(
                Box::new(app(s_k(), e_ctor("B", vec![var("__fld_B_0", e_sort())]))),
                Box::new(app(var("__k", fuel_sort()), var("__fld_B_0", e_sort()))),
            ),
        );
        vec![
            vc(&format!("{SIM_BAIL_PREFIX}{l}"), l, bail.clone()),
            vc(&format!("{SIM_DONE_PREFIX}{l}::A"), l, done_a.clone()),
            vc(&format!("{SIM_CONTINUE_PREFIX}{l}::B"), l, cont_b.clone()),
            vc(
                &format!(
                    "{SIM_CONCLUSION_PREFIX}[loop-fuel-sim:loop={l};model={m};\
                     fuel=fuel::Fuel:Z|S;out=outcome::O:Done|Exh:1;data=expr::E;\
                     bails=1;dones=1;continues=1]"
                ),
                l,
                Formula::And(vec![bail, done_a, cont_b]),
            ),
        ]
    }

    #[test]
    fn test_true_bundle_certifies() {
        let vcs = true_bundle();
        let evidence = certify_fuel_outcome_functional(&vcs)
            .expect("the Done-conditional peeler bundle must certify");
        let trust_ir::ProofEvidence::CleanCic { term, context, lineage, .. } = &evidence else {
            panic!("expected CleanCic evidence");
        };
        assert!(recheck_fuel_outcome_functional(&vcs, term, context, lineage));
    }

    #[test]
    fn test_induction_is_load_bearing() {
        assert!(fuel_outcome_induction_is_load_bearing(&true_bundle()));
    }

    #[test]
    fn test_exhausted_only_post_is_kernel_rejected() {
        assert!(
            certify_fuel_outcome_functional(&exhausted_only_bundle()).is_none(),
            "a postcondition that holds only on the Exhausted arm must NOT certify \
             unconditionally — the complete arm's Done value refutes it in the kernel"
        );
    }

    #[test]
    fn test_false_done_conditional_is_kernel_rejected() {
        let wrong = bundle_with(e_ctor("B", vec![e_ctor("A", vec![])]));
        assert!(
            certify_fuel_outcome_functional(&wrong).is_none(),
            "Done r -> r = B(A) is false at the complete arm; the transport base \
             must be kernel-rejected"
        );
    }

    #[test]
    fn test_fuel_monotonicity_is_machine_built() {
        assert!(
            fuel_monotonicity_is_machine_built(&true_bundle()),
            "Done at f must transport to every f' >= f, and the downward statement \
             must be rejected"
        );
    }

    #[test]
    fn test_loop_sim_certifies_and_recheck() {
        let bundle = true_bundle();
        let sim = sim_vcs();
        let evidence = certify_loop_fuel_sim(&sim, &bundle)
            .expect("the per-iteration simulation equations are definitional for the model");
        let trust_ir::ProofEvidence::CleanCic { term, context, lineage, .. } = &evidence else {
            panic!("expected CleanCic evidence");
        };
        assert!(recheck_loop_fuel_sim(&sim, &bundle, term, context, lineage));
    }

    #[test]
    fn both_public_recheck_lanes_reject_relineaged_ambient_sorry_and_noncanonical_bytes() {
        let bundle = true_bundle();
        let plan = parse_bundle(&bundle).expect("bundle parses");
        let env = plan.build_env().expect("minimal env");
        let outcome_goal = plan.goal().expect("outcome goal");
        let outcome_proof = plan.proof().expect("outcome proof");
        let context = crate::canonical_empty_context_bytes().expect("canonical context");

        let mut ambient = env.clone();
        let sorry = crate::install_adversarial_trust_marker(&mut ambient, &outcome_goal)
            .expect("install adversarial trusted marker");
        assert!(kernel_checks_goal(&ambient, &sorry, &outcome_goal));
        let sorry_bytes = serialize_term(&sorry).expect("serialize sorry");
        let sorry_lineage =
            lineage_digest(OUTCOME_LINEAGE_DOMAIN, &sorry_bytes, &context, &plan.label, &[&bundle])
                .expect("lineage");
        assert!(!recheck_fuel_outcome_functional(&bundle, &sorry_bytes, &context, &sorry_lineage,));

        let beta = Expr::app(
            Expr::lam(BinderInfo::Default, outcome_goal.clone(), Expr::bvar(0)),
            outcome_proof.clone(),
        );
        assert!(kernel_checks_goal(&env, &beta, &outcome_goal));
        let beta_bytes = serialize_term(&beta).expect("serialize beta proof");
        let beta_lineage =
            lineage_digest(OUTCOME_LINEAGE_DOMAIN, &beta_bytes, &context, &plan.label, &[&bundle])
                .expect("lineage");
        assert!(!recheck_fuel_outcome_functional(&bundle, &beta_bytes, &context, &beta_lineage,));

        let outcome_bytes = serialize_term(&outcome_proof).expect("canonical proof");
        let mut noncanonical_context = context.clone();
        noncanonical_context.push(0);
        let relined = lineage_digest(
            OUTCOME_LINEAGE_DOMAIN,
            &outcome_bytes,
            &noncanonical_context,
            &plan.label,
            &[&bundle],
        )
        .expect("lineage");
        assert!(!recheck_fuel_outcome_functional(
            &bundle,
            &outcome_bytes,
            &noncanonical_context,
            &relined,
        ));

        let mut changed_bundle = bundle.clone();
        changed_bundle[0].location.file = "different_source.rs".to_string();
        assert!(parse_bundle(&changed_bundle).is_some());
        let honest_lineage = lineage_digest(
            OUTCOME_LINEAGE_DOMAIN,
            &outcome_bytes,
            &context,
            &plan.label,
            &[&bundle],
        )
        .expect("lineage");
        assert!(!recheck_fuel_outcome_functional(
            &changed_bundle,
            &outcome_bytes,
            &context,
            &honest_lineage,
        ));

        let sim_vcs = sim_vcs();
        let sim = parse_sim(&sim_vcs, &plan).expect("simulation parses");
        let props = sim
            .eqs
            .iter()
            .map(|e| plan.sim_eq_prop(e))
            .collect::<Option<Vec<_>>>()
            .expect("simulation propositions");
        let proofs = sim
            .eqs
            .iter()
            .map(|e| plan.sim_eq_proof(e))
            .collect::<Option<Vec<_>>>()
            .expect("simulation proofs");
        let sim_goal = and_chain(&props);
        let sim_proof = intro_chain(&props, &proofs);
        // The sim-half adversarial proof is built SELF-CONTAINED, exactly as the
        // outcome half above: install a goal-specific admitted marker (an ambient
        // trust defect) whose type IS `sim_goal`, so it genuinely kernel-checks
        // (the non-vacuity precondition that makes the recheck rejection below
        // meaningful) WITHOUT depending on a polymorphic `sorry` in the ambient
        // env — the minimal recheck env deliberately carries no trust markers
        // (`build_env` uses `Environment::default()`, which does not `init_sorry`;
        // an ambient `sorry` is a sealed authority defect this lane must reject).
        // A fresh clone avoids a name collision with the outcome-goal marker.
        let mut sim_ambient = env.clone();
        let sim_sorry = crate::install_adversarial_trust_marker(&mut sim_ambient, &sim_goal)
            .expect("install adversarial sim marker");
        assert!(kernel_checks_goal(&sim_ambient, &sim_sorry, &sim_goal));
        let sim_sorry_bytes = serialize_term(&sim_sorry).expect("serialize sorry");
        let sim_sorry_lineage = lineage_digest(
            LOOP_SIM_LINEAGE_DOMAIN,
            &sim_sorry_bytes,
            &context,
            &sim.label,
            &[&sim_vcs, &bundle],
        )
        .expect("lineage");
        assert!(!recheck_loop_fuel_sim(
            &sim_vcs,
            &bundle,
            &sim_sorry_bytes,
            &context,
            &sim_sorry_lineage,
        ));

        let sim_beta =
            Expr::app(Expr::lam(BinderInfo::Default, sim_goal.clone(), Expr::bvar(0)), sim_proof);
        assert!(kernel_checks_goal(&env, &sim_beta, &sim_goal));
        let sim_beta_bytes = serialize_term(&sim_beta).expect("serialize beta proof");
        let sim_beta_lineage = lineage_digest(
            LOOP_SIM_LINEAGE_DOMAIN,
            &sim_beta_bytes,
            &context,
            &sim.label,
            &[&sim_vcs, &bundle],
        )
        .expect("lineage");
        assert!(!recheck_loop_fuel_sim(
            &sim_vcs,
            &bundle,
            &sim_beta_bytes,
            &context,
            &sim_beta_lineage,
        ));
    }

    #[test]
    fn test_loop_sim_wrong_continue_fails_closed() {
        // The continue equation goes to the WRONG next state (B(x) instead of
        // x): the cross-check against the model bundle fails closed.
        let bundle = true_bundle();
        let mut sim = sim_vcs();
        let wrong = Formula::forall(
            &[("__k", fuel_sort()), ("__fld_B_0", e_sort())],
            Formula::Eq(
                Box::new(Formula::FnApp {
                    func: "peel_model".to_string(),
                    args: vec![
                        fuel_ctor("S", vec![var("__k", fuel_sort())]),
                        e_ctor("B", vec![var("__fld_B_0", e_sort())]),
                    ],
                    sort: o_sort(),
                }),
                Box::new(Formula::FnApp {
                    func: "peel_model".to_string(),
                    args: vec![
                        var("__k", fuel_sort()),
                        e_ctor("B", vec![var("__fld_B_0", e_sort())]),
                    ],
                    sort: o_sort(),
                }),
            ),
        );
        sim[2].formula = wrong.clone();
        if let VcKind::FunctionalCorrectness { .. } = &sim[3].kind {
            sim[3].formula =
                Formula::And(vec![sim[0].formula.clone(), sim[1].formula.clone(), wrong]);
        }
        assert!(certify_loop_fuel_sim(&sim, &bundle).is_none());
    }

    #[test]
    fn test_missing_case_fails_closed() {
        let mut vcs = true_bundle();
        vcs.remove(1);
        assert!(certify_fuel_outcome_functional(&vcs).is_none());
    }
}
