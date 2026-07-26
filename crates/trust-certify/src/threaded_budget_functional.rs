// trust-certify: STATE-THREADED numeric-budget induction discharge lane —
// SN-vs-fuel RESOLUTION item 1 (the adopted partial-correctness-via-fuel
// design, assessment framing: the real kernel cluster is budget-mediated by a
// state-threaded heartbeat counter, not by the mutual lane's each-at-k
// structural fuel).
//
// THIS lane consumes the bundle trust-vcgen's `threaded_budget_functional`
// lane emits for a threaded 2+-member cluster (`(&Fuel, &E) -> Res` with
// `Res = Mk(Fuel, E)`, per-entry decrement, remainder passed to every later
// callee, model-vs-reference postconditions) and machine-builds the JOINT
// kernel discharge.
//
// THE DISCHARGE DESIGN (the "minimal sound shape" the design item asks for —
// the MAJORANT fold):
//
// The threaded members are NOT structurally recursive in their own fuel: the
// second call of an arm runs at `(first call's remainder)`, a COMPUTED value,
// not the structural predecessor. The fold therefore generalizes: the models
// record's fields become FUEL-TAKING functions
//
//   __ThModels := { field_i : Fuel -> E -> Res }          (one per member)
//   __th_cluster : Fuel -> __ThModels                     (ONE Fuel.rec fold)
//     cluster Z     = { fun m e => Mk m e }               (exhaustion sheet)
//     cluster (S K) = { fun m e => match m with
//         | Z   => Mk Z e                                 (pinned exhaustion)
//         | S j => <arm: calls THROUGH cluster K at the THREADED fuels —
//                   call 0 at j, call p at (call p-1's remainder)> }
//   __th_model_i : Fuel -> E -> Res := fun n e => proj_i (cluster n) n e
//
// The first index (the fold argument) is a structural MAJORANT; the second is
// the live threaded budget. Every guarded entry decrements at least once, so
// every fuel value a callee ever receives is < the caller's — which keeps all
// calls inside the majorant's structural predecessor `cluster K`. That is
// exactly why plain `Fuel.rec` suffices and NO `Acc` is needed: the strict
// decrease is carried by the MAJORANT, while the IH is stated over ALL
// threaded fuels
//
//   motive Q(w) := And_i (forall (m : Fuel) (e : E),
//                     proj_i (Mcluster w) m e = proj_i (Rcluster w) m e)
//
// — "the IH applies at any smaller fuel" holds because the inner quantifier
// is UNBOUNDED: the step leg instantiates it at the dynamic remainders
// (`(gr k x).0`), which no per-level motive could reach. No `<=` relation and
// no bounded-monotonicity side lemma are needed for the model=reference
// discharge; the majorant quantifier absorbs both. The goal
// `forall n, And_i (forall e, model_i n e = ref_i n e)` is the motive's
// diagonal (`m := n`).
//
// NO MASQUERADE (kernel-witnessed):
//   * the refl-only pseudo-proof (no induction) is REJECTED while the
//     generated majorant induction is ACCEPTED
//     (`threaded_induction_is_load_bearing`);
//   * a reference whose arm disagrees with the model's (e.g. a call-free
//     B-arm returning the un-spent budget) parses, builds, and the kernel
//     REJECTS the joint proof — no certificate;
//   * the remainder-threading gates (call 0 at `k`, call p at call p-1's
//     remainder, returned remainder = the last call's) are parse-enforced;
//     an each-at-k bundle is not a threaded bundle.
//
// SOUNDNESS (fail-closed, never a false `Certified`): evidence is minted ONLY
// when the clean kernel certifies `proof : goal` (`infer_only = false`), env =
// `init_eq` + `init_and` + the reconstructed inductives + the two fold
// definitions (no smuggled axioms), closed context; term + context + label
// digest-bound; the deserialized payload independently re-checked; every
// unsupported shape returns `None`.
//
// HONEST SCOPE: fixture-grade. This certifies the reconstructed kernel model
// represented by the supplied typed VC bundle; absent a separate
// extraction/provenance bridge, it does NOT prove that bundle came from a
// literal Rust/TrustIR cluster. The LITERAL kernel-cluster application still
// needs the non-SN extraction gaps (interior mutability of the heartbeat
// `Cell`, `Rc` sharing, generics) — named residuals, out of scope here.
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

/// Lineage domain tag — distinct from every sibling lane.
const THREADED_LINEAGE_DOMAIN: &str = "trust-certify.cleancic.threaded-budget-functional.v2";

const BASE_PROPERTY_PREFIX: &str = "threaded_budget_functional_base::";
const CASE_PROPERTY_PREFIX: &str = "threaded_budget_functional_case::";
const CONCLUSION_PROPERTY_PREFIX: &str = "threaded_budget_functional_conclusion";
const REF_BASE_PROPERTY_PREFIX: &str = "threaded_budget_functional_refbase::";
const REF_STEP_PROPERTY_PREFIX: &str = "threaded_budget_functional_refstep::";

// ---------------------------------------------------------------------------
// Bundle parsing.
// ---------------------------------------------------------------------------

/// A parsed PAYLOAD result tree. Leaves are pattern fields or the payload
/// component of a call's result pair.
#[derive(Clone, Debug, PartialEq, Eq)]
enum TTree {
    Field(usize),
    /// `<call p>.1`.
    CallSnd(usize),
    Node {
        ctor: String,
        args: Vec<TTree>,
    },
}

/// The arm's returned REMAINDER.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum RemSrc {
    /// The decremented entry budget `k` (call-free arms).
    K,
    /// `<call p>.0` — pinned to the LAST call.
    CallFst(usize),
}

/// One parsed step arm (member or reference; the same shape).
#[derive(Debug, PartialEq, Eq)]
struct TArm {
    /// Callee indices (into the member list for member arms, the reference
    /// list for reference arms) and the recursed-on field, per call in
    /// threading order.
    calls: Vec<(usize, usize)>,
    rem: RemSrc,
    tree: TTree,
}

/// The parsed threaded plan.
struct ThreadedPlan {
    fuel: String,
    fuel_z: String,
    fuel_s: String,
    res: String,
    res_mk: String,
    data: String,
    /// Payload constructors `(name, arity)` in case order (all fields
    /// recursive payload fields).
    ctors: Vec<(String, usize)>,
    /// Member step arms, per member, in ctor order.
    members: Vec<Vec<TArm>>,
    /// member index -> reference index (from the conclusion conjuncts).
    member_ref: Vec<usize>,
    /// Reference step arms, per reference, in ctor order.
    refs: Vec<Vec<TArm>>,
    label: String,
}

struct Marker {
    fuel_full: String,
    fuel_z: String,
    fuel_s: String,
    res_full: String,
    res_mk: String,
    data_full: String,
    member_names: Vec<String>,
    bases: usize,
    cases: usize,
    refs: Vec<String>,
    refbases: usize,
    refcases: usize,
}

fn parse_marker(property: &str) -> Option<Marker> {
    let marker = property.strip_prefix(CONCLUSION_PROPERTY_PREFIX)?;
    let marker = marker.strip_prefix("[threaded-induction:")?.strip_suffix(']')?;
    let mut fuel = None;
    let mut res = None;
    let mut data = None;
    let mut member_names = None;
    let mut bases = None;
    let mut cases = None;
    let mut refs = None;
    let mut refbases = None;
    let mut refcases = None;
    for field in marker.split(';') {
        let (key, value) = field.split_once('=')?;
        match key {
            "fuel" => {
                let (dt, ctors) = value.rsplit_once(':')?;
                let (z, s) = ctors.split_once('|')?;
                fuel = Some((dt.to_string(), z.to_string(), s.to_string()));
            }
            "res" => {
                let (dt, mk) = value.rsplit_once(':')?;
                res = Some((dt.to_string(), mk.to_string()));
            }
            "data" => data = Some(value.to_string()),
            "members" => {
                member_names = Some(value.split(',').map(str::to_string).collect::<Vec<_>>());
            }
            "bases" => bases = value.parse().ok(),
            "cases" => cases = value.parse().ok(),
            "refs" => refs = Some(value.split(',').map(str::to_string).collect::<Vec<_>>()),
            "refbases" => refbases = value.parse().ok(),
            "refcases" => refcases = value.parse().ok(),
            _ => return None,
        }
    }
    let (fuel_full, fuel_z, fuel_s) = fuel?;
    let (res_full, res_mk) = res?;
    Some(Marker {
        fuel_full,
        fuel_z,
        fuel_s,
        res_full,
        res_mk,
        data_full: data?,
        member_names: member_names?,
        bases: bases?,
        cases: cases?,
        refs: refs?,
        refbases: refbases?,
        refcases: refcases?,
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

/// `f` as the nullary fuel constructor `Z`.
fn is_fuel_z(f: &Formula, marker: &Marker) -> bool {
    matches!(f, Formula::Ctor { ctor, args, .. } if ctor == &marker.fuel_z && args.is_empty())
}

/// `f` as `S <k-var>`.
fn is_fuel_s_of(f: &Formula, marker: &Marker, k: &str) -> bool {
    matches!(f, Formula::Ctor { ctor, args, .. }
        if ctor == &marker.fuel_s && args.len() == 1 && args[0].var_name() == Some(k))
}

/// `f` as the FUEL component selection `<inner>.0` of the result pair
/// (classified by field sort); returns the inner formula.
fn as_fst_sel<'a>(f: &'a Formula, marker: &Marker) -> Option<&'a Formula> {
    let Formula::Sel { datatype, field_sort, arg, .. } = f else {
        return None;
    };
    (datatype == &marker.res_full && is_datatype_sort(field_sort, &marker.fuel_full))
        .then(|| arg.as_ref())
}

/// `f` as the PAYLOAD component selection `<inner>.1`.
fn as_snd_sel<'a>(f: &'a Formula, marker: &Marker) -> Option<&'a Formula> {
    let Formula::Sel { datatype, field_sort, arg, .. } = f else {
        return None;
    };
    (datatype == &marker.res_full && is_datatype_sort(field_sort, &marker.data_full))
        .then(|| arg.as_ref())
}

/// Partitioned binders of one step-arm VC.
struct ArmBinders {
    k: String,
    fields: Vec<String>,
    ihs: Vec<String>,
}

fn partition_binders(binders: &[(String, Sort)], marker: &Marker) -> Option<ArmBinders> {
    let mut k = None;
    let mut fields = Vec::new();
    let mut ihs = Vec::new();
    for (name, sort) in binders {
        if is_datatype_sort(sort, &marker.fuel_full) {
            if k.replace(name.clone()).is_some() {
                return None;
            }
        } else if is_datatype_sort(sort, &marker.res_full) {
            if !name.starts_with("__ih") {
                return None;
            }
            ihs.push(name.clone());
        } else if is_datatype_sort(sort, &marker.data_full) {
            fields.push(name.clone());
        } else {
            return None;
        }
    }
    Some(ArmBinders { k: k?, fields, ihs })
}

/// Parse a payload result tree; `call_of` resolves a candidate `Sel .1` inner
/// value to its call index.
fn parse_tree(
    f: &Formula,
    fields: &[String],
    ctors: &[(String, usize)],
    marker: &Marker,
    call_of: &dyn Fn(&Formula) -> Option<usize>,
) -> Option<TTree> {
    if let Some(inner) = as_snd_sel(f, marker) {
        return Some(TTree::CallSnd(call_of(inner)?));
    }
    if let Some(name) = f.var_name() {
        return Some(TTree::Field(fields.iter().position(|n| n == name)?));
    }
    let Formula::Ctor { ctor, args, .. } = f else {
        return None;
    };
    let (_, arity) = ctors.iter().find(|(c, _)| c == ctor)?;
    if args.len() != *arity {
        return None;
    }
    let out = args
        .iter()
        .map(|a| parse_tree(a, fields, ctors, marker, call_of))
        .collect::<Option<Vec<_>>>()?;
    Some(TTree::Node { ctor: ctor.clone(), args: out })
}

/// Parse `result` (`Mk(rem, tree)`) given the arm's call values.
fn parse_pair_result(
    result: &Formula,
    fields: &[String],
    ctors: &[(String, usize)],
    marker: &Marker,
    k: &str,
    n_calls: usize,
    call_of: &dyn Fn(&Formula) -> Option<usize>,
) -> Option<(RemSrc, TTree)> {
    let Formula::Ctor { ctor, args, .. } = result else {
        return None;
    };
    if ctor != &marker.res_mk {
        return None;
    }
    let [rem, tree] = args.as_slice() else {
        return None;
    };
    let rem = if n_calls == 0 {
        (rem.var_name() == Some(k)).then_some(RemSrc::K)?
    } else {
        let inner = as_fst_sel(rem, marker)?;
        let p = call_of(inner)?;
        if p + 1 != n_calls {
            return None; // the returned remainder is the LAST call's
        }
        RemSrc::CallFst(p)
    };
    let tree = parse_tree(tree, fields, ctors, marker, call_of)?;
    Some((rem, tree))
}

/// Raw per-member/per-reference VC partitions.
#[derive(Default)]
struct Raw<'a> {
    bases: Vec<&'a VerificationCondition>,
    cases: Vec<(&'a str, Vec<&'a str>, &'a VerificationCondition)>,
}

fn entry<'b>(raw: &mut Vec<(String, Raw<'b>)>, name: &str) -> usize {
    if let Some(i) = raw.iter().position(|(n, _)| n == name) {
        i
    } else {
        raw.push((name.to_string(), Raw::default()));
        raw.len() - 1
    }
}

/// Parse one MEMBER step arm.
#[allow(clippy::too_many_arguments)]
fn parse_member_arm(
    formula: &Formula,
    ctor: &str,
    arity: usize,
    calls_tag: &[&str],
    member_names: &[String],
    member_ref: &[usize],
    refs: &[String],
    marker: &Marker,
    ctors: &[(String, usize)],
    member_idx: usize,
) -> Option<TArm> {
    let (binders, body) = split_forall(formula);
    let ab = partition_binders(&binders, marker)?;
    if ab.fields.len() != arity || ab.ihs.len() != calls_tag.len() {
        return None;
    }
    let (atoms, concl): (Vec<&Formula>, &Formula) = match body {
        Formula::Implies(ih, concl) => {
            let atoms = match ih.as_ref() {
                Formula::And(parts) => parts.iter().collect(),
                single => vec![single],
            };
            (atoms, concl.as_ref())
        }
        other => (Vec::new(), other),
    };
    if atoms.len() != ab.ihs.len() {
        return None;
    }
    // IH atoms: atom p is the callee's postcondition at the THREADED fuel.
    let mut calls: Vec<(usize, usize)> = Vec::with_capacity(atoms.len());
    for ((p, atom), call_name) in atoms.iter().enumerate().zip(calls_tag) {
        let callee = member_names.iter().position(|m| m == call_name)?;
        let Formula::Eq(ih_var, rhs) = atom else {
            return None;
        };
        if ih_var.var_name() != Some(ab.ihs[p].as_str()) {
            return None;
        }
        let Formula::FnApp { func, args, .. } = rhs.as_ref() else {
            return None;
        };
        if func != &refs[member_ref[callee]] {
            return None;
        }
        let [fuel_arg, payload_arg] = args.as_slice() else {
            return None;
        };
        // THREADING: call 0 at k, call p at call p-1's remainder.
        let fuel_ok = if p == 0 {
            fuel_arg.var_name() == Some(ab.k.as_str())
        } else {
            as_fst_sel(fuel_arg, marker)
                .and_then(Formula::var_name)
                .is_some_and(|n| n == ab.ihs[p - 1])
        };
        if !fuel_ok {
            return None;
        }
        let field = ab.fields.iter().position(|f| Some(f.as_str()) == payload_arg.var_name())?;
        calls.push((callee, field));
    }
    // Conclusion: `Eq(Mk(rem, tree), FnApp(ref_i, [S k, C(fields)]))`.
    let Formula::Eq(result, rhs) = concl else {
        return None;
    };
    let Formula::FnApp { func, args, .. } = rhs.as_ref() else {
        return None;
    };
    if func != &refs[member_ref[member_idx]] {
        return None;
    }
    let [fuel_inst, payload_inst] = args.as_slice() else {
        return None;
    };
    if !is_fuel_s_of(fuel_inst, marker, &ab.k) {
        return None;
    }
    let pattern_ok = matches!(payload_inst, Formula::Ctor { ctor: pc, args: pa, .. }
        if pc == ctor
            && pa.len() == ab.fields.len()
            && pa.iter().zip(&ab.fields).all(|(a, f)| a.var_name() == Some(f.as_str())));
    if !pattern_ok {
        return None;
    }
    let ihs = ab.ihs.clone();
    let call_of = |f: &Formula| -> Option<usize> {
        f.var_name().and_then(|n| ihs.iter().position(|i| i == n))
    };
    let (rem, tree) =
        parse_pair_result(result, &ab.fields, ctors, marker, &ab.k, calls.len(), &call_of)?;
    Some(TArm { calls, rem, tree })
}

/// Parse one REFERENCE definitional step arm.
#[allow(clippy::too_many_arguments)]
fn parse_ref_arm(
    formula: &Formula,
    ref_name: &str,
    ctor: &str,
    arity: usize,
    calls_tag: &[&str],
    refs: &[String],
    marker: &Marker,
    ctors: &[(String, usize)],
) -> Option<TArm> {
    let (binders, body) = split_forall(formula);
    let ab = partition_binders(&binders, marker)?;
    if ab.fields.len() != arity || !ab.ihs.is_empty() {
        return None;
    }
    let Formula::Eq(lhs, result) = body else {
        return None;
    };
    let Formula::FnApp { func, args, .. } = lhs.as_ref() else {
        return None;
    };
    if func != ref_name {
        return None;
    }
    let [fuel_inst, payload_inst] = args.as_slice() else {
        return None;
    };
    if !is_fuel_s_of(fuel_inst, marker, &ab.k) {
        return None;
    }
    let pattern_ok = matches!(payload_inst, Formula::Ctor { ctor: pc, args: pa, .. }
        if pc == ctor
            && pa.len() == ab.fields.len()
            && pa.iter().zip(&ab.fields).all(|(a, f)| a.var_name() == Some(f.as_str())));
    if !pattern_ok {
        return None;
    }
    // Reconstruct the call CHAIN: call 0 is the FnApp at fuel `k`; call p the
    // FnApp at call p-1's remainder. Calls are definitional applications
    // `FnApp(ref_c, [fuel, field])`.
    fn collect_fnapps<'f>(f: &'f Formula, out: &mut Vec<&'f Formula>) {
        if matches!(f, Formula::FnApp { .. }) && !out.iter().any(|g| *g == f) {
            out.push(f);
        }
        for child in f.children() {
            collect_fnapps(child, out);
        }
    }
    let mut apps: Vec<&Formula> = Vec::new();
    collect_fnapps(result, &mut apps);
    let mut chain: Vec<Formula> = Vec::new();
    let mut calls: Vec<(usize, usize)> = Vec::new();
    for p in 0..calls_tag.len() {
        let expected_fuel_of = |g: &Formula| -> bool {
            let Formula::FnApp { args, .. } = g else {
                return false;
            };
            let Some(fuel_arg) = args.first() else {
                return false;
            };
            if p == 0 {
                fuel_arg.var_name() == Some(ab.k.as_str())
            } else {
                as_fst_sel(fuel_arg, marker).is_some_and(|inner| inner == &chain[p - 1])
            }
        };
        let mut matches_p = apps.iter().filter(|g| expected_fuel_of(g));
        let g = matches_p.next()?;
        if matches_p.next().is_some() {
            return None; // the chain must be linear
        }
        let Formula::FnApp { func, args, .. } = g else {
            return None;
        };
        let callee = refs.iter().position(|r| r == func)?;
        if refs[callee] != calls_tag[p] {
            return None;
        }
        let [_, payload_arg] = args.as_slice() else {
            return None;
        };
        let field = ab.fields.iter().position(|f| Some(f.as_str()) == payload_arg.var_name())?;
        chain.push((*g).clone());
        calls.push((callee, field));
    }
    if apps.len() != calls_tag.len() {
        return None; // no stray applications outside the chain
    }
    let call_of = |f: &Formula| -> Option<usize> { chain.iter().position(|c| c == f) };
    let (rem, tree) =
        parse_pair_result(result, &ab.fields, ctors, marker, &ab.k, calls.len(), &call_of)?;
    Some(TArm { calls, rem, tree })
}

/// Validate one pinned BASE VC (`Forall [e] Eq(Mk(Z, e), FnApp(r, [Z, e]))`,
/// sides swapped for references).
fn check_base(formula: &Formula, ref_name: &str, marker: &Marker, member_side: bool) -> bool {
    let (binders, body) = split_forall(formula);
    let [(e, e_sort)] = binders.as_slice() else {
        return false;
    };
    if !is_datatype_sort(e_sort, &marker.data_full) {
        return false;
    }
    let Formula::Eq(a, b) = body else {
        return false;
    };
    let (pair, app) = if member_side { (a, b) } else { (b, a) };
    let pair_ok = matches!(pair.as_ref(), Formula::Ctor { ctor, args, .. }
        if ctor == &marker.res_mk
            && args.len() == 2
            && is_fuel_z(&args[0], marker)
            && args[1].var_name() == Some(e.as_str()));
    let app_ok = matches!(app.as_ref(), Formula::FnApp { func, args, .. }
        if func == ref_name
            && args.len() == 2
            && is_fuel_z(&args[0], marker)
            && args[1].var_name() == Some(e.as_str()));
    pair_ok && app_ok
}

/// Parse the emitted threaded bundle into a plan. `None` on any shape outside
/// the supported scope.
#[allow(clippy::too_many_lines)]
fn parse_bundle(vcs: &[VerificationCondition]) -> Option<ThreadedPlan> {
    let mut conclusion: Option<&VerificationCondition> = None;
    let mut raw: Vec<(String, Raw)> = Vec::new();
    let mut raw_refs: Vec<(String, Raw)> = Vec::new();
    let mut properties: Vec<String> = Vec::new();
    for vc in vcs {
        let VcKind::FunctionalCorrectness { property, context } = &vc.kind else {
            return None;
        };
        properties.push(property.clone());
        if let Some(member) = property.strip_prefix(BASE_PROPERTY_PREFIX) {
            if context != member {
                return None;
            }
            let i = entry(&mut raw, member);
            raw[i].1.bases.push(vc);
        } else if let Some(rest) = property.strip_prefix(CASE_PROPERTY_PREFIX) {
            let (member, rest) = rest.split_once("::")?;
            let rest = rest.strip_suffix(']')?;
            let (ctor, calls) = rest.split_once("[calls=")?;
            let calls: Vec<&str> =
                if calls.is_empty() { Vec::new() } else { calls.split(',').collect() };
            if context != member {
                return None;
            }
            let i = entry(&mut raw, member);
            raw[i].1.cases.push((ctor, calls, vc));
        } else if let Some(rname) = property.strip_prefix(REF_BASE_PROPERTY_PREFIX) {
            if context != rname {
                return None;
            }
            let i = entry(&mut raw_refs, rname);
            raw_refs[i].1.bases.push(vc);
        } else if let Some(rest) = property.strip_prefix(REF_STEP_PROPERTY_PREFIX) {
            let (rname, rest) = rest.split_once("::")?;
            let rest = rest.strip_suffix(']')?;
            let (ctor, calls) = rest.split_once("[calls=")?;
            let calls: Vec<&str> =
                if calls.is_empty() { Vec::new() } else { calls.split(',').collect() };
            if context != rname {
                return None;
            }
            let i = entry(&mut raw_refs, rname);
            raw_refs[i].1.cases.push((ctor, calls, vc));
        } else if property.starts_with(CONCLUSION_PROPERTY_PREFIX) {
            if conclusion.replace(vc).is_some() {
                return None;
            }
        } else {
            return None;
        }
    }
    let conclusion = conclusion?;
    let VcKind::FunctionalCorrectness { property: c_prop, .. } = &conclusion.kind else {
        return None;
    };
    let marker = parse_marker(c_prop)?;
    if marker.member_names.len() < 2 || marker.refs.is_empty() {
        return None;
    }
    for set in [&marker.member_names, &marker.refs] {
        let mut sorted = set.clone();
        sorted.sort();
        sorted.dedup();
        if sorted.len() != set.len() {
            return None;
        }
    }
    if marker.refs.iter().any(|r| marker.member_names.contains(r)) {
        return None;
    }
    let bundle_order: Vec<&str> = raw.iter().map(|(n, _)| n.as_str()).collect();
    let marker_order: Vec<&str> = marker.member_names.iter().map(String::as_str).collect();
    if bundle_order != marker_order {
        return None;
    }
    let ref_bundle_order: Vec<&str> = raw_refs.iter().map(|(n, _)| n.as_str()).collect();
    let ref_marker_order: Vec<&str> = marker.refs.iter().map(String::as_str).collect();
    if ref_bundle_order != ref_marker_order {
        return None;
    }
    if raw.iter().map(|(_, m)| m.bases.len()).sum::<usize>() != marker.bases
        || raw.iter().map(|(_, m)| m.cases.len()).sum::<usize>() != marker.cases
        || raw_refs.iter().map(|(_, m)| m.bases.len()).sum::<usize>() != marker.refbases
        || raw_refs.iter().map(|(_, m)| m.cases.len()).sum::<usize>() != marker.refcases
    {
        return None;
    }
    let fuel = short_name(&marker.fuel_full)?;
    let res = short_name(&marker.res_full)?;
    let data = short_name(&marker.data_full)?;
    {
        let mut shorts = [fuel.as_str(), res.as_str(), data.as_str()];
        shorts.sort_unstable();
        let mut dedup = shorts.to_vec();
        dedup.dedup();
        if dedup.len() != shorts.len() || marker.fuel_z == marker.fuel_s {
            return None;
        }
    }

    // Conclusion conjuncts: member i's `Forall [fuel, e] Eq(_0, FnApp(r_i, ..))`
    // — recording the member -> reference assignment.
    let Formula::And(conjuncts) = &conclusion.formula else {
        return None;
    };
    if conjuncts.len() != marker.member_names.len() {
        return None;
    }
    let mut member_ref: Vec<usize> = Vec::with_capacity(conjuncts.len());
    for conj in conjuncts {
        let (binders, body) = split_forall(conj);
        let [(fuel_var, fuel_sort), (e_var, e_sort)] = binders.as_slice() else {
            return None;
        };
        if !is_datatype_sort(fuel_sort, &marker.fuel_full)
            || !is_datatype_sort(e_sort, &marker.data_full)
        {
            return None;
        }
        let Formula::Eq(lhs, rhs) = body else {
            return None;
        };
        if lhs.var_name() != Some("_0") {
            return None;
        }
        let Formula::FnApp { func, args, .. } = rhs.as_ref() else {
            return None;
        };
        let r = marker.refs.iter().position(|n| n == func)?;
        let [a_fuel, a_e] = args.as_slice() else {
            return None;
        };
        if a_fuel.var_name() != Some(fuel_var.as_str()) || a_e.var_name() != Some(e_var.as_str()) {
            return None;
        }
        member_ref.push(r);
    }

    // Payload constructor list from the FIRST member's cases.
    let mut ctors: Vec<(String, usize)> = Vec::new();
    for (ctor, _, vc) in &raw[0].1.cases {
        let (binders, _) = split_forall(&vc.formula);
        let ab = partition_binders(&binders, &marker)?;
        ctors.push(((*ctor).to_string(), ab.fields.len()));
    }
    if ctors.is_empty() {
        return None;
    }
    {
        let mut names: Vec<&str> = ctors.iter().map(|(c, _)| c.as_str()).collect();
        names.sort_unstable();
        names.dedup();
        if names.len() != ctors.len() {
            return None;
        }
    }

    // Members.
    let mut members: Vec<Vec<TArm>> = Vec::with_capacity(raw.len());
    for (idx, ((_, rm), _)) in raw.iter().zip(&marker.member_names).enumerate() {
        let [base] = rm.bases.as_slice() else {
            return None;
        };
        if !check_base(&base.formula, &marker.refs[member_ref[idx]], &marker, true) {
            return None;
        }
        if rm.cases.len() != ctors.len()
            || !rm.cases.iter().zip(&ctors).all(|((tag, _, _), (c, _))| tag == c)
        {
            return None;
        }
        let mut arms = Vec::with_capacity(rm.cases.len());
        for ((ctor, arity), (_, calls, vc)) in ctors.iter().zip(&rm.cases) {
            arms.push(parse_member_arm(
                &vc.formula,
                ctor,
                *arity,
                calls,
                &marker.member_names,
                &member_ref,
                &marker.refs,
                &marker,
                &ctors,
                idx,
            )?);
        }
        members.push(arms);
    }

    // References.
    let mut refs: Vec<Vec<TArm>> = Vec::with_capacity(raw_refs.len());
    for (rname, rr) in &raw_refs {
        let [base] = rr.bases.as_slice() else {
            return None;
        };
        if !check_base(&base.formula, rname, &marker, false) {
            return None;
        }
        if rr.cases.len() != ctors.len()
            || !rr.cases.iter().zip(&ctors).all(|((tag, _, _), (c, _))| tag == c)
        {
            return None;
        }
        let mut arms = Vec::with_capacity(rr.cases.len());
        for ((ctor, arity), (_, calls, vc)) in ctors.iter().zip(&rr.cases) {
            arms.push(parse_ref_arm(
                &vc.formula,
                rname,
                ctor,
                *arity,
                calls,
                &marker.refs,
                &marker,
                &ctors,
            )?);
        }
        refs.push(arms);
    }

    let label = format!(
        "threaded_budget_functional:{}:[{}]:{:?}",
        marker.member_names.join("+"),
        properties.join(";"),
        conclusion.formula
    );
    Some(ThreadedPlan {
        fuel,
        fuel_z: marker.fuel_z.clone(),
        fuel_s: marker.fuel_s.clone(),
        res,
        res_mk: marker.res_mk.clone(),
        data,
        ctors,
        members,
        member_ref,
        refs,
        label,
    })
}

// ---------------------------------------------------------------------------
// CIC construction (raw kernel Expr, de Bruijn indices).
// ---------------------------------------------------------------------------

fn level1() -> Level {
    Level::succ(Level::zero())
}

/// Which fold a construction targets.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Side {
    Model,
    Ref,
}

impl Side {
    fn record(self) -> &'static str {
        match self {
            Side::Model => "__ThModels",
            Side::Ref => "__ThRef",
        }
    }

    fn prefix(self) -> &'static str {
        match self {
            Side::Model => "__th",
            Side::Ref => "__thref",
        }
    }
}

impl ThreadedPlan {
    fn n(&self, side: Side) -> usize {
        match side {
            Side::Model => self.members.len(),
            Side::Ref => self.refs.len(),
        }
    }

    fn arms(&self, side: Side, i: usize) -> &[TArm] {
        match side {
            Side::Model => &self.members[i],
            Side::Ref => &self.refs[i],
        }
    }

    fn fuel_expr(&self) -> Expr {
        Expr::const_(Name::from_string(&self.fuel), Vec::new())
    }

    fn data_expr(&self) -> Expr {
        Expr::const_(Name::from_string(&self.data), Vec::new())
    }

    fn res_expr(&self) -> Expr {
        Expr::const_(Name::from_string(&self.res), Vec::new())
    }

    fn fuel_z_expr(&self) -> Expr {
        Expr::const_(Name::from_string(&format!("{}.{}", self.fuel, self.fuel_z)), Vec::new())
    }

    fn fuel_s_expr(&self) -> Expr {
        Expr::const_(Name::from_string(&format!("{}.{}", self.fuel, self.fuel_s)), Vec::new())
    }

    fn mk_pair_expr(&self) -> Expr {
        Expr::const_(Name::from_string(&format!("{}.{}", self.res, self.res_mk)), Vec::new())
    }

    fn e_ctor(&self, ctor: &str) -> Option<Expr> {
        self.ctors.iter().find(|(c, _)| c == ctor)?;
        Some(Expr::const_(Name::from_string(&format!("{}.{ctor}", self.data)), Vec::new()))
    }

    fn res_fst(&self, r: Expr) -> Expr {
        Expr::app(Expr::const_(Name::from_string("__res_fst"), Vec::new()), r)
    }

    fn res_snd(&self, r: Expr) -> Expr {
        Expr::app(Expr::const_(Name::from_string("__res_snd"), Vec::new()), r)
    }

    fn record_expr(&self, side: Side) -> Expr {
        Expr::const_(Name::from_string(side.record()), Vec::new())
    }

    fn mk_record_expr(&self, side: Side) -> Expr {
        Expr::const_(Name::from_string(&format!("{}.mk", side.record())), Vec::new())
    }

    fn proj_expr(&self, side: Side, i: usize) -> Expr {
        Expr::const_(Name::from_string(&format!("{}_proj_{i}", side.prefix())), Vec::new())
    }

    fn cluster_expr(&self, side: Side) -> Expr {
        Expr::const_(Name::from_string(&format!("{}_cluster", side.prefix())), Vec::new())
    }

    fn model_expr(&self, side: Side, i: usize) -> Expr {
        Expr::const_(Name::from_string(&format!("{}_model_{i}", side.prefix())), Vec::new())
    }

    /// `Fuel -> E -> Res` — the fuel-taking record field type.
    fn tfn(&self) -> Expr {
        Expr::pi(
            BinderInfo::Default,
            self.fuel_expr(),
            Expr::pi(BinderInfo::Default, self.data_expr(), self.res_expr()),
        )
    }

    /// `Eq.{1} Res a b`.
    fn eq_res(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(Expr::const_(Name::from_string("Eq"), vec![level1()]), [self.res_expr(), a, b])
    }

    fn refl_res(&self, t: Expr) -> Expr {
        Expr::apps(Expr::const_(Name::from_string("Eq.refl"), vec![level1()]), [self.res_expr(), t])
    }

    /// Right-nested conjunction / intro / projection (as in the mutual lane).
    fn and_chain(&self, props: &[Expr]) -> Expr {
        let and_const = Expr::const_(Name::from_string("And"), Vec::new());
        let mut iter = props.iter().rev();
        let mut acc = iter.next().expect("and_chain over >= 1 props").clone();
        for p in iter {
            acc = Expr::apps(and_const.clone(), [p.clone(), acc]);
        }
        acc
    }

    fn intro_chain(&self, props: &[Expr], proofs: &[Expr]) -> Expr {
        debug_assert_eq!(props.len(), proofs.len());
        if props.len() == 1 {
            return proofs[0].clone();
        }
        let rest_prop = self.and_chain(&props[1..]);
        let rest_proof = self.intro_chain(&props[1..], &proofs[1..]);
        Expr::apps(
            Expr::const_(Name::from_string("And.intro"), Vec::new()),
            [props[0].clone(), rest_prop, proofs[0].clone(), rest_proof],
        )
    }

    fn and_component(&self, props: &[Expr], j: usize, h: Expr) -> Expr {
        if props.len() == 1 {
            return h;
        }
        let rest = self.and_chain(&props[1..]);
        if j == 0 {
            Expr::apps(
                Expr::const_(Name::from_string("And.left"), Vec::new()),
                [props[0].clone(), rest, h],
            )
        } else {
            let tail = Expr::apps(
                Expr::const_(Name::from_string("And.right"), Vec::new()),
                [props[0].clone(), rest, h],
            );
            self.and_component(&props[1..], j - 1, tail)
        }
    }

    // ── Inductives ───────────────────────────────────────────────────────────

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

    /// `Res = Mk(Fuel, E)` — the (remainder, result) pair.
    fn res_inductive(&self) -> InductiveDecl {
        let mk_ty = Expr::pi(
            BinderInfo::Default,
            self.fuel_expr(),
            Expr::pi(BinderInfo::Default, self.data_expr(), self.res_expr()),
        );
        InductiveDecl {
            level_params: vec![],
            num_params: 0,
            types: vec![InductiveType {
                name: Name::from_string(&self.res),
                type_: Expr::type_(),
                constructors: vec![Constructor {
                    name: Name::from_string(&format!("{}.{}", self.res, self.res_mk)),
                    type_: mk_ty,
                }],
            }],
        }
    }

    /// `__res_fst : Res -> Fuel` / `__res_snd : Res -> E` via `Res.rec`.
    fn res_proj_def(&self, fst: bool) -> Declaration {
        let out_ty = if fst { self.fuel_expr() } else { self.data_expr() };
        let motive = Expr::lam(BinderInfo::Default, self.res_expr(), out_ty.clone());
        // Minor for Mk: fun (f : Fuel) (v : E) => f | v (no recursive fields).
        let body = if fst { Expr::bvar(1) } else { Expr::bvar(0) };
        let minor = Expr::lam(
            BinderInfo::Default,
            self.fuel_expr(),
            Expr::lam(BinderInfo::Default, self.data_expr(), body),
        );
        let rec = Expr::apps(
            Expr::const_(Name::from_string(&format!("{}.rec", self.res)), vec![level1()]),
            [motive, minor, Expr::bvar(0)],
        );
        Declaration::Definition {
            name: Name::from_string(if fst { "__res_fst" } else { "__res_snd" }),
            level_params: vec![],
            type_: Expr::pi(BinderInfo::Default, self.res_expr(), out_ty),
            value: Expr::lam(BinderInfo::Default, self.res_expr(), rec),
            is_reducible: true,
        }
    }

    fn models_inductive(&self, side: Side) -> InductiveDecl {
        let mut ctor_ty = self.record_expr(side);
        for _ in 0..self.n(side) {
            ctor_ty = Expr::pi(BinderInfo::Default, self.tfn(), ctor_ty);
        }
        InductiveDecl {
            level_params: vec![],
            num_params: 0,
            types: vec![InductiveType {
                name: Name::from_string(side.record()),
                type_: Expr::type_(),
                constructors: vec![Constructor {
                    name: Name::from_string(&format!("{}.mk", side.record())),
                    type_: ctor_ty,
                }],
            }],
        }
    }

    fn proj_def(&self, side: Side, i: usize) -> Declaration {
        let motive = Expr::lam(BinderInfo::Default, self.record_expr(side), self.tfn());
        let mut minor = Expr::bvar((self.n(side) - 1 - i) as u32);
        for _ in 0..self.n(side) {
            minor = Expr::lam(BinderInfo::Default, self.tfn(), minor);
        }
        let rec = Expr::apps(
            Expr::const_(Name::from_string(&format!("{}.rec", side.record())), vec![level1()]),
            [motive, minor, Expr::bvar(0)],
        );
        Declaration::Definition {
            name: Name::from_string(&format!("{}_proj_{i}", side.prefix())),
            level_params: vec![],
            type_: Expr::pi(BinderInfo::Default, self.record_expr(side), self.tfn()),
            value: Expr::lam(BinderInfo::Default, self.record_expr(side), rec),
            is_reducible: true,
        }
    }

    // ── The MAJORANT fold ────────────────────────────────────────────────────

    /// The arm's call-value expressions at depth `depth`, where `prev` is the
    /// previous-majorant RECORD expression (valid at `depth`), `j_at` the live
    /// decremented fuel, and `field_at(p)` the arm's field variables. Call 0
    /// runs at `j`, call p at call p-1's remainder — the THREADED chain.
    fn call_values(
        &self,
        side_of: &dyn Fn(usize) -> (Side, usize),
        arm: &TArm,
        prev: &Expr,
        j: &Expr,
        field_at: &dyn Fn(usize) -> Expr,
    ) -> Vec<Expr> {
        let mut vals: Vec<Expr> = Vec::with_capacity(arm.calls.len());
        for (p, (callee, field)) in arm.calls.iter().enumerate() {
            let fuel = if p == 0 { j.clone() } else { self.res_fst(vals[p - 1].clone()) };
            let (side, callee_i) = side_of(*callee);
            vals.push(Expr::apps(
                self.proj_expr(side, callee_i),
                [prev.clone(), fuel, field_at(*field)],
            ));
        }
        vals
    }

    /// `Mk rem tree` from parsed arm parts and call values.
    fn pair_value(
        &self,
        arm: &TArm,
        j: &Expr,
        field_at: &dyn Fn(usize) -> Expr,
        call_vals: &[Expr],
    ) -> Option<Expr> {
        let rem = match arm.rem {
            RemSrc::K => j.clone(),
            RemSrc::CallFst(p) => self.res_fst(call_vals.get(p)?.clone()),
        };
        let tree = self.tree_expr(&arm.tree, field_at, call_vals)?;
        Some(Expr::apps(self.mk_pair_expr(), [rem, tree]))
    }

    fn tree_expr(
        &self,
        t: &TTree,
        field_at: &dyn Fn(usize) -> Expr,
        call_vals: &[Expr],
    ) -> Option<Expr> {
        match t {
            TTree::Field(p) => Some(field_at(*p)),
            TTree::CallSnd(p) => Some(self.res_snd(call_vals.get(*p)?.clone())),
            TTree::Node { ctor, args } => {
                let mut expr = self.e_ctor(ctor)?;
                for a in args {
                    expr = Expr::app(expr, self.tree_expr(a, field_at, call_vals)?);
                }
                Some(expr)
            }
        }
    }

    /// One member's STEP-sheet field (under binders K, prev — levels
    /// `k_level`, `k_level+1`):
    /// `fun (m : Fuel) (e : E) => Fuel.rec.{1} (motive fun _ => Res)
    ///    (Mk Z e) (fun j _ => E.rec.{1} (motive fun _ => Res) <minors> e) m`.
    fn step_field(&self, side: Side, i: usize, k_level: usize) -> Option<Expr> {
        let prev_level = k_level + 1;
        let m_level = k_level + 2;
        let e_level = k_level + 3;
        // Z-case (depth = e_level + 1): Mk Z e.
        let z_depth = e_level + 1;
        let z_case = Expr::apps(
            self.mk_pair_expr(),
            [self.fuel_z_expr(), Expr::bvar((z_depth - 1 - e_level) as u32)],
        );
        // S-case: fun (j : Fuel) (_ : Res) => E.rec ... e.
        let j_level = e_level + 1;
        let erec_depth = e_level + 3; // under j, junk
        let mut rec_args = vec![Expr::lam(BinderInfo::Default, self.data_expr(), self.res_expr())];
        for (arm, (_, arity)) in self.arms(side, i).iter().zip(&self.ctors) {
            // Minor: fields then junk payload-IHs (motive constant Res).
            let a = *arity;
            let body_depth = erec_depth + 2 * a;
            let field_at = |p: usize| Expr::bvar((body_depth - 1 - (erec_depth + p)) as u32);
            let prev = Expr::bvar((body_depth - 1 - prev_level) as u32);
            let j = Expr::bvar((body_depth - 1 - j_level) as u32);
            // In-fold calls target the SAME side's record: callee index is
            // the member index within this side.
            let side_of = |callee: usize| (side, callee);
            let call_vals = self.call_values(&side_of, arm, &prev, &j, &field_at);
            let mut body = self.pair_value(arm, &j, &field_at, &call_vals)?;
            for _ in 0..a {
                body = Expr::lam(BinderInfo::Default, self.res_expr(), body); // junk IHs
            }
            for _ in 0..a {
                body = Expr::lam(BinderInfo::Default, self.data_expr(), body); // fields
            }
            rec_args.push(body);
        }
        rec_args.push(Expr::bvar((erec_depth - 1 - e_level) as u32));
        let e_rec = Expr::apps(
            Expr::const_(Name::from_string(&format!("{}.rec", self.data)), vec![level1()]),
            rec_args,
        );
        let s_case = Expr::lam(
            BinderInfo::Default,
            self.fuel_expr(),
            Expr::lam(BinderInfo::Default, self.res_expr(), e_rec),
        );
        let m_rec = Expr::apps(
            Expr::const_(Name::from_string(&format!("{}.rec", self.fuel)), vec![level1()]),
            [
                Expr::lam(BinderInfo::Default, self.fuel_expr(), self.res_expr()),
                z_case,
                s_case,
                Expr::bvar((e_level + 1 - 1 - m_level) as u32),
            ],
        );
        Some(Expr::lam(
            BinderInfo::Default,
            self.fuel_expr(),
            Expr::lam(BinderInfo::Default, self.data_expr(), m_rec),
        ))
    }

    /// `<side>_cluster : Fuel -> Record` — the majorant fold.
    fn cluster_def(&self, side: Side) -> Option<Declaration> {
        let n = self.n(side);
        // Base sheet (majorant Z): every field is `fun m e => Mk m e`.
        let base_field = Expr::lam(
            BinderInfo::Default,
            self.fuel_expr(),
            Expr::lam(
                BinderInfo::Default,
                self.data_expr(),
                Expr::apps(self.mk_pair_expr(), [Expr::bvar(1), Expr::bvar(0)]),
            ),
        );
        let base = Expr::apps(self.mk_record_expr(side), vec![base_field; n]);
        // Step sheet: fun (K : Fuel) (prev : Record) => Record.mk <fields>.
        // K sits at level 1 (under the definition's outer `fun n`).
        let step_fields =
            (0..n).map(|i| self.step_field(side, i, 1)).collect::<Option<Vec<_>>>()?;
        let step_body = Expr::apps(self.mk_record_expr(side), step_fields);
        let step = Expr::lam(
            BinderInfo::Default,
            self.fuel_expr(),
            Expr::lam(BinderInfo::Default, self.record_expr(side), step_body),
        );
        let rec = Expr::apps(
            Expr::const_(Name::from_string(&format!("{}.rec", self.fuel)), vec![level1()]),
            [
                Expr::lam(BinderInfo::Default, self.fuel_expr(), self.record_expr(side)),
                base,
                step,
                Expr::bvar(0),
            ],
        );
        Some(Declaration::Definition {
            name: Name::from_string(&format!("{}_cluster", side.prefix())),
            level_params: vec![],
            type_: Expr::pi(BinderInfo::Default, self.fuel_expr(), self.record_expr(side)),
            value: Expr::lam(BinderInfo::Default, self.fuel_expr(), rec),
            is_reducible: true,
        })
    }

    /// `<side>_model_i := fun n e => proj_i (cluster n) n e` — the DIAGONAL.
    fn model_def(&self, side: Side, i: usize) -> Declaration {
        let body = Expr::apps(
            self.proj_expr(side, i),
            [Expr::app(self.cluster_expr(side), Expr::bvar(1)), Expr::bvar(1), Expr::bvar(0)],
        );
        Declaration::Definition {
            name: Name::from_string(&format!("{}_model_{i}", side.prefix())),
            level_params: vec![],
            type_: Expr::pi(
                BinderInfo::Default,
                self.fuel_expr(),
                Expr::pi(BinderInfo::Default, self.data_expr(), self.res_expr()),
            ),
            value: Expr::lam(
                BinderInfo::Default,
                self.fuel_expr(),
                Expr::lam(BinderInfo::Default, self.data_expr(), body),
            ),
            is_reducible: true,
        }
    }

    fn build_env(&self) -> Option<Environment> {
        // Shape sanity: every call's callee/field and tree indices in range.
        for (side, count) in [(Side::Model, self.members.len()), (Side::Ref, self.refs.len())] {
            for i in 0..count {
                for (arm, (_, arity)) in self.arms(side, i).iter().zip(&self.ctors) {
                    for (callee, field) in &arm.calls {
                        if *callee >= count || *field >= *arity {
                            return None;
                        }
                    }
                }
            }
        }
        let mut env = Environment::default();
        env.init_eq().ok()?;
        env.init_and().ok()?;
        env.add_inductive(self.fuel_inductive()).ok()?;
        env.add_inductive(self.data_inductive()).ok()?;
        env.add_inductive(self.res_inductive()).ok()?;
        env.add_decl(self.res_proj_def(true)).ok()?;
        env.add_decl(self.res_proj_def(false)).ok()?;
        for side in [Side::Ref, Side::Model] {
            env.add_inductive(self.models_inductive(side)).ok()?;
            for i in 0..self.n(side) {
                env.add_decl(self.proj_def(side, i)).ok()?;
            }
            env.add_decl(self.cluster_def(side)?).ok()?;
            for i in 0..self.n(side) {
                env.add_decl(self.model_def(side, i)).ok()?;
            }
        }
        Some(env)
    }

    // ── Goal + proof ─────────────────────────────────────────────────────────

    /// Goal conjunct i under the binder `n` at level `n_level`, formed at
    /// depth `d`: `forall (e : E), Eq (model_i n e) (refmodel_i n e)`.
    fn goal_conjunct(&self, i: usize, n_level: usize, d: usize) -> Expr {
        let n = Expr::bvar((d + 1 - 1 - n_level) as u32);
        let body = self.eq_res(
            Expr::apps(self.model_expr(Side::Model, i), [n.clone(), Expr::bvar(0)]),
            Expr::apps(self.model_expr(Side::Ref, self.member_ref[i]), [n, Expr::bvar(0)]),
        );
        Expr::pi(BinderInfo::Default, self.data_expr(), body)
    }

    /// `forall n, And_i (forall e, model_i n e = ref_i n e)`.
    fn goal(&self) -> Expr {
        let props: Vec<Expr> =
            (0..self.members.len()).map(|i| self.goal_conjunct(i, 0, 1)).collect();
        Expr::pi(BinderInfo::Default, self.fuel_expr(), self.and_chain(&props))
    }

    /// The majorant motive component `P'_j(w)` at depth `d`:
    /// `forall (m : Fuel) (e : E),
    ///    Eq (proj_j (Mcluster w) m e) (proj_j (Rcluster w) m e)`.
    /// `w_at(at)` forms `w` at inner depth `at`.
    fn p_prime(&self, j: usize, w_at: &dyn Fn(usize) -> Expr, d: usize) -> Expr {
        let inner = d + 2;
        let w = w_at(inner);
        let m = Expr::bvar(1);
        let e = Expr::bvar(0);
        let lhs = Expr::apps(
            self.proj_expr(Side::Model, j),
            [Expr::app(self.cluster_expr(Side::Model), w.clone()), m.clone(), e.clone()],
        );
        let rhs = Expr::apps(
            self.proj_expr(Side::Ref, self.member_ref[j]),
            [Expr::app(self.cluster_expr(Side::Ref), w), m, e],
        );
        Expr::pi(
            BinderInfo::Default,
            self.fuel_expr(),
            Expr::pi(BinderInfo::Default, self.data_expr(), self.eq_res(lhs, rhs)),
        )
    }

    fn p_prime_all(&self, w_at: &dyn Fn(usize) -> Expr, d: usize) -> Vec<Expr> {
        (0..self.members.len()).map(|j| self.p_prime(j, w_at, d)).collect()
    }

    /// The PROOF-side call-value expressions for `arm` at depth `d`, with
    /// switch point `t` (calls < t on the REFERENCE side, >= t on the MODEL
    /// side) and an optional hole substituting call index `hole` by
    /// `Expr::bvar(0)` (the one-hole abstraction's binder — callers must
    /// build at `d + 1` for the lambda body).
    #[allow(clippy::too_many_arguments)]
    fn proof_call_values(
        &self,
        arm: &TArm,
        t: usize,
        hole: Option<usize>,
        k_level: usize,
        j_level: usize,
        field_level0: usize,
        d: usize,
    ) -> Vec<Expr> {
        let k = Expr::bvar((d - 1 - k_level) as u32);
        let j = Expr::bvar((d - 1 - j_level) as u32);
        let field = |p: usize| Expr::bvar((d - 1 - (field_level0 + p)) as u32);
        let mut vals: Vec<Expr> = Vec::with_capacity(arm.calls.len());
        for (p, (callee, fidx)) in arm.calls.iter().enumerate() {
            if hole == Some(p) {
                vals.push(Expr::bvar(0));
                continue;
            }
            let fuel = if p == 0 { j.clone() } else { self.res_fst(vals[p - 1].clone()) };
            let (side, idx) =
                if p < t { (Side::Ref, self.member_ref[*callee]) } else { (Side::Model, *callee) };
            let prev = Expr::app(self.cluster_expr(side), k.clone());
            vals.push(Expr::apps(self.proj_expr(side, idx), [prev, fuel, field(*fidx)]));
        }
        vals
    }

    /// One member's STEP-leg proof component (under binders K at `k_level`,
    /// ih at `k_level + 1`), at depth `d0 = k_level + 2`:
    /// `fun (m : Fuel) => Fuel.rec.{0} <motive over m'> <Z> <S> m`.
    #[allow(clippy::too_many_lines)]
    fn step_component(&self, i: usize, k_level: usize, d0: usize) -> Option<Expr> {
        let r = self.member_ref[i];
        let s_k = |at: usize| Expr::app(self.fuel_s_expr(), Expr::bvar((at - 1 - k_level) as u32));
        // proj_i (side-cluster (S K)) fuel e — the stuck application.
        let sheet = |side: Side, idx: usize, fuel: Expr, e: Expr, at: usize| {
            Expr::apps(
                self.proj_expr(side, idx),
                [Expr::app(self.cluster_expr(side), s_k(at)), fuel, e],
            )
        };
        // Motive: fun (m' : Fuel) => forall (e : E), Eq (M-sheet m' e) (R-sheet m' e).
        let motive = {
            let at = d0 + 3; // under m (d0), m' (d0+1), e (d0+2)
            let m_prime = Expr::bvar((at - 1 - (d0 + 1)) as u32);
            let e = Expr::bvar(0);
            Expr::lam(
                BinderInfo::Default,
                self.fuel_expr(),
                Expr::pi(
                    BinderInfo::Default,
                    self.data_expr(),
                    self.eq_res(
                        sheet(Side::Model, i, m_prime.clone(), e.clone(), at),
                        sheet(Side::Ref, r, m_prime, e, at),
                    ),
                ),
            )
        };
        // Z-minor: fun (e : E) => refl (M-sheet Z e).
        let z_minor = {
            let at = d0 + 2; // under m, e
            Expr::lam(
                BinderInfo::Default,
                self.data_expr(),
                self.refl_res(sheet(Side::Model, i, self.fuel_z_expr(), Expr::bvar(0), at)),
            )
        };
        // S-minor: fun (j : Fuel) (junk : motive j) (e : E) => E.rec ... e.
        let s_minor = {
            let j_level = d0 + 1;
            let e_level = d0 + 3;
            // junk binder TYPE = motive applied at j: forall e, Eq(.. (S K) j e ..).
            let junk_ty = {
                let at = d0 + 3; // under m, j, its own e binder
                let j = Expr::bvar((at - 1 - j_level) as u32);
                let e = Expr::bvar(0);
                Expr::pi(
                    BinderInfo::Default,
                    self.data_expr(),
                    self.eq_res(
                        sheet(Side::Model, i, j.clone(), e.clone(), at),
                        sheet(Side::Ref, r, j, e, at),
                    ),
                )
            };
            // E.rec motive: fun (y : E) => Eq(M-sheet (S j) y, R-sheet (S j) y).
            let erec_depth = e_level + 1; // args of E.rec formed under m, j, junk, e
            let s_j =
                |at: usize| Expr::app(self.fuel_s_expr(), Expr::bvar((at - 1 - j_level) as u32));
            let e_motive = {
                let at = erec_depth + 1; // + y binder
                let y = Expr::bvar(0);
                Expr::lam(
                    BinderInfo::Default,
                    self.data_expr(),
                    self.eq_res(
                        sheet(Side::Model, i, s_j(at), y.clone(), at),
                        sheet(Side::Ref, r, s_j(at), y, at),
                    ),
                )
            };
            let mut rec_args = vec![e_motive];
            for (arm, (_ctor, arity)) in self.arms(Side::Model, i).iter().zip(&self.ctors) {
                let a = *arity;
                let field_level0 = erec_depth;
                let body_depth = erec_depth + 2 * a;
                // eih binder types: E.rec motive applied at the field var.
                let eih_ty = |ty_depth: usize, field_p: usize| {
                    let x = Expr::bvar((ty_depth - 1 - (field_level0 + field_p)) as u32);
                    self.eq_res(
                        sheet(Side::Model, i, s_j(ty_depth), x.clone(), ty_depth),
                        sheet(Side::Ref, r, s_j(ty_depth), x, ty_depth),
                    )
                };
                let body =
                    self.arm_equality_proof(arm, k_level, j_level, field_level0, body_depth)?;
                // Wrap: fields then one IH per field (all payload fields are
                // recursive), IH types formed at their own depths.
                let mut expr = body;
                for q in (0..a).rev() {
                    let ty_depth = erec_depth + a + q;
                    expr = Expr::lam(BinderInfo::Default, eih_ty(ty_depth, q), expr);
                }
                for _ in 0..a {
                    expr = Expr::lam(BinderInfo::Default, self.data_expr(), expr);
                }
                rec_args.push(expr);
            }
            rec_args.push(Expr::bvar((erec_depth - 1 - e_level) as u32));
            let e_rec = Expr::apps(
                Expr::const_(Name::from_string(&format!("{}.rec", self.data)), vec![Level::zero()]),
                rec_args,
            );
            Expr::lam(
                BinderInfo::Default,
                self.fuel_expr(),
                Expr::lam(
                    BinderInfo::Default,
                    junk_ty,
                    Expr::lam(BinderInfo::Default, self.data_expr(), e_rec),
                ),
            )
        };
        let rec = Expr::apps(
            Expr::const_(Name::from_string(&format!("{}.rec", self.fuel)), vec![Level::zero()]),
            [motive, z_minor, s_minor, Expr::bvar(0)],
        );
        Some(Expr::lam(BinderInfo::Default, self.fuel_expr(), rec))
    }

    /// The per-arm equality proof: the congruence chain rewriting the MODEL
    /// arm instance into its all-REFERENCE-side counterpart, one `congrArg`
    /// per call (each justified by the product IH's callee component applied
    /// at the THREADED fuel), composed with `Eq.trans`. Built from the MODEL
    /// arm ONLY — whether the final endpoint matches the REFERENCE fold's own
    /// arm reduct is the KERNEL's judgment: a reference whose arm disagrees
    /// (different calls, different remainder, different tree) type-checks
    /// nowhere, so the mint fails closed with a kernel witness, never a false
    /// `Certified`. Call-free arms close by `refl` (same judgment).
    fn arm_equality_proof(
        &self,
        arm: &TArm,
        k_level: usize,
        j_level: usize,
        field_level0: usize,
        d: usize,
    ) -> Option<Expr> {
        let ih_level = k_level + 1;
        let field = |p: usize, at: usize| Expr::bvar((at - 1 - (field_level0 + p)) as u32);
        let c = arm.calls.len();
        let endpoint = |t: usize, at: usize| -> Option<Expr> {
            let vals = self.proof_call_values(arm, t, None, k_level, j_level, field_level0, at);
            let j = Expr::bvar((at - 1 - j_level) as u32);
            self.pair_value(arm, &j, &|p| field(p, at), &vals)
        };
        if c == 0 {
            return Some(self.refl_res(endpoint(0, d)?));
        }
        let ih_props =
            |at: usize| self.p_prime_all(&|inner| Expr::bvar((inner - 1 - k_level) as u32), at);
        let ih = |at: usize| Expr::bvar((at - 1 - ih_level) as u32);
        let cong = |t: usize| -> Option<Expr> {
            // One-hole abstraction over call t (the hole reaches every later
            // call's fuel chain and the returned remainder).
            let hole_vals =
                self.proof_call_values(arm, t, Some(t), k_level, j_level, field_level0, d + 1);
            let j1 = Expr::bvar((d + 1 - 1 - j_level) as u32);
            let hole_body = self.pair_value(arm, &j1, &|p| field(p, d + 1), &hole_vals)?;
            // The rewrite: call t's MODEL value over the R prefix becomes its
            // REFERENCE value over the same prefix.
            let lhs_vals = self.proof_call_values(arm, t, None, k_level, j_level, field_level0, d);
            let rhs_vals =
                self.proof_call_values(arm, t + 1, None, k_level, j_level, field_level0, d);
            let lhs = lhs_vals.get(t)?.clone();
            let rhs = rhs_vals.get(t)?.clone();
            let (callee, fidx) = arm.calls[t];
            let fuel_arg = if t == 0 {
                Expr::bvar((d - 1 - j_level) as u32)
            } else {
                self.res_fst(rhs_vals.get(t - 1)?.clone())
            };
            let h = Expr::apps(
                self.and_component(&ih_props(d), callee, ih(d)),
                [fuel_arg, field(fidx, d)],
            );
            Some(Expr::apps(
                Expr::const_(Name::from_string("congrArg"), vec![level1(), level1()]),
                [
                    self.res_expr(),
                    self.res_expr(),
                    lhs,
                    rhs,
                    Expr::lam(BinderInfo::Default, self.res_expr(), hole_body),
                    h,
                ],
            ))
        };
        let mut acc = cong(0)?;
        for t in 1..c {
            acc = Expr::apps(
                Expr::const_(Name::from_string("Eq.trans"), vec![level1()]),
                [
                    self.res_expr(),
                    endpoint(0, d)?,
                    endpoint(t, d)?,
                    endpoint(t + 1, d)?,
                    acc,
                    cong(t)?,
                ],
            );
        }
        Some(acc)
    }

    /// The joint majorant-induction proof.
    fn proof(&self) -> Option<Expr> {
        let n_members = self.members.len();
        // motive = fun (w : Fuel) => AndChain_j P'_j(w). Only `w` is free
        // inside, so the motive is a CLOSED lambda (depth-independent).
        let motive = {
            let props = self.p_prime_all(&|inner| Expr::bvar((inner - 1) as u32), 1);
            Expr::lam(BinderInfo::Default, self.fuel_expr(), self.and_chain(&props))
        };
        // Base leg (closed): components `fun m e => refl (proj (Mcl Z) m e)`.
        let base = {
            let props = self.p_prime_all(&|_inner| self.fuel_z_expr(), 0);
            let proofs: Vec<Expr> = (0..n_members)
                .map(|j| {
                    let lhs = Expr::apps(
                        self.proj_expr(Side::Model, j),
                        [
                            Expr::app(self.cluster_expr(Side::Model), self.fuel_z_expr()),
                            Expr::bvar(1),
                            Expr::bvar(0),
                        ],
                    );
                    Expr::lam(
                        BinderInfo::Default,
                        self.fuel_expr(),
                        Expr::lam(BinderInfo::Default, self.data_expr(), self.refl_res(lhs)),
                    )
                })
                .collect();
            self.intro_chain(&props, &proofs)
        };
        // Step leg: fun (K : Fuel) (ih : AndChain P'(K)) => intro chain of
        // step components. K at level 0 of the step lambda (the proof term's
        // Fuel.rec minors are closed).
        let step = {
            let k_level = 0;
            let ih_ty = {
                let props = self.p_prime_all(&|inner| Expr::bvar((inner - 1 - k_level) as u32), 1);
                self.and_chain(&props)
            };
            let d0 = 2; // under K, ih
            let props = self.p_prime_all(
                &|inner| Expr::app(self.fuel_s_expr(), Expr::bvar((inner - 1 - k_level) as u32)),
                d0,
            );
            let proofs = (0..n_members)
                .map(|i| self.step_component(i, k_level, d0))
                .collect::<Option<Vec<_>>>()?;
            Expr::lam(
                BinderInfo::Default,
                self.fuel_expr(),
                Expr::lam(BinderInfo::Default, ih_ty, self.intro_chain(&props, &proofs)),
            )
        };
        // fun (n : Fuel) => intro chain over i of
        //   fun (e : E) => (and_component (L n)) n e.
        let lterm = |at: usize| {
            Expr::apps(
                Expr::const_(Name::from_string(&format!("{}.rec", self.fuel)), vec![Level::zero()]),
                [motive.clone(), base.clone(), step.clone(), Expr::bvar((at - 1) as u32)],
            )
        };
        let goal_props: Vec<Expr> = (0..n_members).map(|i| self.goal_conjunct(i, 0, 1)).collect();
        let proofs: Vec<Expr> = (0..n_members)
            .map(|i| {
                let d = 2; // under n, e
                let lprops = self.p_prime_all(&|inner| Expr::bvar((inner - 1) as u32), d);
                let comp = self.and_component(&lprops, i, lterm(d));
                Expr::lam(
                    BinderInfo::Default,
                    self.data_expr(),
                    Expr::apps(comp, [Expr::bvar(1), Expr::bvar(0)]),
                )
            })
            .collect();
        Some(Expr::lam(
            BinderInfo::Default,
            self.fuel_expr(),
            self.intro_chain(&goal_props, &proofs),
        ))
    }

    /// The refl-only PSEUDO-proof — must be kernel-REJECTED (the models are
    /// distinct stuck constants on the free `n`).
    fn refl_only_pseudo_proof(&self) -> Expr {
        let n_members = self.members.len();
        let props: Vec<Expr> = (0..n_members).map(|i| self.goal_conjunct(i, 0, 1)).collect();
        let proofs: Vec<Expr> = (0..n_members)
            .map(|i| {
                let model =
                    Expr::apps(self.model_expr(Side::Model, i), [Expr::bvar(1), Expr::bvar(0)]);
                Expr::lam(BinderInfo::Default, self.data_expr(), self.refl_res(model))
            })
            .collect();
        Expr::lam(BinderInfo::Default, self.fuel_expr(), self.intro_chain(&props, &proofs))
    }
}

// ---------------------------------------------------------------------------
// Mint / recheck / witnesses.
// ---------------------------------------------------------------------------

fn kernel_checks_goal(env: &Environment, term: &Expr, goal: &Expr) -> bool {
    TypeChecker::with_context(env, LocalContext::new()).check_type(term, goal).is_ok()
}

fn threaded_lineage_digest(
    vcs: &[VerificationCondition],
    term_bytes: &[u8],
    context_bytes: &[u8],
    label: &str,
) -> Option<trust_ir::ProofDigest> {
    let encoded_vcs = bincode::serialize(vcs).ok()?;
    let mut hasher = Sha256::new();
    hasher.update(THREADED_LINEAGE_DOMAIN.as_bytes());
    for (tag, field) in [
        (b"term:".as_slice(), term_bytes),
        (b"ctx:".as_slice(), context_bytes),
        (b"label:".as_slice(), label.as_bytes()),
        (b"vcs:".as_slice(), encoded_vcs.as_slice()),
    ] {
        hasher.update(tag);
        hasher.update((field.len() as u64).to_le_bytes());
        hasher.update(field);
    }
    let digest = hasher.finalize();
    let mut bytes = [0u8; 32];
    bytes.copy_from_slice(&digest);
    Some(trust_ir::ProofDigest::sha256(bytes))
}

/// Mint a kernel-CHECKED `CleanCic` certificate discharging a THREADED-budget
/// bundle by the generated MAJORANT `Fuel.rec` induction with the
/// all-threaded-fuels product motive. Fail-closed on every count.
#[must_use]
pub fn certify_threaded_budget_functional(
    vcs: &[VerificationCondition],
) -> Option<trust_ir::ProofEvidence> {
    let plan = parse_bundle(vcs)?;
    let env = plan.build_env()?;
    let goal = plan.goal();
    let proof = plan.proof()?;
    if !kernel_checks_goal(&env, &proof, &goal) {
        return None;
    }
    let term_bytes = serialize_term(&proof).ok()?;
    let context_bytes = crate::canonical_empty_context_bytes()?;
    let lineage = threaded_lineage_digest(vcs, &term_bytes, &context_bytes, &plan.label)?;
    if !recheck_threaded_budget_functional(vcs, &term_bytes, &context_bytes, &lineage) {
        return None;
    }
    Some(trust_ir::ProofEvidence::CleanCic {
        term: term_bytes,
        context: context_bytes,
        lineage,
        kernel_recheck: None,
    })
}

/// Consumer-side re-check (independent re-parse, kernel re-check, digest
/// re-bind).
#[must_use]
pub fn recheck_threaded_budget_functional(
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
    let goal = plan.goal();
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
    threaded_lineage_digest(vcs, term_bytes, context_bytes, &plan.label).as_ref() == Some(lineage)
}

/// LOAD-BEARING-INDUCTION witness: the generated majorant induction is
/// ACCEPTED and the refl-only pseudo-proof is REJECTED.
#[must_use]
pub fn threaded_induction_is_load_bearing(vcs: &[VerificationCondition]) -> bool {
    let Some(plan) = parse_bundle(vcs) else {
        return false;
    };
    let (Some(env), Some(proof)) = (plan.build_env(), plan.proof()) else {
        return false;
    };
    let goal = plan.goal();
    let pseudo = plan.refl_only_pseudo_proof();
    kernel_checks_goal(&env, &proof, &goal) && !kernel_checks_goal(&env, &pseudo, &goal)
}

#[cfg(test)]
mod tests {
    use super::*;

    // The unit tests drive HAND-BUILT bundles in the exact emitted shape (the
    // integration e2e drives the literal trust-vcgen output). Shapes are the
    // 2-member fixture over E = A | B(E) | M(E, E), Res = Mk(Fuel, E).

    fn fuel_sort() -> Sort {
        Sort::Datatype { name: "fuel::Fuel".to_string(), constructors: vec![] }
    }

    fn e_sort() -> Sort {
        Sort::Datatype { name: "expr::E".to_string(), constructors: vec![] }
    }

    fn res_sort() -> Sort {
        Sort::Datatype { name: "res::Res".to_string(), constructors: vec![] }
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

    fn mk_pair(rem: Formula, tree: Formula) -> Formula {
        Formula::Ctor { ctor: "Mk".to_string(), args: vec![rem, tree], sort: res_sort() }
    }

    fn fst_of(inner: Formula) -> Formula {
        Formula::Sel {
            datatype: "res::Res".to_string(),
            field: "0".to_string(),
            field_sort: fuel_sort(),
            arg: Box::new(inner),
        }
    }

    fn snd_of(inner: Formula) -> Formula {
        Formula::Sel {
            datatype: "res::Res".to_string(),
            field: "1".to_string(),
            field_sort: e_sort(),
            arg: Box::new(inner),
        }
    }

    fn fnapp(f: &str, args: Vec<Formula>) -> Formula {
        Formula::FnApp { func: f.to_string(), args, sort: res_sort() }
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
        }
    }

    /// One member's VCs (`member` calling `callee`, referenced by `rname`
    /// whose callee-reference is `callee_ref`).
    fn member_vcs(
        member: &str,
        callee: &str,
        rname: &str,
        callee_ref: &str,
    ) -> Vec<VerificationCondition> {
        let k = || var("__fld_S_0", fuel_sort());
        let base = Formula::forall(
            &[("e", e_sort())],
            Formula::Eq(
                Box::new(mk_pair(fuel_ctor("Z", vec![]), var("e", e_sort()))),
                Box::new(fnapp(rname, vec![fuel_ctor("Z", vec![]), var("e", e_sort())])),
            ),
        );
        let s_k = || fuel_ctor("S", vec![k()]);
        let case_a = Formula::forall(
            &[("__fld_S_0", fuel_sort())],
            Formula::Eq(
                Box::new(mk_pair(k(), e_ctor("A", vec![]))),
                Box::new(fnapp(rname, vec![s_k(), e_ctor("A", vec![])])),
            ),
        );
        let x = || var("__fld_B_0", e_sort());
        let ih0 = || var("__ih0", res_sort());
        let case_b = Formula::forall(
            &[("__fld_S_0", fuel_sort()), ("__fld_B_0", e_sort()), ("__ih0", res_sort())],
            Formula::Implies(
                Box::new(Formula::Eq(Box::new(ih0()), Box::new(fnapp(callee_ref, vec![k(), x()])))),
                Box::new(Formula::Eq(
                    Box::new(mk_pair(fst_of(ih0()), e_ctor("B", vec![snd_of(ih0())]))),
                    Box::new(fnapp(rname, vec![s_k(), e_ctor("B", vec![x()])])),
                )),
            ),
        );
        let mx = || var("__fld_M_0", e_sort());
        let my = || var("__fld_M_1", e_sort());
        let ih1 = || var("__ih1", res_sort());
        let case_m = Formula::forall(
            &[
                ("__fld_S_0", fuel_sort()),
                ("__fld_M_0", e_sort()),
                ("__fld_M_1", e_sort()),
                ("__ih0", res_sort()),
                ("__ih1", res_sort()),
            ],
            Formula::Implies(
                Box::new(Formula::And(vec![
                    Formula::Eq(Box::new(ih0()), Box::new(fnapp(callee_ref, vec![k(), mx()]))),
                    Formula::Eq(
                        Box::new(ih1()),
                        Box::new(fnapp(callee_ref, vec![fst_of(ih0()), my()])),
                    ),
                ])),
                Box::new(Formula::Eq(
                    Box::new(mk_pair(
                        fst_of(ih1()),
                        e_ctor("M", vec![snd_of(ih0()), snd_of(ih1())]),
                    )),
                    Box::new(fnapp(rname, vec![s_k(), e_ctor("M", vec![mx(), my()])])),
                )),
            ),
        );
        vec![
            vc(&format!("{BASE_PROPERTY_PREFIX}{member}"), member, base),
            vc(&format!("{CASE_PROPERTY_PREFIX}{member}::A[calls=]"), member, case_a),
            vc(&format!("{CASE_PROPERTY_PREFIX}{member}::B[calls={callee}]"), member, case_b),
            vc(
                &format!("{CASE_PROPERTY_PREFIX}{member}::M[calls={callee},{callee}]"),
                member,
                case_m,
            ),
        ]
    }

    /// One reference's definitional VCs. `honest_b_arm = false` swaps the
    /// B arm for a CALL-FREE arm returning the un-spent budget — pointwise
    /// UNEQUAL to the model (the kernel-witnessed negative).
    fn ref_vcs(rname: &str, callee: &str, honest_b_arm: bool) -> Vec<VerificationCondition> {
        let k = || var("__fld_S_0", fuel_sort());
        let s_k = || fuel_ctor("S", vec![k()]);
        let base = Formula::forall(
            &[("e", e_sort())],
            Formula::Eq(
                Box::new(fnapp(rname, vec![fuel_ctor("Z", vec![]), var("e", e_sort())])),
                Box::new(mk_pair(fuel_ctor("Z", vec![]), var("e", e_sort()))),
            ),
        );
        let case_a = Formula::forall(
            &[("__fld_S_0", fuel_sort())],
            Formula::Eq(
                Box::new(fnapp(rname, vec![s_k(), e_ctor("A", vec![])])),
                Box::new(mk_pair(k(), e_ctor("A", vec![]))),
            ),
        );
        let x = || var("__fld_B_0", e_sort());
        let bcall = || fnapp(callee, vec![k(), x()]);
        let (case_b, b_calls) = if honest_b_arm {
            (
                Formula::forall(
                    &[("__fld_S_0", fuel_sort()), ("__fld_B_0", e_sort())],
                    Formula::Eq(
                        Box::new(fnapp(rname, vec![s_k(), e_ctor("B", vec![x()])])),
                        Box::new(mk_pair(fst_of(bcall()), e_ctor("B", vec![snd_of(bcall())]))),
                    ),
                ),
                format!("[calls={callee}]"),
            )
        } else {
            (
                Formula::forall(
                    &[("__fld_S_0", fuel_sort()), ("__fld_B_0", e_sort())],
                    Formula::Eq(
                        Box::new(fnapp(rname, vec![s_k(), e_ctor("B", vec![x()])])),
                        Box::new(mk_pair(k(), e_ctor("B", vec![x()]))),
                    ),
                ),
                "[calls=]".to_string(),
            )
        };
        let mx = || var("__fld_M_0", e_sort());
        let my = || var("__fld_M_1", e_sort());
        let mcall0 = || fnapp(callee, vec![k(), mx()]);
        let mcall1 = || fnapp(callee, vec![fst_of(mcall0()), my()]);
        let case_m = Formula::forall(
            &[("__fld_S_0", fuel_sort()), ("__fld_M_0", e_sort()), ("__fld_M_1", e_sort())],
            Formula::Eq(
                Box::new(fnapp(rname, vec![s_k(), e_ctor("M", vec![mx(), my()])])),
                Box::new(mk_pair(
                    fst_of(mcall1()),
                    e_ctor("M", vec![snd_of(mcall0()), snd_of(mcall1())]),
                )),
            ),
        );
        vec![
            vc(&format!("{REF_BASE_PROPERTY_PREFIX}{rname}"), rname, base),
            vc(&format!("{REF_STEP_PROPERTY_PREFIX}{rname}::A[calls=]"), rname, case_a),
            vc(&format!("{REF_STEP_PROPERTY_PREFIX}{rname}::B{b_calls}"), rname, case_b),
            vc(
                &format!("{REF_STEP_PROPERTY_PREFIX}{rname}::M[calls={callee},{callee}]"),
                rname,
                case_m,
            ),
        ]
    }

    fn conclusion_vc() -> VerificationCondition {
        let conj = |rname: &str| {
            Formula::forall(
                &[("fuel", fuel_sort()), ("e", e_sort())],
                Formula::Eq(
                    Box::new(var("_0", res_sort())),
                    Box::new(fnapp(rname, vec![var("fuel", fuel_sort()), var("e", e_sort())])),
                ),
            )
        };
        vc(
            &format!(
                "{CONCLUSION_PROPERTY_PREFIX}[threaded-induction:fuel=fuel::Fuel:Z|S;\
                 res=res::Res:Mk;data=expr::E;members=ft,gt;bases=2;cases=6;\
                 refs=fr,gr;refbases=2;refcases=6]"
            ),
            "ft+gt",
            Formula::And(vec![conj("fr"), conj("gr")]),
        )
    }

    fn true_bundle() -> Vec<VerificationCondition> {
        let mut vcs = Vec::new();
        vcs.extend(member_vcs("ft", "gt", "fr", "gr"));
        vcs.extend(member_vcs("gt", "ft", "gr", "fr"));
        vcs.extend(ref_vcs("fr", "gr", true));
        vcs.extend(ref_vcs("gr", "fr", true));
        vcs.push(conclusion_vc());
        vcs
    }

    fn wrong_ref_bundle() -> Vec<VerificationCondition> {
        let mut vcs = Vec::new();
        vcs.extend(member_vcs("ft", "gt", "fr", "gr"));
        vcs.extend(member_vcs("gt", "ft", "gr", "fr"));
        vcs.extend(ref_vcs("fr", "gr", false)); // fr's B arm skips the call
        vcs.extend(ref_vcs("gr", "fr", true));
        vcs.push(conclusion_vc());
        vcs
    }

    #[test]
    fn test_true_bundle_certifies() {
        let vcs = true_bundle();
        let evidence = certify_threaded_budget_functional(&vcs)
            .expect("the threaded model=reference bundle must certify");
        let trust_ir::ProofEvidence::CleanCic { term, context, lineage, .. } = &evidence else {
            panic!("expected CleanCic evidence");
        };
        assert!(recheck_threaded_budget_functional(&vcs, term, context, lineage));
    }

    #[test]
    fn test_threaded_induction_is_load_bearing() {
        assert!(
            threaded_induction_is_load_bearing(&true_bundle()),
            "the majorant induction must be accepted and the refl pseudo-proof rejected"
        );
    }

    #[test]
    fn test_wrong_reference_is_kernel_rejected() {
        assert!(
            certify_threaded_budget_functional(&wrong_ref_bundle()).is_none(),
            "a reference whose B arm returns the un-spent budget is pointwise unequal \
             to the threaded model — the kernel must reject the joint proof"
        );
    }

    #[test]
    fn test_tampered_term_fails_recheck() {
        let vcs = true_bundle();
        let evidence = certify_threaded_budget_functional(&vcs).expect("must certify");
        let trust_ir::ProofEvidence::CleanCic { term, context, lineage, .. } = evidence else {
            panic!("expected CleanCic evidence");
        };
        let mut tampered = term.clone();
        if let Some(byte) = tampered.last_mut() {
            *byte ^= 0x5a;
        }
        assert!(!recheck_threaded_budget_functional(&vcs, &tampered, &context, &lineage));
    }

    #[test]
    fn relineaged_ambient_sorry_beta_proof_context_and_vc_drift_are_rejected() {
        let vcs = true_bundle();
        let plan = parse_bundle(&vcs).expect("bundle parses");
        let env = plan.build_env().expect("minimal env");
        let goal = plan.goal();
        let proof = plan.proof().expect("canonical proof");
        let context = crate::canonical_empty_context_bytes().expect("canonical context");

        let mut ambient = env.clone();
        let sorry = crate::install_adversarial_trust_marker(&mut ambient, &goal)
            .expect("install adversarial trusted marker");
        assert!(kernel_checks_goal(&ambient, &sorry, &goal));
        let sorry_bytes = serialize_term(&sorry).expect("serialize sorry");
        let sorry_lineage =
            threaded_lineage_digest(&vcs, &sorry_bytes, &context, &plan.label).expect("lineage");
        assert!(!recheck_threaded_budget_functional(&vcs, &sorry_bytes, &context, &sorry_lineage,));

        let beta =
            Expr::app(Expr::lam(BinderInfo::Default, goal.clone(), Expr::bvar(0)), proof.clone());
        assert!(kernel_checks_goal(&env, &beta, &goal));
        let beta_bytes = serialize_term(&beta).expect("serialize beta proof");
        let beta_lineage =
            threaded_lineage_digest(&vcs, &beta_bytes, &context, &plan.label).expect("lineage");
        assert!(!recheck_threaded_budget_functional(&vcs, &beta_bytes, &context, &beta_lineage,));

        let term = serialize_term(&proof).expect("canonical proof");
        let mut noncanonical_context = context.clone();
        noncanonical_context.push(0);
        let relined = threaded_lineage_digest(&vcs, &term, &noncanonical_context, &plan.label)
            .expect("lineage");
        assert!(!recheck_threaded_budget_functional(&vcs, &term, &noncanonical_context, &relined,));

        let honest_lineage =
            threaded_lineage_digest(&vcs, &term, &context, &plan.label).expect("lineage");
        let mut drifted = vcs.clone();
        drifted[0].location.file = "different_source.rs".to_string();
        assert!(parse_bundle(&drifted).is_some());
        assert!(!recheck_threaded_budget_functional(&drifted, &term, &context, &honest_lineage,));
    }

    #[test]
    fn test_missing_case_fails_closed() {
        let mut vcs = true_bundle();
        vcs.remove(2); // drop ft's B case
        assert!(certify_threaded_budget_functional(&vcs).is_none());
    }
}
