// trust-certify: MUTUAL-SCC induction discharge lane (WALL C scaled to mutual).
//
// The sibling `recursive_datatype_functional` lane discharges the SELF-recursion
// (SCC-of-1) induction bundle by a generated `DT.rec` term. THIS lane consumes
// the MUTUAL bundle that trust-vcgen's `mutual_recursive_datatype_functional`
// lane emits for a fuel-indexed mutual cluster (a call-graph SCC of size N > 1
// — the shape of the kernel's `infer_type <-> whnf <-> is_def_eq` cluster,
// mirroring the Aristotle-proved template `MutualCluster.lean`) and
// machine-builds the JOINT discharge:
//
//   ONE induction on fuel (`Fuel.rec`) with a PRODUCT motive — the per-member
//   agreement statements conjoined (the template's `cluster_agrees_assembled`
//   AndType):
//     goal  : forall (n : Fuel), And (forall e, model_1 n e = rhs_1 n e)
//                                    (And ... (forall e, model_N n e = rhs_N n e))
//     proof : fun n => Fuel.rec
//               (motive := fun m => And (P_1 m) (.. (P_N m)))
//               <base leg: And.intro of per-member fuel-0 proofs
//                          (per-payload-constructor Eq.refl minors)>
//               <step leg: fun k ih => And.intro of per-member proofs whose
//                          call minors PROJECT the callee's component out of
//                          the product IH (And.left/And.right chains) and
//                          close by congruence — the cross-member IH edge>
//               n
//
// LITERAL-CLUSTER EXTENSIONS (the three named items, machine-built):
//   1. MULTI-IH CONSTRUCTORS (`Max`/`IMax(Level, Level)`): a payload
//      constructor may have SEVERAL recursive fields, so one step arm carries
//      several IH atoms. The discharge composes `congrArg` per call-result
//      OCCURRENCE, chained with `Eq.trans` — a per-occurrence one-hole
//      abstraction `fun x => T[.., x, ..]` rewrites the arm's result tree from
//      the model-call values to the callee-postcondition values, each step
//      justified by the RIGHT component of the product IH.
//   2. NON-DATATYPE (OPAQUE) PAYLOAD FIELDS (`Param(Name)`): a field whose
//      binder sort is a by-name uninterpreted `Sort::Datatype` distinct from
//      the fuel/payload datatypes is bound as an opaque atom. The kernel
//      carrier for each opaque sort is a dedicated TWO-constructor inductive
//      `__opaque_i : Type := mk0 | mk1`; proofs bind opaque values as lambda
//      parameters and never inspect them.
//      SOUNDNESS of the carrier choice: the bundle's semantics treats the
//      opaque sort as an arbitrary (nonempty) uninterpreted domain, so the
//      discharge must not exploit carrier specifics. The generated terms
//      contain no `__opaque_i` eliminators, and TWO constructors mean the
//      type is not unit-like: the kernel's definitional machinery can never
//      identify two DISTINCT opaque variables (no structure-eta collapse), so
//      a bundle equating distinct opaque atoms is kernel-REJECTED — witnessed
//      by `opaque_field_swap_is_rejected`.
//   3. FUNCTION-VS-FUNCTION POSTCONDITIONS (model = reference, the
//      `bootstrap_model_fidelity` shape): a member's postcondition
//      `Eq(_0, FnApp(ref, [fuel, e]))` names a REFERENCE function whose arm
//      structure travels in the bundle's `refbase`/`refstep` definitional
//      VCs. The reference cluster is rebuilt as a SECOND record-motive
//      `Fuel.rec` fold (`__RefModels`/`__ref_cluster`/`__ref_model_j`), the
//      goal becomes `Eq` of two folds, and the same induction discharges it —
//      base minors by `Eq.refl` (both folds iota-reduce on the pattern), call
//      minors by the congruence chain against `__ref_model_j k x`.
//
// GENERATED FROM THE BUNDLE (all machine-built):
//   1. the FUEL datatype (nat-shaped: Z | S Fuel), the opaque-field carriers,
//      and the PAYLOAD datatype are RECONSTRUCTED from the conclusion marker +
//      the case patterns and registered via `add_inductive`;
//   2. the member models are built as ONE `Fuel.rec` fold with a MODELS-record
//      motive (`__MutualModels`, one function field per member — the mutual
//      fixpoint encoded as a product, so member i's step body can call member
//      j's previous-fuel approximation through the record) and registered as
//      real kernel-checked `Definition`s; in function-vs-function mode the
//      REFERENCE cluster gets the same treatment;
//   3. the joint goal is proved by the generated mutual induction term above,
//      whose minor premises come 1:1 from the emitted base/case VCs — the
//      `[calls=..]` tag names WHICH component of the product IH each call
//      minor must project (member identity is load-bearing).
//
// NO MASQUERADE (kernel-witnessed):
//   * a WRONG postcondition on ANY ONE member parses and builds, and the clean
//     KERNEL rejects the generated joint proof — the WHOLE bundle fails (no
//     certificate); mutual induction is all-or-nothing;
//   * the refl-only pseudo-proof (no induction) is REJECTED while the
//     generated `Fuel.rec` proof is ACCEPTED (`mutual_induction_is_load_bearing`);
//   * projecting the WRONG component of the product IH (the caller's own
//     instead of the callee's) is REJECTED
//     (`cross_member_ih_is_load_bearing`) — the mutual edges are real;
//   * a two-IH arm wrong in ONE leg is REJECTED (`multi_ih` negative);
//   * a reference with COMMUTED call arguments is REJECTED (`ref_fn` negative).
//
// SOUNDNESS (fail-closed, never a false `Certified`):
//   * evidence is minted ONLY when the clean kernel certifies `proof : goal`
//     (`infer_only = false`), env = `init_eq` + `init_and` + the reconstructed
//     inductives + the model/reference definitions (no smuggled axioms),
//     closed context;
//   * canonical term + context + the FULL serialized VC bundle are
//     digest-bound; the DESERIALIZED payload is independently re-checked;
//   * every unsupported shape returns `None`.
//
// HONEST SCOPE — the mutual-cluster shape with multi-IH constructors, opaque
// payload fields, and model=reference postconditions: fuel-indexed members of
// uniform signature `(Fuel, E) -> E`. This certifies the reconstructed kernel
// model represented by the supplied typed VC bundle; absent a separate
// extraction/provenance bridge, it does NOT prove that bundle came from a
// literal Rust/TrustIR cluster. The literal
// `infer_type <-> whnf <-> is_def_eq` discharge additionally needs SN-vs-fuel
// (the real cluster's termination is SN-based; the fuel-indexed model is the
// extracted total shape) and extraction serialization — the named residuals.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::HashMap;

use clean_auto::bridge::ay_contract::{deserialize_term, serialize_term};
use clean_kernel::name::Name;
use clean_kernel::{
    BinderInfo, Constructor, Declaration, Environment, Expr, InductiveDecl, InductiveType, Level,
    LocalContext, TypeChecker,
};
use sha2::{Digest, Sha256};
use trust_types::{Formula, Sort, VcKind, VerificationCondition};

/// Lineage domain tag — distinct from every sibling lane.
const MUTUAL_FUNCTIONAL_LINEAGE_DOMAIN: &str =
    "trust-certify.cleancic.mutual-recursive-datatype-functional.v2";

/// Property-tag prefixes of the emitted bundle (kept in lockstep with
/// `trust-vcgen/src/mutual_recursive_datatype_functional.rs`; the integration
/// test drives the literal emitted VCs through this lane).
const BASE_PROPERTY_PREFIX: &str = "mutual_recursive_datatype_functional_base::";
const CASE_PROPERTY_PREFIX: &str = "mutual_recursive_datatype_functional_case::";
const CONCLUSION_PROPERTY_PREFIX: &str = "mutual_recursive_datatype_functional_conclusion";
const REF_BASE_PROPERTY_PREFIX: &str = "mutual_recursive_datatype_functional_refbase::";
const REF_STEP_PROPERTY_PREFIX: &str = "mutual_recursive_datatype_functional_refstep::";

// ---------------------------------------------------------------------------
// Bundle parsing: VCs -> mutual induction plan.
// ---------------------------------------------------------------------------

/// The kind of one payload-constructor field.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum FieldKind {
    /// A recursive field (the payload datatype itself).
    Rec,
    /// An opaque field — index into [`MutualPlan::opaques`].
    Opaque(usize),
}

/// A parsed arm-result term. Leaves are the arm's pattern fields or its call
/// results (member arms: the `__ih_j` variables; reference arms: the
/// definitional `FnApp` applications).
#[derive(Clone, Debug)]
enum Tree {
    Field(usize),
    /// The result of the arm's call `j` (index into [`GenArm::calls`]).
    Call(usize),
    Node {
        ctor: String,
        args: Vec<Tree>,
    },
}

/// One cluster/reference call inside an arm.
#[derive(Clone, Copy, Debug)]
struct ArmCall {
    /// Callee index (into the member list for member arms, into the
    /// reference list for reference arms).
    callee: usize,
    /// The arm field the call recurses on (a `Rec` field).
    field: usize,
}

/// One parsed per-payload-constructor arm (base or step; member or reference).
struct GenArm {
    /// Constructor name (from the property tag, cross-checked). Empty for a
    /// reference's direct-base pseudo-arm.
    #[allow(dead_code)]
    ctor: String,
    /// Pattern field variable names, in binder order.
    #[allow(dead_code)]
    fields: Vec<String>,
    calls: Vec<ArmCall>,
    result: Tree,
}

/// One member's/reference's base (fuel = 0) leg.
enum BaseLeg {
    /// A single direct-return VC: `Field(0)` in the tree denotes the payload
    /// variable itself.
    Direct(Tree),
    /// Per-constructor arms, in payload-constructor order.
    PerCtor(Vec<GenArm>),
}

/// A member's postcondition right-hand side.
enum Rhs {
    /// `rhs(e)` — a constructor tree over the payload variable.
    CtorTree(Formula),
    /// `FnApp(ref, [fuel, e])` — the model=reference shape; index into
    /// [`MutualPlan::refs`].
    RefFn(usize),
}

/// One cluster member's parsed plan.
struct MemberPlan {
    /// The payload variable name of the member's conclusion conjunct.
    e_var: String,
    rhs: Rhs,
    base: BaseLeg,
    /// Step arms in payload-constructor order.
    steps: Vec<GenArm>,
}

/// One REFERENCE function's parsed plan (function-vs-function mode).
struct RefPlan {
    #[allow(dead_code)]
    name: String,
    base: BaseLeg,
    steps: Vec<GenArm>,
}

/// The parsed mutual induction plan for one bundle.
struct MutualPlan {
    /// Kernel-safe (last `::` segment) fuel / payload datatype names.
    fuel: String,
    fuel_z: String,
    fuel_s: String,
    data: String,
    /// Payload constructors `(name, field kinds)` in declaration (case) order.
    ctors: Vec<(String, Vec<FieldKind>)>,
    /// Full opaque field sort names, in interning order — opaque sort `k`'s
    /// kernel carrier is the inductive `__opaque_k`.
    opaques: Vec<String>,
    /// Members in bundle (canonical) order.
    members: Vec<MemberPlan>,
    /// Reference functions (empty outside function-vs-function mode).
    refs: Vec<RefPlan>,
    /// Stable label material: member names + property tags + conclusion.
    label: String,
}

/// Split a `Forall` into (binders, body); a bare formula has no binders.
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

/// `true` iff `f` is a Var/Ctor term whose variables all come from `allowed`.
fn is_term_over(f: &Formula, allowed: &[&str]) -> bool {
    if let Some(name) = f.var_name() {
        return allowed.contains(&name);
    }
    match f {
        Formula::Ctor { args, .. } => args.iter().all(|a| is_term_over(a, allowed)),
        _ => false,
    }
}

fn formula_mentions_var(f: &Formula, x: &str) -> bool {
    if f.var_name() == Some(x) {
        return true;
    }
    match f {
        Formula::Ctor { args, .. } => args.iter().any(|a| formula_mentions_var(a, x)),
        _ => false,
    }
}

/// Match `rhs` (a term over the variable `x`) against an instance; return the
/// term substituted for `x`. All occurrences must agree; constructor spines
/// must match exactly. (Shared shape with the self-recursion lane.)
fn match_scrutinee(rhs: &Formula, inst: &Formula, x: &str) -> Option<Formula> {
    fn go(rhs: &Formula, inst: &Formula, x: &str, out: &mut Option<Formula>) -> bool {
        if rhs.var_name() == Some(x) {
            return match out {
                Some(prev) => prev == inst,
                None => {
                    *out = Some(inst.clone());
                    true
                }
            };
        }
        match (rhs, inst) {
            (
                Formula::Ctor { ctor: c1, args: a1, .. },
                Formula::Ctor { ctor: c2, args: a2, .. },
            ) => {
                c1 == c2 && a1.len() == a2.len() && a1.iter().zip(a2).all(|(r, i)| go(r, i, x, out))
            }
            _ => rhs == inst,
        }
    }
    let mut out = None;
    if go(rhs, inst, x, &mut out) { out } else { None }
}

/// Validate an arm-instance side against `rhs[x := Ctor(ctor, fields)]`
/// WITHOUT constructing sort-carrying formulas: when `rhs` mentions `x` the
/// substituted pattern is recovered by matching and compared field-by-field
/// (variable names only); when `rhs` is ground the instance must equal `rhs`.
fn instance_matches_pattern(
    rhs: &Formula,
    inst: &Formula,
    x: &str,
    ctor: &str,
    fields: &[String],
) -> bool {
    if !formula_mentions_var(rhs, x) {
        return inst == rhs;
    }
    let Some(pattern) = match_scrutinee(rhs, inst, x) else {
        return false;
    };
    let Formula::Ctor { ctor: pc, args, .. } = &pattern else {
        return false;
    };
    pc == ctor
        && args.len() == fields.len()
        && args.iter().zip(fields).all(|(a, f)| a.var_name() == Some(f.as_str()))
}

/// The `[mutual-induction:..]` conclusion marker, parsed.
struct Marker {
    fuel_full: String,
    fuel_z: String,
    fuel_s: String,
    data_full: String,
    member_names: Vec<String>,
    bases: usize,
    cases: usize,
    /// Function-vs-function mode: reference names + refbase/refstep counts.
    refs: Vec<String>,
    refbases: usize,
    refcases: usize,
    ref_mode: bool,
}

fn parse_marker(property: &str) -> Option<Marker> {
    let marker = property.strip_prefix(CONCLUSION_PROPERTY_PREFIX)?;
    let marker = marker.strip_prefix("[mutual-induction:")?.strip_suffix(']')?;
    let mut fuel_full = None;
    let mut fuel_ctors = None;
    let mut data_full = None;
    let mut member_names: Option<Vec<String>> = None;
    let mut bases = None;
    let mut cases = None;
    let mut refs: Option<Vec<String>> = None;
    let mut refbases = None;
    let mut refcases = None;
    for field in marker.split(';') {
        let (key, value) = field.split_once('=')?;
        match key {
            "fuel" => {
                let (dt, ctors) = value.rsplit_once(':')?;
                let (z, s) = ctors.split_once('|')?;
                fuel_full = Some(dt.to_string());
                fuel_ctors = Some((z.to_string(), s.to_string()));
            }
            "data" => data_full = Some(value.to_string()),
            "members" => {
                member_names = Some(value.split(',').map(str::to_string).collect());
            }
            "bases" => bases = value.parse().ok(),
            "cases" => cases = value.parse().ok(),
            "refs" => refs = Some(value.split(',').map(str::to_string).collect()),
            "refbases" => refbases = value.parse().ok(),
            "refcases" => refcases = value.parse().ok(),
            _ => return None,
        }
    }
    let (fuel_z, fuel_s) = fuel_ctors?;
    // The three reference fields travel together or not at all.
    let ref_mode = refs.is_some();
    if ref_mode != refbases.is_some() || ref_mode != refcases.is_some() {
        return None;
    }
    Some(Marker {
        fuel_full: fuel_full?,
        fuel_z,
        fuel_s,
        data_full: data_full?,
        member_names: member_names?,
        bases: bases?,
        cases: cases?,
        refs: refs.unwrap_or_default(),
        refbases: refbases.unwrap_or(0),
        refcases: refcases.unwrap_or(0),
        ref_mode,
    })
}

/// Kernel-safe short name: nonempty last `::` segment, identifier-shaped.
fn short_name(full: &str) -> Option<String> {
    let seg = full.rsplit("::").next()?;
    (!seg.is_empty() && seg.chars().all(|c| c.is_alphanumeric() || c == '_'))
        .then(|| seg.to_string())
}

/// One member's/reference's raw VC partitions (bundle order preserved).
#[derive(Default)]
struct RawMember<'a> {
    /// `(ctor_tag_or_None_for_direct, vc)`.
    bases: Vec<(Option<&'a str>, &'a VerificationCondition)>,
    /// `(ctor_tag, calls, vc)`.
    cases: Vec<(&'a str, Vec<&'a str>, &'a VerificationCondition)>,
}

fn member_entry<'b>(raw: &mut Vec<(String, RawMember<'b>)>, name: &str) -> usize {
    if let Some(i) = raw.iter().position(|(n, _)| n == name) {
        i
    } else {
        raw.push((name.to_string(), RawMember::default()));
        raw.len() - 1
    }
}

/// Classify one arm binder sort against the marker's datatypes. `Opaque`
/// interns the by-name sort into `opaques` (first-seen order).
fn classify_field_sort(
    sort: &Sort,
    marker: &Marker,
    opaques: &mut Vec<String>,
) -> Option<FieldKind> {
    let Sort::Datatype { name, .. } = sort else {
        return None;
    };
    if name == &marker.data_full {
        return Some(FieldKind::Rec);
    }
    if name == &marker.fuel_full {
        return None; // a fuel-typed payload field is out of scope
    }
    short_name(name)?; // opaque sorts must be kernel-shortable
    let idx = if let Some(i) = opaques.iter().position(|n| n == name) {
        i
    } else {
        opaques.push(name.clone());
        opaques.len() - 1
    };
    Some(FieldKind::Opaque(idx))
}

/// Partitioned binders of one arm VC.
struct ArmBinders {
    /// The step arm's fuel binder name (`None` for base arms).
    k_name: Option<String>,
    /// `(name, kind)` per pattern field, in binder order.
    fields: Vec<(String, FieldKind)>,
    /// IH variable names, in binder order (member step arms only).
    ihs: Vec<String>,
}

fn partition_binders(
    binders: &[(String, Sort)],
    marker: &Marker,
    opaques: &mut Vec<String>,
) -> Option<ArmBinders> {
    let mut k_name = None;
    let mut fields = Vec::new();
    let mut ihs = Vec::new();
    for (name, sort) in binders {
        if is_datatype_sort(sort, &marker.fuel_full) {
            if k_name.replace(name.clone()).is_some() {
                return None; // at most one fuel binder
            }
        } else if name.starts_with("__ih") {
            // IH result variables are payload-typed.
            if !is_datatype_sort(sort, &marker.data_full) {
                return None;
            }
            ihs.push(name.clone());
        } else {
            fields.push((name.clone(), classify_field_sort(sort, marker, opaques)?));
        }
    }
    Some(ArmBinders { k_name, fields, ihs })
}

/// The kind a result (sub)tree inhabits: `Rec` for calls and constructor
/// nodes, the field's own kind for a field leaf.
fn tree_kind(t: &Tree, fields: &[(String, FieldKind)]) -> Option<FieldKind> {
    match t {
        Tree::Field(p) => fields.get(*p).map(|(_, k)| *k),
        Tree::Call(_) | Tree::Node { .. } => Some(FieldKind::Rec),
    }
}

/// Parse a result formula into a [`Tree`]. `call_leaf` resolves a candidate
/// call leaf (member arms: an `__ih_j` variable; reference arms: a
/// definitional `FnApp`) to its call index — outer `None` fails the parse,
/// inner `None` means "not a call leaf". Node constructors must be payload
/// constructors applied at exact arity with kind-correct arguments; opaque
/// positions must be opaque field leaves of the SAME opaque sort.
fn parse_tree(
    f: &Formula,
    fields: &[(String, FieldKind)],
    ctors: &[(String, Vec<FieldKind>)],
    call_leaf: &mut dyn FnMut(&Formula) -> Option<Option<usize>>,
) -> Option<Tree> {
    if let Some(j) = call_leaf(f)? {
        return Some(Tree::Call(j));
    }
    if let Some(name) = f.var_name() {
        let p = fields.iter().position(|(n, _)| n == name)?;
        return Some(Tree::Field(p));
    }
    let Formula::Ctor { ctor, args, .. } = f else {
        return None;
    };
    let (_, kinds) = ctors.iter().find(|(c, _)| c == ctor)?;
    if args.len() != kinds.len() {
        return None;
    }
    let mut out_args = Vec::with_capacity(args.len());
    for (arg, kind) in args.iter().zip(kinds) {
        let t = parse_tree(arg, fields, ctors, call_leaf)?;
        if tree_kind(&t, fields)? != *kind {
            return None;
        }
        out_args.push(t);
    }
    Some(Tree::Node { ctor: ctor.clone(), args: out_args })
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum ArmKind {
    Base,
    Step,
}

/// Check a member VC's postcondition INSTANCE (the conclusion side of an arm)
/// against the member's rhs at the given fuel/payload instantiation.
/// `payload_pattern`: `Some((ctor, fields))` for per-constructor arms, `None`
/// for the direct-base payload variable itself.
#[allow(clippy::too_many_arguments)]
fn rhs_instance_matches(
    rhs: &Rhs,
    rhs_inst: &Formula,
    e_var: &str,
    marker: &Marker,
    refs_names: &[String],
    kind: ArmKind,
    k_name: Option<&str>,
    payload_pattern: Option<(&str, &[String])>,
) -> bool {
    match rhs {
        Rhs::CtorTree(rhs_f) => match payload_pattern {
            Some((ctor, fields)) => instance_matches_pattern(rhs_f, rhs_inst, e_var, ctor, fields),
            None => rhs_inst == rhs_f,
        },
        Rhs::RefFn(r) => {
            let Formula::FnApp { func, args, .. } = rhs_inst else {
                return false;
            };
            if func != &refs_names[*r] {
                return false;
            }
            let [fuel_inst, payload_inst] = args.as_slice() else {
                return false;
            };
            let fuel_ok = match kind {
                ArmKind::Base => {
                    matches!(fuel_inst, Formula::Ctor { ctor, args, .. }
                        if ctor == &marker.fuel_z && args.is_empty())
                }
                ArmKind::Step => match (fuel_inst, k_name) {
                    (Formula::Ctor { ctor, args, .. }, Some(k)) => {
                        ctor == &marker.fuel_s && args.len() == 1 && args[0].var_name() == Some(k)
                    }
                    _ => false,
                },
            };
            if !fuel_ok {
                return false;
            }
            match payload_pattern {
                Some((ctor, fields)) => {
                    matches!(payload_inst, Formula::Ctor { ctor: pc, args: pa, .. }
                        if pc == ctor
                            && pa.len() == fields.len()
                            && pa.iter().zip(fields).all(|(a, f)| a.var_name() == Some(f.as_str())))
                }
                None => payload_inst.var_name() == Some(e_var),
            }
        }
    }
}

/// Parse one MEMBER per-constructor arm VC (base or step).
#[allow(clippy::too_many_arguments)]
fn parse_member_arm(
    formula: &Formula,
    ctor: &str,
    kinds: &[FieldKind],
    calls_tag: &[&str],
    e_var: &str,
    rhs: &Rhs,
    member_rhss: &[(String, Rhs)],
    member_names: &[&str],
    refs_names: &[String],
    marker: &Marker,
    opaques: &mut Vec<String>,
    ctors: &[(String, Vec<FieldKind>)],
    kind: ArmKind,
) -> Option<GenArm> {
    let (binders, body) = split_forall(formula);
    let ab = partition_binders(&binders, marker, opaques)?;
    match kind {
        ArmKind::Base => {
            if ab.k_name.is_some() || !calls_tag.is_empty() || !ab.ihs.is_empty() {
                return None;
            }
        }
        ArmKind::Step => {
            if ab.k_name.is_none() {
                return None;
            }
        }
    }
    let field_kinds: Vec<FieldKind> = ab.fields.iter().map(|(_, k)| *k).collect();
    if field_kinds != kinds || ab.ihs.len() != calls_tag.len() {
        return None;
    }
    let field_names: Vec<String> = ab.fields.iter().map(|(n, _)| n.clone()).collect();

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

    // Conclusion instance: `Eq(result, rhs @ [fuel := Z / S k, e := pattern])`.
    let Formula::Eq(result, rhs_inst) = concl else {
        return None;
    };
    if !rhs_instance_matches(
        rhs,
        rhs_inst,
        e_var,
        marker,
        refs_names,
        kind,
        ab.k_name.as_deref(),
        Some((ctor, &field_names)),
    ) {
        return None;
    }

    // IH atoms: atom j is the CALLEE's postcondition at the smaller fuel.
    let mut calls = Vec::with_capacity(calls_tag.len());
    for ((call, ih_name), atom) in calls_tag.iter().zip(&ab.ihs).zip(&atoms) {
        let callee = member_names.iter().position(|m| m == call)?;
        let Formula::Eq(ih_var, atom_rhs) = atom else {
            return None;
        };
        if ih_var.var_name() != Some(ih_name.as_str()) {
            return None;
        }
        let (callee_e, callee_rhs) = &member_rhss[callee];
        let field = match callee_rhs {
            Rhs::CtorTree(crhs) => {
                if formula_mentions_var(crhs, callee_e) {
                    let arg = match_scrutinee(crhs, atom_rhs, callee_e)?;
                    let name = arg.var_name()?;
                    ab.fields.iter().position(|(n, _)| n == name)?
                } else {
                    // Ground callee rhs: the recursed-on field is not
                    // recoverable from the atom; supported only when the arm
                    // has exactly one recursive field.
                    if atom_rhs.as_ref() != crhs {
                        return None;
                    }
                    let mut rec_fields =
                        ab.fields.iter().enumerate().filter(|(_, (_, k))| *k == FieldKind::Rec);
                    let (idx, _) = rec_fields.next()?;
                    if rec_fields.next().is_some() {
                        return None;
                    }
                    idx
                }
            }
            Rhs::RefFn(r) => {
                let Formula::FnApp { func, args, .. } = atom_rhs.as_ref() else {
                    return None;
                };
                if func != &refs_names[*r] {
                    return None;
                }
                let [k_arg, field_arg] = args.as_slice() else {
                    return None;
                };
                if k_arg.var_name() != ab.k_name.as_deref() {
                    return None;
                }
                let name = field_arg.var_name()?;
                ab.fields.iter().position(|(n, _)| n == name)?
            }
        };
        if ab.fields[field].1 != FieldKind::Rec {
            return None;
        }
        calls.push(ArmCall { callee, field });
    }

    // Result tree: leaves are pattern fields and IH variables.
    let ihs = ab.ihs.clone();
    let result_tree = parse_tree(result, &ab.fields, ctors, &mut |f| match f.var_name() {
        Some(name) if name.starts_with("__ih") => Some(Some(ihs.iter().position(|n| n == name)?)),
        _ => Some(None),
    })?;
    if tree_kind(&result_tree, &ab.fields)? != FieldKind::Rec {
        return None;
    }
    Some(GenArm { ctor: ctor.to_string(), fields: field_names, calls, result: result_tree })
}

/// Parse one REFERENCE definitional arm VC:
/// `Forall [k?, fields] Eq(FnApp(r, [Z | S k, pattern]), result)`.
#[allow(clippy::too_many_arguments)]
fn parse_ref_arm(
    formula: &Formula,
    ref_name: &str,
    ref_idx_of: &dyn Fn(&str) -> Option<usize>,
    ctor: Option<(&str, &[FieldKind])>,
    calls_tag: &[&str],
    refs_names: &[String],
    marker: &Marker,
    opaques: &mut Vec<String>,
    ctors: &[(String, Vec<FieldKind>)],
    kind: ArmKind,
) -> Option<GenArm> {
    let (binders, body) = split_forall(formula);
    let ab = partition_binders(&binders, marker, opaques)?;
    match kind {
        ArmKind::Base => {
            if ab.k_name.is_some() {
                return None;
            }
        }
        ArmKind::Step => {
            if ab.k_name.is_none() {
                return None;
            }
        }
    }
    if !ab.ihs.is_empty() {
        return None; // definitional arms carry no IHs
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
    let fuel_ok = match kind {
        ArmKind::Base => matches!(fuel_inst, Formula::Ctor { ctor, args, .. }
            if ctor == &marker.fuel_z && args.is_empty()),
        ArmKind::Step => match (fuel_inst, ab.k_name.as_deref()) {
            (Formula::Ctor { ctor, args, .. }, Some(k)) => {
                ctor == &marker.fuel_s && args.len() == 1 && args[0].var_name() == Some(k)
            }
            _ => false,
        },
    };
    if !fuel_ok {
        return None;
    }

    let (arm_ctor, fields_for_tree): (String, Vec<(String, FieldKind)>) = match ctor {
        Some((c, kinds)) => {
            let field_kinds: Vec<FieldKind> = ab.fields.iter().map(|(_, k)| *k).collect();
            if field_kinds != kinds {
                return None;
            }
            let names: Vec<&str> = ab.fields.iter().map(|(n, _)| n.as_str()).collect();
            let ok = matches!(payload_inst, Formula::Ctor { ctor: pc, args: pa, .. }
                if pc == c
                    && pa.len() == names.len()
                    && pa.iter().zip(&names).all(|(a, f)| a.var_name() == Some(*f)));
            if !ok {
                return None;
            }
            (c.to_string(), ab.fields.clone())
        }
        None => {
            // Direct base: exactly one payload binder, matched as the variable.
            let [(name, FieldKind::Rec)] = ab.fields.as_slice() else {
                return None;
            };
            if payload_inst.var_name() != Some(name.as_str()) {
                return None;
            }
            (String::new(), vec![(name.clone(), FieldKind::Rec)])
        }
    };

    // Result tree: leaves are pattern fields; a definitional
    // `FnApp(callee, [k, field])` becomes a call (deduplicated by
    // (callee, field), first-occurrence order).
    let mut calls: Vec<ArmCall> = Vec::new();
    let k_name = ab.k_name.clone();
    let result_tree = {
        let calls_ref = &mut calls;
        let fields = &fields_for_tree;
        parse_tree(result, fields, ctors, &mut |f| {
            let Formula::FnApp { func, args, .. } = f else {
                return Some(None);
            };
            // Calls only exist under S k (the base arms are call-free).
            let k = k_name.as_deref()?;
            let callee = ref_idx_of(func)?;
            let [k_arg, field_arg] = args.as_slice() else {
                return None;
            };
            if k_arg.var_name() != Some(k) {
                return None;
            }
            let fname = field_arg.var_name()?;
            let field = fields.iter().position(|(n, _)| n == fname)?;
            if fields[field].1 != FieldKind::Rec {
                return None;
            }
            let j = if let Some(j) =
                calls_ref.iter().position(|c| c.callee == callee && c.field == field)
            {
                j
            } else {
                calls_ref.push(ArmCall { callee, field });
                calls_ref.len() - 1
            };
            Some(Some(j))
        })?
    };
    if tree_kind(&result_tree, &fields_for_tree)? != FieldKind::Rec {
        return None;
    }
    // The `[calls=..]` tag pins the call list (callee names, in order).
    let tag_ok = calls.len() == calls_tag.len()
        && calls.iter().zip(calls_tag).all(|(c, t)| refs_names[c.callee] == *t);
    if !tag_ok {
        return None;
    }
    let field_names = fields_for_tree.iter().map(|(n, _)| n.clone()).collect();
    Some(GenArm { ctor: arm_ctor, fields: field_names, calls, result: result_tree })
}

/// Parse the emitted mutual bundle into a plan. `None` (fail-closed) on any
/// shape outside the supported scope.
#[allow(clippy::too_many_lines)]
fn parse_bundle(vcs: &[VerificationCondition]) -> Option<MutualPlan> {
    // 1. Split base / case / refbase / refstep / conclusion VCs by tag.
    let mut conclusion: Option<&VerificationCondition> = None;
    let mut raw: Vec<(String, RawMember)> = Vec::new();
    let mut raw_refs: Vec<(String, RawMember)> = Vec::new();
    let mut properties: Vec<String> = Vec::new();
    for vc in vcs {
        let VcKind::FunctionalCorrectness { property, context } = &vc.kind else {
            return None;
        };
        properties.push(property.clone());
        if let Some(rest) = property.strip_prefix(BASE_PROPERTY_PREFIX) {
            let (member, ctor) = match rest.split_once("::") {
                Some((m, c)) => (m, Some(c)),
                None => (rest, None),
            };
            if context != member {
                return None;
            }
            let i = member_entry(&mut raw, member);
            raw[i].1.bases.push((ctor, vc));
        } else if let Some(rest) = property.strip_prefix(CASE_PROPERTY_PREFIX) {
            let (member, rest) = rest.split_once("::")?;
            let rest = rest.strip_suffix(']')?;
            let (ctor, calls) = rest.split_once("[calls=")?;
            let calls: Vec<&str> =
                if calls.is_empty() { Vec::new() } else { calls.split(',').collect() };
            if context != member {
                return None;
            }
            let i = member_entry(&mut raw, member);
            raw[i].1.cases.push((ctor, calls, vc));
        } else if let Some(rest) = property.strip_prefix(REF_BASE_PROPERTY_PREFIX) {
            let (rname, ctor) = match rest.split_once("::") {
                Some((r, c)) => (r, Some(c)),
                None => (rest, None),
            };
            if context != rname {
                return None;
            }
            let i = member_entry(&mut raw_refs, rname);
            raw_refs[i].1.bases.push((ctor, vc));
        } else if let Some(rest) = property.strip_prefix(REF_STEP_PROPERTY_PREFIX) {
            let (rname, rest) = rest.split_once("::")?;
            let rest = rest.strip_suffix(']')?;
            let (ctor, calls) = rest.split_once("[calls=")?;
            let calls: Vec<&str> =
                if calls.is_empty() { Vec::new() } else { calls.split(',').collect() };
            if context != rname {
                return None;
            }
            let i = member_entry(&mut raw_refs, rname);
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

    // 2. The conclusion marker MUST match the bundle exactly (member set and
    //    order, base/case counts, reference set and counts) — coverage is
    //    part of the plan.
    let VcKind::FunctionalCorrectness { property: c_prop, .. } = &conclusion.kind else {
        return None;
    };
    let marker = parse_marker(c_prop)?;
    if marker.member_names.len() < 2 {
        return None;
    }
    {
        let mut sorted = marker.member_names.clone();
        sorted.sort();
        sorted.dedup();
        if sorted.len() != marker.member_names.len() {
            return None;
        }
    }
    let bundle_order: Vec<&str> = raw.iter().map(|(n, _)| n.as_str()).collect();
    let marker_order: Vec<&str> = marker.member_names.iter().map(String::as_str).collect();
    if bundle_order != marker_order {
        return None;
    }
    if raw.iter().map(|(_, m)| m.bases.len()).sum::<usize>() != marker.bases
        || raw.iter().map(|(_, m)| m.cases.len()).sum::<usize>() != marker.cases
    {
        return None;
    }
    // Reference set: order and counts pinned by the marker; names disjoint
    // from the member set.
    if marker.ref_mode {
        let mut sorted = marker.refs.clone();
        sorted.sort();
        sorted.dedup();
        if sorted.len() != marker.refs.len() || marker.refs.is_empty() {
            return None;
        }
        if marker.refs.iter().any(|r| marker.member_names.contains(r)) {
            return None;
        }
    }
    let ref_bundle_order: Vec<&str> = raw_refs.iter().map(|(n, _)| n.as_str()).collect();
    let ref_marker_order: Vec<&str> = marker.refs.iter().map(String::as_str).collect();
    if ref_bundle_order != ref_marker_order {
        return None;
    }
    if raw_refs.iter().map(|(_, m)| m.bases.len()).sum::<usize>() != marker.refbases
        || raw_refs.iter().map(|(_, m)| m.cases.len()).sum::<usize>() != marker.refcases
    {
        return None;
    }
    let fuel = short_name(&marker.fuel_full)?;
    let data = short_name(&marker.data_full)?;
    if fuel == data || marker.fuel_z == marker.fuel_s {
        return None;
    }

    // 3. The conclusion formula: one `Forall [fuel, e] Eq(_0, rhs)` conjunct
    //    per member, in member order. `rhs` is a constructor tree over `e`
    //    (original mode) or `FnApp(ref, [fuel, e])` (function-vs-function).
    let Formula::And(conjuncts) = &conclusion.formula else {
        return None;
    };
    if conjuncts.len() != marker.member_names.len() {
        return None;
    }
    let mut rhss: Vec<(String, Rhs)> = Vec::with_capacity(conjuncts.len());
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
        let parsed = if marker.ref_mode {
            let Formula::FnApp { func, args, .. } = rhs.as_ref() else {
                return None;
            };
            let r = marker.refs.iter().position(|n| n == func)?;
            let [a_fuel, a_e] = args.as_slice() else {
                return None;
            };
            if a_fuel.var_name() != Some(fuel_var.as_str())
                || a_e.var_name() != Some(e_var.as_str())
            {
                return None;
            }
            Rhs::RefFn(r)
        } else {
            let rhs = rhs.as_ref().clone();
            if !is_term_over(&rhs, &[e_var.as_str()]) {
                return None;
            }
            Rhs::CtorTree(rhs)
        };
        rhss.push((e_var.clone(), parsed));
    }

    // 4. The payload constructor list `(name, field kinds)`: from the FIRST
    //    member's step cases; every member and reference must present the
    //    SAME ordered list. Opaque sorts are interned in first-seen order.
    let mut opaques: Vec<String> = Vec::new();
    let mut ctors: Vec<(String, Vec<FieldKind>)> = Vec::new();
    for (ctor, _, vc) in &raw[0].1.cases {
        let (binders, _) = split_forall(&vc.formula);
        let ab = partition_binders(&binders, &marker, &mut opaques)?;
        ctors.push(((*ctor).to_string(), ab.fields.iter().map(|(_, k)| *k).collect()));
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

    // 5. Parse each member's arms against its rhs.
    let member_names: Vec<&str> = marker.member_names.iter().map(String::as_str).collect();
    let mut members: Vec<MemberPlan> = Vec::with_capacity(raw.len());
    for ((_name, rm), (e_var, rhs)) in raw.iter().zip(&rhss) {
        // Coverage + tag order for the step arms.
        if rm.cases.len() != ctors.len()
            || !rm.cases.iter().zip(&ctors).all(|((tag, _, _), (c, _))| tag == c)
        {
            return None;
        }
        // Base leg.
        let base = match rm.bases.as_slice() {
            [(None, vc)] => {
                let (binders, body) = split_forall(&vc.formula);
                let [(b_e, b_sort)] = binders.as_slice() else {
                    return None;
                };
                if b_e != e_var || !is_datatype_sort(b_sort, &marker.data_full) {
                    return None;
                }
                let Formula::Eq(result, rhs_inst) = body else {
                    return None;
                };
                if !rhs_instance_matches(
                    rhs,
                    rhs_inst,
                    e_var,
                    &marker,
                    &marker.refs,
                    ArmKind::Base,
                    None,
                    None,
                ) {
                    return None;
                }
                let fields = vec![(e_var.clone(), FieldKind::Rec)];
                let tree = parse_tree(result, &fields, &ctors, &mut |_| Some(None))?;
                if tree_kind(&tree, &fields)? != FieldKind::Rec {
                    return None;
                }
                BaseLeg::Direct(tree)
            }
            bases => {
                if bases.len() != ctors.len() {
                    return None;
                }
                let mut arms = Vec::with_capacity(bases.len());
                for ((ctor, kinds), (tag, vc)) in ctors.iter().zip(bases) {
                    if tag.as_deref() != Some(ctor.as_str()) {
                        return None;
                    }
                    arms.push(parse_member_arm(
                        &vc.formula,
                        ctor,
                        kinds,
                        &[],
                        e_var,
                        rhs,
                        &rhss,
                        &member_names,
                        &marker.refs,
                        &marker,
                        &mut opaques,
                        &ctors,
                        ArmKind::Base,
                    )?);
                }
                BaseLeg::PerCtor(arms)
            }
        };
        // Step leg.
        let mut steps = Vec::with_capacity(rm.cases.len());
        for ((ctor, kinds), (tag, calls, vc)) in ctors.iter().zip(&rm.cases) {
            if tag != ctor {
                return None;
            }
            steps.push(parse_member_arm(
                &vc.formula,
                ctor,
                kinds,
                calls,
                e_var,
                rhs,
                &rhss,
                &member_names,
                &marker.refs,
                &marker,
                &mut opaques,
                &ctors,
                ArmKind::Step,
            )?);
        }
        let rhs = match rhs {
            Rhs::CtorTree(f) => Rhs::CtorTree(f.clone()),
            Rhs::RefFn(r) => Rhs::RefFn(*r),
        };
        members.push(MemberPlan { e_var: e_var.clone(), rhs, base, steps });
    }

    // 6. Parse each reference's definitional arms (function-vs-function mode).
    let refs_names = marker.refs.clone();
    let ref_idx_of = |name: &str| refs_names.iter().position(|n| n == name);
    let mut refs: Vec<RefPlan> = Vec::with_capacity(raw_refs.len());
    for (rname, rr) in &raw_refs {
        if rr.cases.len() != ctors.len()
            || !rr.cases.iter().zip(&ctors).all(|((tag, _, _), (c, _))| tag == c)
        {
            return None;
        }
        let base = match rr.bases.as_slice() {
            [(None, vc)] => BaseLeg::Direct(
                parse_ref_arm(
                    &vc.formula,
                    rname,
                    &ref_idx_of,
                    None,
                    &[],
                    &refs_names,
                    &marker,
                    &mut opaques,
                    &ctors,
                    ArmKind::Base,
                )?
                .result,
            ),
            bases => {
                if bases.len() != ctors.len() {
                    return None;
                }
                let mut arms = Vec::with_capacity(bases.len());
                for ((ctor, kinds), (tag, vc)) in ctors.iter().zip(bases) {
                    if tag.as_deref() != Some(ctor.as_str()) {
                        return None;
                    }
                    arms.push(parse_ref_arm(
                        &vc.formula,
                        rname,
                        &ref_idx_of,
                        Some((ctor, kinds)),
                        &[],
                        &refs_names,
                        &marker,
                        &mut opaques,
                        &ctors,
                        ArmKind::Base,
                    )?);
                }
                BaseLeg::PerCtor(arms)
            }
        };
        let mut steps = Vec::with_capacity(rr.cases.len());
        for ((ctor, kinds), (tag, calls, vc)) in ctors.iter().zip(&rr.cases) {
            if tag != ctor {
                return None;
            }
            steps.push(parse_ref_arm(
                &vc.formula,
                rname,
                &ref_idx_of,
                Some((ctor, kinds)),
                calls,
                &refs_names,
                &marker,
                &mut opaques,
                &ctors,
                ArmKind::Step,
            )?);
        }
        refs.push(RefPlan { name: rname.clone(), base, steps });
    }

    let label = format!(
        "mutual_recursive_datatype_functional:{}:[{}]:{:?}",
        marker.member_names.join("+"),
        properties.join(";"),
        conclusion.formula
    );
    Some(MutualPlan {
        fuel,
        fuel_z: marker.fuel_z.clone(),
        fuel_s: marker.fuel_s.clone(),
        data,
        ctors,
        opaques,
        members,
        refs,
        label,
    })
}

// ---------------------------------------------------------------------------
// CIC construction (raw kernel Expr, de Bruijn indices).
// ---------------------------------------------------------------------------

/// `Type 0 = Sort 1` — `Eq`/`Eq.refl`/`congrArg` over the payload take `u = 1`.
fn level1() -> Level {
    Level::succ(Level::zero())
}

/// The wrong-IH-projection mode of the generated proof (negative control).
#[derive(Clone, Copy, PartialEq, Eq)]
enum ProjectionMode {
    /// Project the CALLEE's component of the product IH (the real proof).
    Callee,
    /// Project the CALLER's own component (must be kernel-rejected).
    CallerSelf,
}

/// Which cluster fold a construction targets.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Side {
    Model,
    Ref,
}

impl Side {
    fn record(self) -> &'static str {
        match self {
            Side::Model => "__MutualModels",
            Side::Ref => "__RefModels",
        }
    }

    fn prefix(self) -> &'static str {
        match self {
            Side::Model => "__mutual",
            Side::Ref => "__ref",
        }
    }
}

impl MutualPlan {
    fn n(&self, side: Side) -> usize {
        match side {
            Side::Model => self.members.len(),
            Side::Ref => self.refs.len(),
        }
    }

    fn side_base(&self, side: Side, i: usize) -> &BaseLeg {
        match side {
            Side::Model => &self.members[i].base,
            Side::Ref => &self.refs[i].base,
        }
    }

    fn side_steps(&self, side: Side, i: usize) -> &[GenArm] {
        match side {
            Side::Model => &self.members[i].steps,
            Side::Ref => &self.refs[i].steps,
        }
    }

    fn fuel_expr(&self) -> Expr {
        Expr::const_(Name::from_string(&self.fuel), Vec::new())
    }

    fn data_expr(&self) -> Expr {
        Expr::const_(Name::from_string(&self.data), Vec::new())
    }

    fn fuel_z_expr(&self) -> Expr {
        Expr::const_(Name::from_string(&format!("{}.{}", self.fuel, self.fuel_z)), Vec::new())
    }

    fn fuel_s_expr(&self) -> Expr {
        Expr::const_(Name::from_string(&format!("{}.{}", self.fuel, self.fuel_s)), Vec::new())
    }

    fn opaque_name(&self, k: usize) -> String {
        format!("__opaque_{k}")
    }

    fn opaque_expr(&self, k: usize) -> Expr {
        Expr::const_(Name::from_string(&self.opaque_name(k)), Vec::new())
    }

    fn field_ty_expr(&self, kind: FieldKind) -> Expr {
        match kind {
            FieldKind::Rec => self.data_expr(),
            FieldKind::Opaque(k) => self.opaque_expr(k),
        }
    }

    fn ctor_kinds(&self, ctor: &str) -> Option<&[FieldKind]> {
        self.ctors.iter().find(|(c, _)| c == ctor).map(|(_, k)| k.as_slice())
    }

    fn e_ctor(&self, ctor: &str) -> Option<Expr> {
        // Only the payload datatype's own constructors are nameable.
        self.ctor_kinds(ctor)?;
        Some(Expr::const_(Name::from_string(&format!("{}.{ctor}", self.data)), Vec::new()))
    }

    fn record_expr(&self, side: Side) -> Expr {
        Expr::const_(Name::from_string(side.record()), Vec::new())
    }

    fn mk_expr(&self, side: Side) -> Expr {
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

    /// `E -> E`.
    fn efn(&self) -> Expr {
        Expr::pi(BinderInfo::Default, self.data_expr(), self.data_expr())
    }

    /// `Eq.{1} E a b`.
    fn eq_e(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(Expr::const_(Name::from_string("Eq"), vec![level1()]), [self.data_expr(), a, b])
    }

    /// `Eq.refl.{1} E t`.
    fn refl(&self, t: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.refl"), vec![level1()]),
            [self.data_expr(), t],
        )
    }

    /// Convert a bundle Var/Ctor term to CIC; `env` maps variable names to
    /// already-depth-adjusted expressions.
    fn term_to_cic(&self, f: &Formula, env: &HashMap<String, Expr>) -> Option<Expr> {
        if let Some(name) = f.var_name() {
            return env.get(name).cloned();
        }
        match f {
            Formula::Ctor { ctor, args, .. } => {
                let mut expr = self.e_ctor(ctor)?;
                for arg in args {
                    expr = Expr::app(expr, self.term_to_cic(arg, env)?);
                }
                Some(expr)
            }
            _ => None,
        }
    }

    /// Member i's postcondition rhs at (`fuel`, `t`), both already at the
    /// current depth: the instantiated constructor tree, or the REFERENCE
    /// model's application `__ref_model_r fuel t`.
    fn rhs_cic(&self, i: usize, fuel: &Expr, t: &Expr) -> Option<Expr> {
        let member = &self.members[i];
        match &member.rhs {
            Rhs::CtorTree(rhs) => {
                let mut env = HashMap::new();
                env.insert(member.e_var.clone(), t.clone());
                self.term_to_cic(rhs, &env)
            }
            Rhs::RefFn(r) => {
                Some(Expr::apps(self.model_expr(Side::Ref, *r), [fuel.clone(), t.clone()]))
            }
        }
    }

    /// Member i's agreement statement
    /// `forall e, model_i <fuel> e = rhs_i <fuel> e`. `fuel_inside` must
    /// already be valid INSIDE the `forall e` binder.
    fn p_member(&self, i: usize, fuel_inside: &Expr) -> Option<Expr> {
        let model_app =
            Expr::apps(self.model_expr(Side::Model, i), [fuel_inside.clone(), Expr::bvar(0)]);
        let rhs = self.rhs_cic(i, fuel_inside, &Expr::bvar(0))?;
        Some(Expr::pi(BinderInfo::Default, self.data_expr(), self.eq_e(model_app, rhs)))
    }

    /// Right-nested conjunction `And p1 (And p2 (.. pN))`.
    fn and_chain(&self, props: &[Expr]) -> Expr {
        let and_const = Expr::const_(Name::from_string("And"), Vec::new());
        let mut iter = props.iter().rev();
        let mut acc = iter.next().expect("and_chain over >= 1 props").clone();
        for p in iter {
            acc = Expr::apps(and_const.clone(), [p.clone(), acc]);
        }
        acc
    }

    /// `And.intro` chain packaging per-member proofs into the product.
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

    /// Component `j` of a right-nested product proof `h : And p1 (.. pN)`.
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

    /// The reconstructed FUEL inductive: `inductive Fuel | z | s (k : Fuel)`.
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

    /// The kernel carrier of opaque sort `k`: `inductive __opaque_k : Type
    /// where | mk0 | mk1`.
    ///
    /// SOUNDNESS: TWO nullary constructors, deliberately. The bundle's
    /// semantics treats the sort as an arbitrary uninterpreted domain; the
    /// generated proofs never eliminate the carrier, so the only way the
    /// kernel could exploit a specific carrier is definitional collapse — and
    /// a unit-like (single-constructor) carrier WOULD collapse (structure eta
    /// identifies all its values), silently certifying bundles that equate
    /// distinct opaque atoms. Two constructors keep distinct opaque variables
    /// definitionally distinct (`opaque_field_swap_is_rejected`).
    fn opaque_inductive(&self, k: usize) -> InductiveDecl {
        let o = self.opaque_expr(k);
        let name = self.opaque_name(k);
        InductiveDecl {
            level_params: vec![],
            num_params: 0,
            types: vec![InductiveType {
                name: Name::from_string(&name),
                type_: Expr::type_(),
                constructors: vec![
                    Constructor {
                        name: Name::from_string(&format!("{name}.mk0")),
                        type_: o.clone(),
                    },
                    Constructor { name: Name::from_string(&format!("{name}.mk1")), type_: o },
                ],
            }],
        }
    }

    /// The reconstructed PAYLOAD inductive (recursive / opaque fields).
    fn data_inductive(&self) -> InductiveDecl {
        let data = self.data_expr();
        let constructors = self
            .ctors
            .iter()
            .map(|(ctor, kinds)| Constructor {
                name: Name::from_string(&format!("{}.{ctor}", self.data)),
                type_: kinds.iter().rev().fold(data.clone(), |acc, kind| {
                    Expr::pi(BinderInfo::Default, self.field_ty_expr(*kind), acc)
                }),
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

    /// The MODELS record for `side`: one `(E -> E)` field per member — the
    /// mutual fixpoint's product carrier.
    fn models_inductive(&self, side: Side) -> InductiveDecl {
        let mut ctor_ty = self.record_expr(side);
        for _ in 0..self.n(side) {
            ctor_ty = Expr::pi(BinderInfo::Default, self.efn(), ctor_ty);
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

    /// `<side>_proj_i : Record -> E -> E` (field projection via `Record.rec`).
    fn proj_def(&self, side: Side, i: usize) -> Declaration {
        let motive = Expr::lam(BinderInfo::Default, self.record_expr(side), self.efn());
        let mut minor = Expr::bvar((self.n(side) - 1 - i) as u32);
        for _ in 0..self.n(side) {
            minor = Expr::lam(BinderInfo::Default, self.efn(), minor);
        }
        let rec = Expr::apps(
            Expr::const_(Name::from_string(&format!("{}.rec", side.record())), vec![level1()]),
            [motive, minor, Expr::bvar(0)],
        );
        Declaration::Definition {
            name: Name::from_string(&format!("{}_proj_{i}", side.prefix())),
            level_params: vec![],
            type_: Expr::pi(BinderInfo::Default, self.record_expr(side), self.efn()),
            value: Expr::lam(BinderInfo::Default, self.record_expr(side), rec),
            is_reducible: true,
        }
    }

    /// Instantiate a result tree: `fields[p]` / `calls[j]` are the leaf
    /// expressions, already at the current depth (every occurrence of call
    /// `j` gets the same value).
    fn tree_to_cic(&self, t: &Tree, fields: &[Expr], calls: &[Expr]) -> Option<Expr> {
        match t {
            Tree::Field(p) => fields.get(*p).cloned(),
            Tree::Call(j) => calls.get(*j).cloned(),
            Tree::Node { ctor, args } => {
                let mut expr = self.e_ctor(ctor)?;
                for arg in args {
                    expr = Expr::app(expr, self.tree_to_cic(arg, fields, calls)?);
                }
                Some(expr)
            }
        }
    }

    /// Instantiate a result tree with PER-OCCURRENCE call values (DFS
    /// left-to-right order) — the congruence chain's endpoints.
    fn tree_to_cic_occ(&self, t: &Tree, fields: &[Expr], occ_vals: &[Expr]) -> Option<Expr> {
        fn go(
            plan: &MutualPlan,
            t: &Tree,
            fields: &[Expr],
            occ_vals: &[Expr],
            counter: &mut usize,
        ) -> Option<Expr> {
            match t {
                Tree::Field(p) => fields.get(*p).cloned(),
                Tree::Call(_) => {
                    let v = occ_vals.get(*counter).cloned();
                    *counter += 1;
                    v
                }
                Tree::Node { ctor, args } => {
                    let mut expr = plan.e_ctor(ctor)?;
                    for arg in args {
                        expr = Expr::app(expr, go(plan, arg, fields, occ_vals, counter)?);
                    }
                    Some(expr)
                }
            }
        }
        let mut counter = 0usize;
        let expr = go(self, t, fields, occ_vals, &mut counter)?;
        (counter == occ_vals.len()).then_some(expr)
    }

    /// λ-wrap `body_at(depth)` in a `.rec` minor's binders: the constructor's
    /// fields first, then one IH per RECURSIVE field, in field order (the
    /// kernel recursor's minor shape). `outer` is the binder depth at which
    /// the minor sits; `eih_ty_at(d, x)` forms the IH binder's type at depth
    /// `d` for the recursive field variable `x` (valid at depth `d`).
    fn wrap_minor(
        &self,
        kinds: &[FieldKind],
        outer: usize,
        eih_ty_at: &dyn Fn(usize, &Expr) -> Option<Expr>,
        body_at: &dyn Fn(usize) -> Option<Expr>,
    ) -> Option<Expr> {
        let a = kinds.len();
        let recs: Vec<usize> = kinds
            .iter()
            .enumerate()
            .filter(|(_, k)| matches!(k, FieldKind::Rec))
            .map(|(p, _)| p)
            .collect();
        let depth = outer + a + recs.len();
        let mut expr = body_at(depth)?;
        for (q, &p) in recs.iter().enumerate().rev() {
            let ty_depth = outer + a + q;
            let x = Expr::bvar((ty_depth - 1 - (outer + p)) as u32);
            expr = Expr::lam(BinderInfo::Default, eih_ty_at(ty_depth, &x)?, expr);
        }
        for p in (0..a).rev() {
            expr = Expr::lam(BinderInfo::Default, self.field_ty_expr(kinds[p]), expr);
        }
        Some(expr)
    }

    /// One member's fuel-0 model body `fun (e : E) => ..` (closed).
    fn base_model_body(&self, side: Side, i: usize) -> Option<Expr> {
        match self.side_base(side, i) {
            BaseLeg::Direct(tree) => {
                let body = self.tree_to_cic(tree, &[Expr::bvar(0)], &[])?;
                Some(Expr::lam(BinderInfo::Default, self.data_expr(), body))
            }
            BaseLeg::PerCtor(arms) => {
                let motive = Expr::lam(BinderInfo::Default, self.data_expr(), self.data_expr());
                let mut rec_args = vec![motive];
                for (arm, (_, kinds)) in arms.iter().zip(&self.ctors) {
                    if !arm.calls.is_empty() {
                        return None; // base arms carry no calls
                    }
                    // Minor sits under λ(e) — outer depth 1. The eih binders
                    // (motive `fun _ => E`) have constant type E.
                    let outer = 1usize;
                    rec_args.push(self.wrap_minor(
                        kinds,
                        outer,
                        &|_, _| Some(self.data_expr()),
                        &|depth| {
                            let fields: Vec<Expr> = (0..kinds.len())
                                .map(|p| Expr::bvar((depth - 1 - (outer + p)) as u32))
                                .collect();
                            self.tree_to_cic(&arm.result, &fields, &[])
                        },
                    )?);
                }
                rec_args.push(Expr::bvar(0));
                let rec = Expr::apps(
                    Expr::const_(Name::from_string(&format!("{}.rec", self.data)), vec![level1()]),
                    rec_args,
                );
                Some(Expr::lam(BinderInfo::Default, self.data_expr(), rec))
            }
        }
    }

    /// One member's fuel-(S k) model body, under binders `k : Fuel` (level 0)
    /// and `ih : Record` (level 1): `fun (e : E) => E.rec .. e` where call
    /// leaves apply the CALLEE's projection of `ih` — the mutual edge.
    fn step_model_body(&self, side: Side, i: usize) -> Option<Expr> {
        let motive = Expr::lam(BinderInfo::Default, self.data_expr(), self.data_expr());
        let mut rec_args = vec![motive];
        for (arm, (_, kinds)) in self.side_steps(side, i).iter().zip(&self.ctors) {
            // Minor sits under k(0), ih(1), e(2) — outer depth 3.
            let outer = 3usize;
            rec_args.push(self.wrap_minor(
                kinds,
                outer,
                &|_, _| Some(self.data_expr()),
                &|depth| {
                    let fields: Vec<Expr> = (0..kinds.len())
                        .map(|p| Expr::bvar((depth - 1 - (outer + p)) as u32))
                        .collect();
                    let ih = Expr::bvar((depth - 1 - 1) as u32);
                    let calls: Vec<Expr> = arm
                        .calls
                        .iter()
                        .map(|c| {
                            Expr::apps(
                                self.proj_expr(side, c.callee),
                                [ih.clone(), fields[c.field].clone()],
                            )
                        })
                        .collect();
                    self.tree_to_cic(&arm.result, &fields, &calls)
                },
            )?);
        }
        rec_args.push(Expr::bvar(0));
        let rec = Expr::apps(
            Expr::const_(Name::from_string(&format!("{}.rec", self.data)), vec![level1()]),
            rec_args,
        );
        Some(Expr::lam(BinderInfo::Default, self.data_expr(), rec))
    }

    /// `<side>_cluster : Fuel -> Record` — ONE `Fuel.rec` fold whose motive
    /// is the models record: the whole cluster as a product.
    fn cluster_def(&self, side: Side) -> Option<Declaration> {
        let motive = Expr::lam(BinderInfo::Default, self.fuel_expr(), self.record_expr(side));
        let mz = Expr::apps(
            self.mk_expr(side),
            (0..self.n(side)).map(|i| self.base_model_body(side, i)).collect::<Option<Vec<_>>>()?,
        );
        let ms_body = Expr::apps(
            self.mk_expr(side),
            (0..self.n(side)).map(|i| self.step_model_body(side, i)).collect::<Option<Vec<_>>>()?,
        );
        let ms = Expr::lam(
            BinderInfo::Default,
            self.fuel_expr(),
            Expr::lam(BinderInfo::Default, self.record_expr(side), ms_body),
        );
        let rec = Expr::apps(
            Expr::const_(Name::from_string(&format!("{}.rec", self.fuel)), vec![level1()]),
            [motive, mz, ms, Expr::bvar(0)],
        );
        Some(Declaration::Definition {
            name: Name::from_string(&format!("{}_cluster", side.prefix())),
            level_params: vec![],
            type_: Expr::pi(BinderInfo::Default, self.fuel_expr(), self.record_expr(side)),
            value: Expr::lam(BinderInfo::Default, self.fuel_expr(), rec),
            is_reducible: true,
        })
    }

    /// `<side>_model_i : Fuel -> E -> E := fun n e => proj_i (cluster n) e`.
    fn model_def(&self, side: Side, i: usize) -> Declaration {
        let body = Expr::apps(
            self.proj_expr(side, i),
            [Expr::app(self.cluster_expr(side), Expr::bvar(1)), Expr::bvar(0)],
        );
        Declaration::Definition {
            name: Name::from_string(&format!("{}_model_{i}", side.prefix())),
            level_params: vec![],
            type_: Expr::pi(
                BinderInfo::Default,
                self.fuel_expr(),
                Expr::pi(BinderInfo::Default, self.data_expr(), self.data_expr()),
            ),
            value: Expr::lam(
                BinderInfo::Default,
                self.fuel_expr(),
                Expr::lam(BinderInfo::Default, self.data_expr(), body),
            ),
            is_reducible: true,
        }
    }

    /// Build the kernel environment: `Eq` family, `And`, the reconstructed
    /// fuel/opaque/payload inductives, and — per side — the models record,
    /// projections, the cluster fold, and the per-member model definitions
    /// (each `add_*` is itself kernel-checked; any failure fails the mint).
    fn build_env(&self) -> Option<Environment> {
        let mut env = Environment::default();
        env.init_eq().ok()?;
        env.init_and().ok()?;
        env.add_inductive(self.fuel_inductive()).ok()?;
        for k in 0..self.opaques.len() {
            env.add_inductive(self.opaque_inductive(k)).ok()?;
        }
        env.add_inductive(self.data_inductive()).ok()?;
        let mut sides = vec![Side::Model];
        if !self.refs.is_empty() {
            // The REFERENCE fold must exist before the goal references it.
            sides.insert(0, Side::Ref);
        }
        for side in sides {
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

    /// The joint goal — the template's `cluster_agrees` statement:
    /// `forall (n : Fuel), And (P_1 n) (.. (P_N n))`.
    fn goal(&self) -> Option<Expr> {
        let props = (0..self.n(Side::Model))
            .map(|i| self.p_member(i, &Expr::bvar(1)))
            .collect::<Option<Vec<_>>>()?;
        Some(Expr::pi(BinderInfo::Default, self.fuel_expr(), self.and_chain(&props)))
    }

    /// One member's BASE-leg proof (fuel = 0), at outer depth 1 (under `n`).
    fn base_leg_proof(&self, i: usize) -> Option<Expr> {
        let z = self.fuel_z_expr();
        // The original direct-return shortcut: with a constructor-tree rhs a
        // direct base reduces on the FREE payload variable, so a plain refl
        // lambda suffices. Everything else — per-constructor bases, and ALL
        // function-vs-function bundles (the reference fold may be stuck on
        // the variable) — inducts on the payload.
        if matches!(&self.members[i].rhs, Rhs::CtorTree(_))
            && matches!(self.side_base(Side::Model, i), BaseLeg::Direct(_))
        {
            let rhs = self.rhs_cic(i, &z, &Expr::bvar(0))?;
            return Some(Expr::lam(BinderInfo::Default, self.data_expr(), self.refl(rhs)));
        }
        // fun (e : E) => E.rec.{0}
        //   (motive := fun y => model_i z y = rhs_i z y) <refl minors> e
        let motive_body = self.eq_e(
            Expr::apps(self.model_expr(Side::Model, i), [z.clone(), Expr::bvar(0)]),
            self.rhs_cic(i, &z, &Expr::bvar(0))?,
        );
        let motive = Expr::lam(BinderInfo::Default, self.data_expr(), motive_body);
        let mut rec_args = vec![motive];
        for (ctor, kinds) in &self.ctors {
            // Minor sits under n(0), e(1) — outer depth 2.
            let outer = 2usize;
            let eih_ty = |_d: usize, x: &Expr| {
                Some(self.eq_e(
                    Expr::apps(self.model_expr(Side::Model, i), [z.clone(), x.clone()]),
                    self.rhs_cic(i, &z, x)?,
                ))
            };
            let body = |depth: usize| {
                let inst = Expr::apps(
                    self.e_ctor(ctor)?,
                    (0..kinds.len()).map(|p| Expr::bvar((depth - 1 - (outer + p)) as u32)),
                );
                Some(self.refl(self.rhs_cic(i, &z, &inst)?))
            };
            rec_args.push(self.wrap_minor(kinds, outer, &eih_ty, &body)?);
        }
        rec_args.push(Expr::bvar(0));
        let rec = Expr::apps(
            Expr::const_(Name::from_string(&format!("{}.rec", self.data)), vec![Level::zero()]),
            rec_args,
        );
        Some(Expr::lam(BinderInfo::Default, self.data_expr(), rec))
    }

    /// One member's STEP-leg proof, at outer depth 3 (under `n`, `k`, `ih`):
    /// `fun (e : E) => E.rec.{0} (motive := fun y => model_i (s k) y = rhs_i (s k) y)
    ///    <minors: refl / congruence chain over the projected product IH> e`.
    /// `mode` selects the real (callee) projection or the deliberately wrong
    /// caller-self projection (the cross-member negative control).
    #[allow(clippy::too_many_lines)]
    fn step_leg_proof(&self, i: usize, mode: ProjectionMode) -> Option<Expr> {
        // k sits at level 1 (binders: n(0), k(1), ih(2), then e, ...).
        let k_at = |at: usize| Expr::bvar((at - 1 - 1) as u32);
        let s_k_at = |at: usize| Expr::app(self.fuel_s_expr(), k_at(at));
        let ih_at = |at: usize| Expr::bvar((at - 1 - 2) as u32);

        // Motive: under λe (level 3) and its own λy (level 4) — depth 5.
        let motive_body = self.eq_e(
            Expr::apps(self.model_expr(Side::Model, i), [s_k_at(5), Expr::bvar(0)]),
            self.rhs_cic(i, &s_k_at(5), &Expr::bvar(0))?,
        );
        let motive = Expr::lam(BinderInfo::Default, self.data_expr(), motive_body);

        let mut rec_args = vec![motive];
        for (arm, (ctor, kinds)) in self.side_steps(Side::Model, i).iter().zip(&self.ctors) {
            // Minor sits under n(0), k(1), ih(2), e(3) — outer depth 4.
            let outer = 4usize;
            let field_at = |p: usize, at: usize| Expr::bvar((at - 1 - (outer + p)) as u32);
            let eih_ty = |d: usize, x: &Expr| {
                Some(self.eq_e(
                    Expr::apps(self.model_expr(Side::Model, i), [s_k_at(d), x.clone()]),
                    self.rhs_cic(i, &s_k_at(d), x)?,
                ))
            };
            let body = |depth: usize| -> Option<Expr> {
                // Call-result occurrences, DFS order.
                fn occurrences(t: &Tree, out: &mut Vec<usize>) {
                    match t {
                        Tree::Field(_) => {}
                        Tree::Call(j) => out.push(*j),
                        Tree::Node { args, .. } => {
                            for a in args {
                                occurrences(a, out);
                            }
                        }
                    }
                }
                let mut occs = Vec::new();
                occurrences(&arm.result, &mut occs);

                if occs.is_empty() {
                    let inst = Expr::apps(
                        self.e_ctor(ctor)?,
                        (0..kinds.len()).map(|p| field_at(p, depth)),
                    );
                    return Some(self.refl(self.rhs_cic(i, &s_k_at(depth), &inst)?));
                }

                let callee_of = |t: usize| match mode {
                    ProjectionMode::Callee => arm.calls[occs[t]].callee,
                    ProjectionMode::CallerSelf => i,
                };
                let field_of = |t: usize| arm.calls[occs[t]].field;
                // Occurrence t's model-call value and callee-postcondition
                // value, formed at depth `at`.
                let u_at = |t: usize, at: usize| {
                    Expr::apps(
                        self.model_expr(Side::Model, callee_of(t)),
                        [k_at(at), field_at(field_of(t), at)],
                    )
                };
                let v_at = |t: usize, at: usize| {
                    self.rhs_cic(callee_of(t), &k_at(at), &field_at(field_of(t), at))
                };
                let fields_at =
                    |at: usize| (0..kinds.len()).map(|p| field_at(p, at)).collect::<Vec<_>>();
                // The product IH's components at depth `at`: inside each
                // P_j's own binder, k sits one deeper.
                let props_at = |at: usize| {
                    (0..self.n(Side::Model))
                        .map(|j| self.p_member(j, &Expr::bvar((at - 1) as u32)))
                        .collect::<Option<Vec<_>>>()
                };
                // h_t : model_c k x = rhs_c k x — the projected component
                // applied at the recursed-on field.
                let h_at = |t: usize, at: usize| {
                    Some(Expr::app(
                        self.and_component(&props_at(at)?, callee_of(t), ih_at(at)),
                        field_at(field_of(t), at),
                    ))
                };
                let m = occs.len();
                // T with occurrences < filled rewritten to the callee values.
                let endpoint = |filled: usize, at: usize| -> Option<Expr> {
                    let occ_vals = (0..m)
                        .map(|t| if t < filled { v_at(t, at) } else { Some(u_at(t, at)) })
                        .collect::<Option<Vec<_>>>()?;
                    self.tree_to_cic_occ(&arm.result, &fields_at(at), &occ_vals)
                };
                // congrArg step t: one-hole abstraction over occurrence t.
                let cong = |t: usize| -> Option<Expr> {
                    let at1 = depth + 1;
                    let occ_vals = (0..m)
                        .map(|s| {
                            if s < t {
                                v_at(s, at1)
                            } else if s == t {
                                Some(Expr::bvar(0))
                            } else {
                                Some(u_at(s, at1))
                            }
                        })
                        .collect::<Option<Vec<_>>>()?;
                    let lam_body = self.tree_to_cic_occ(&arm.result, &fields_at(at1), &occ_vals)?;
                    Some(Expr::apps(
                        Expr::const_(Name::from_string("congrArg"), vec![level1(), level1()]),
                        [
                            self.data_expr(),
                            self.data_expr(),
                            u_at(t, depth),
                            v_at(t, depth)?,
                            Expr::lam(BinderInfo::Default, self.data_expr(), lam_body),
                            h_at(t, depth)?,
                        ],
                    ))
                };
                let mut acc = cong(0)?;
                for t in 1..m {
                    acc = Expr::apps(
                        Expr::const_(Name::from_string("Eq.trans"), vec![level1()]),
                        [
                            self.data_expr(),
                            endpoint(0, depth)?,
                            endpoint(t, depth)?,
                            endpoint(t + 1, depth)?,
                            acc,
                            cong(t)?,
                        ],
                    );
                }
                Some(acc)
            };
            rec_args.push(self.wrap_minor(kinds, outer, &eih_ty, &body)?);
        }
        rec_args.push(Expr::bvar(0));
        let rec = Expr::apps(
            Expr::const_(Name::from_string(&format!("{}.rec", self.data)), vec![Level::zero()]),
            rec_args,
        );
        Some(Expr::lam(BinderInfo::Default, self.data_expr(), rec))
    }

    /// The GENERATED joint mutual-induction proof — the template's
    /// `cluster_agrees_assembled` shape:
    /// `fun (n : Fuel) => Fuel.rec.{0}
    ///     (motive := fun m => And (P_1 m) (.. (P_N m)))
    ///     <base intro-chain> (fun k ih => <step intro-chain>) n`.
    fn proof_with(&self, mode: ProjectionMode) -> Option<Expr> {
        let n = self.n(Side::Model);
        // motive: binders n(0), m(1) — inside each P_i, m -> bvar 1.
        let motive_props =
            (0..n).map(|i| self.p_member(i, &Expr::bvar(1))).collect::<Option<Vec<_>>>()?;
        let motive =
            Expr::lam(BinderInfo::Default, self.fuel_expr(), self.and_chain(&motive_props));

        // Base leg (outer depth 1): P_i at the closed fuel-zero constructor.
        let base_props =
            (0..n).map(|i| self.p_member(i, &self.fuel_z_expr())).collect::<Option<Vec<_>>>()?;
        let base_proofs = (0..n).map(|i| self.base_leg_proof(i)).collect::<Option<Vec<_>>>()?;
        let base = self.intro_chain(&base_props, &base_proofs);

        // Step leg: fun (k : Fuel) (ih : And (P_1 k) ..) => intro-chain.
        // ih TYPE at depth 2: k at level 1 -> bvar 1 inside each P_i.
        let ih_props =
            (0..n).map(|i| self.p_member(i, &Expr::bvar(1))).collect::<Option<Vec<_>>>()?;
        let ih_ty = self.and_chain(&ih_props);
        // Step conclusion props at depth 3: P_i (s k), k at level 1 -> bvar 2.
        let step_props = (0..n)
            .map(|i| self.p_member(i, &Expr::app(self.fuel_s_expr(), Expr::bvar(2))))
            .collect::<Option<Vec<_>>>()?;
        let step_proofs =
            (0..n).map(|i| self.step_leg_proof(i, mode)).collect::<Option<Vec<_>>>()?;
        let step_body = self.intro_chain(&step_props, &step_proofs);
        let step = Expr::lam(
            BinderInfo::Default,
            self.fuel_expr(),
            Expr::lam(BinderInfo::Default, ih_ty, step_body),
        );

        let rec = Expr::apps(
            Expr::const_(Name::from_string(&format!("{}.rec", self.fuel)), vec![Level::zero()]),
            [motive, base, step, Expr::bvar(0)],
        );
        Some(Expr::lam(BinderInfo::Default, self.fuel_expr(), rec))
    }

    fn proof(&self) -> Option<Expr> {
        self.proof_with(ProjectionMode::Callee)
    }

    /// The refl-only PSEUDO-proof `fun n => intro-chain of
    /// (fun e => Eq.refl E (model_i n e))` — well-typed, but each leg's type is
    /// `model_i n e = model_i n e`, NOT the goal (`model_i n e` is stuck on the
    /// free `n`). The kernel must reject it against the goal.
    fn refl_only_pseudo_proof(&self) -> Option<Expr> {
        let n = self.n(Side::Model);
        let props = (0..n).map(|i| self.p_member(i, &Expr::bvar(1))).collect::<Option<Vec<_>>>()?;
        let proofs: Vec<Expr> = (0..n)
            .map(|i| {
                let model_ne =
                    Expr::apps(self.model_expr(Side::Model, i), [Expr::bvar(1), Expr::bvar(0)]);
                Expr::lam(BinderInfo::Default, self.data_expr(), self.refl(model_ne))
            })
            .collect();
        Some(Expr::lam(BinderInfo::Default, self.fuel_expr(), self.intro_chain(&props, &proofs)))
    }

    /// `true` iff some step arm's call targets a DIFFERENT member (the wrong-
    /// projection control is only meaningful for genuinely mutual bundles).
    fn has_cross_member_call(&self) -> bool {
        self.members
            .iter()
            .enumerate()
            .any(|(i, m)| m.steps.iter().any(|arm| arm.calls.iter().any(|c| c.callee != i)))
    }
}

/// Full kernel re-check (`infer_only = false`) that `term : goal` in the empty
/// closed context.
fn kernel_checks_goal(env: &Environment, term: &Expr, goal: &Expr) -> bool {
    TypeChecker::with_context(env, LocalContext::new()).check_type(term, goal).is_ok()
}

/// SHA-256 lineage digest binding term, context, and the bundle label.
fn mutual_functional_lineage_digest(
    vcs: &[VerificationCondition],
    term_bytes: &[u8],
    context_bytes: &[u8],
    label: &str,
) -> Option<trust_ir::ProofDigest> {
    let encoded_vcs = bincode::serialize(vcs).ok()?;
    let mut hasher = Sha256::new();
    hasher.update(MUTUAL_FUNCTIONAL_LINEAGE_DOMAIN.as_bytes());
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

/// Mint a kernel-CHECKED `CleanCic` certificate discharging a MUTUAL-cluster
/// induction bundle (the VCs emitted by trust-vcgen's
/// `mutual_recursive_datatype_functional` lane) by ONE generated `Fuel.rec`
/// induction term with a PRODUCT motive (the per-member statements conjoined).
///
/// Fail-closed on every count: unsupported bundle shapes parse to `None`; a
/// false postcondition on ANY member makes the clean kernel REJECT the joint
/// proof (the whole bundle — mutual induction is all-or-nothing); the
/// serialized payload must re-check after a round-trip.
#[must_use]
pub fn certify_mutual_recursive_datatype_functional(
    vcs: &[VerificationCondition],
) -> Option<trust_ir::ProofEvidence> {
    let plan = parse_bundle(vcs)?;
    let env = plan.build_env()?;
    let goal = plan.goal()?;
    let proof = plan.proof()?;

    // TCB gate: the clean kernel independently type-checks the joint term.
    if !kernel_checks_goal(&env, &proof, &goal) {
        return None;
    }

    let term_bytes = serialize_term(&proof).ok()?;
    let context_bytes = crate::canonical_empty_context_bytes()?;
    let lineage = mutual_functional_lineage_digest(vcs, &term_bytes, &context_bytes, &plan.label)?;
    if !recheck_mutual_recursive_datatype_functional(vcs, &term_bytes, &context_bytes, &lineage) {
        return None;
    }

    Some(trust_ir::ProofEvidence::CleanCic {
        term: term_bytes,
        context: context_bytes,
        lineage,
        kernel_recheck: None,
    })
}

/// Consumer-side re-check: independently re-parse the bundle, rebuild env +
/// goal, deserialize the term, re-run the clean-kernel check, and re-bind the
/// lineage digest. A tampered term or swapped lineage fails closed.
#[must_use]
pub fn recheck_mutual_recursive_datatype_functional(
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
    mutual_functional_lineage_digest(vcs, term_bytes, context_bytes, &plan.label).as_ref()
        == Some(lineage)
}

/// LOAD-BEARING-INDUCTION witness: `true` iff the generated `Fuel.rec` joint
/// proof is ACCEPTED and the refl-only pseudo-proof (no induction, no IH) is
/// REJECTED by the kernel. The mutual twin of the self-recursion lane's
/// no-masquerade asymmetry.
#[must_use]
pub fn mutual_induction_is_load_bearing(vcs: &[VerificationCondition]) -> bool {
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

/// CROSS-MEMBER-IH witness: `true` iff the bundle has a genuine cross-member
/// call, the real proof (projecting the CALLEE's component of the product IH)
/// is ACCEPTED, and the wrong-projection variant (projecting the caller's own
/// component) is REJECTED — the kernel witnesses that member identity in the
/// mutual bundle is load-bearing.
#[must_use]
pub fn cross_member_ih_is_load_bearing(vcs: &[VerificationCondition]) -> bool {
    let Some(plan) = parse_bundle(vcs) else {
        return false;
    };
    if !plan.has_cross_member_call() {
        return false;
    }
    let (Some(env), Some(goal), Some(proof), Some(wrong)) =
        (plan.build_env(), plan.goal(), plan.proof(), plan.proof_with(ProjectionMode::CallerSelf))
    else {
        return false;
    };
    kernel_checks_goal(&env, &proof, &goal) && !kernel_checks_goal(&env, &wrong, &goal)
}

#[cfg(test)]
mod tests {
    use trust_ir::ProofEvidence;
    use trust_types::{SourceSpan, VcKind};

    use super::*;

    // ── Bundle builders: the EXACT shapes trust-vcgen emits for the 2-member
    //    mutual fixture `fm <-> gm : (&Fuel, &E) -> E` (pinned by the
    //    trust-vcgen unit tests and driven literally in
    //    trust-integration-tests). ─────────────────────────────────────────────

    fn fuel_sort() -> Sort {
        Sort::Datatype {
            name: "fuel::Fuel".to_string(),
            constructors: vec![
                ("Z".to_string(), vec![]),
                (
                    "S".to_string(),
                    vec![(
                        "0".to_string(),
                        Sort::Datatype { name: "fuel::Fuel".to_string(), constructors: vec![] },
                    )],
                ),
            ],
        }
    }

    fn e_sort() -> Sort {
        Sort::Datatype {
            name: "expr::Expr".to_string(),
            constructors: vec![
                ("A".to_string(), vec![]),
                (
                    "B".to_string(),
                    vec![(
                        "0".to_string(),
                        Sort::Datatype { name: "expr::Expr".to_string(), constructors: vec![] },
                    )],
                ),
            ],
        }
    }

    fn var(name: &str) -> Formula {
        Formula::var_owned(name.to_string(), e_sort())
    }

    fn ctor(name: &str, args: Vec<Formula>) -> Formula {
        Formula::Ctor { ctor: name.to_string(), args, sort: e_sort() }
    }

    fn vc(property: &str, context: &str, formula: Formula) -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::FunctionalCorrectness {
                property: property.to_string(),
                context: context.to_string(),
            },
            function: context.into(),
            location: SourceSpan::default(),
            formula,
            contract_metadata: None,
            obligation: None,
        }
    }

    /// One member's 4 VCs (base A, base B, step A, step B) for a given rhs
    /// (`rhs(e)` instantiated per arm), plus its callee.
    fn member_vcs(
        name: &str,
        callee: &str,
        rhs_of: &dyn Fn(Formula) -> Formula,
    ) -> Vec<VerificationCondition> {
        let base_a = Formula::Eq(Box::new(ctor("A", vec![])), Box::new(rhs_of(ctor("A", vec![]))));
        let base_b = Formula::forall(
            &[("__fld_B_0", e_sort())],
            Formula::Eq(
                Box::new(ctor("B", vec![var("__fld_B_0")])),
                Box::new(rhs_of(ctor("B", vec![var("__fld_B_0")]))),
            ),
        );
        let step_a = Formula::forall(
            &[("__fld_S_0", fuel_sort())],
            Formula::Eq(Box::new(ctor("A", vec![])), Box::new(rhs_of(ctor("A", vec![])))),
        );
        let step_b = Formula::forall(
            &[("__fld_S_0", fuel_sort()), ("__fld_B_0", e_sort()), ("__ih0", e_sort())],
            Formula::Implies(
                // NOTE: the IH atom is the CALLEE's postcondition; both members
                // of these test bundles share the same rhs shape via `rhs_of`
                // in the true bundle, and the wrong bundle overrides gm's VCs.
                Box::new(Formula::Eq(Box::new(var("__ih0")), Box::new(rhs_of(var("__fld_B_0"))))),
                Box::new(Formula::Eq(
                    Box::new(ctor("B", vec![var("__ih0")])),
                    Box::new(rhs_of(ctor("B", vec![var("__fld_B_0")]))),
                )),
            ),
        );
        vec![
            vc(&format!("{BASE_PROPERTY_PREFIX}{name}::A"), name, base_a),
            vc(&format!("{BASE_PROPERTY_PREFIX}{name}::B"), name, base_b),
            vc(&format!("{CASE_PROPERTY_PREFIX}{name}::A[calls=]"), name, step_a),
            vc(&format!("{CASE_PROPERTY_PREFIX}{name}::B[calls={callee}]"), name, step_b),
        ]
    }

    fn conclusion_vc(rhs_fm: Formula, rhs_gm: Formula) -> VerificationCondition {
        let conj = |rhs: Formula| {
            Formula::forall(
                &[("fuel", fuel_sort()), ("e", e_sort())],
                Formula::Eq(Box::new(var("_0")), Box::new(rhs)),
            )
        };
        vc(
            &format!(
                "{CONCLUSION_PROPERTY_PREFIX}[mutual-induction:fuel=fuel::Fuel:Z|S;\
                 data=expr::Expr;members=fm,gm;bases=4;cases=4]"
            ),
            "fm+gm",
            Formula::And(vec![conj(rhs_fm), conj(rhs_gm)]),
        )
    }

    /// The emitted bundle for the TRUE postconditions `fm fuel e = e` and
    /// `gm fuel e = e` (identity; fm's B step calls gm and vice versa).
    fn identity_bundle() -> Vec<VerificationCondition> {
        let id = |t: Formula| t;
        let mut vcs = member_vcs("fm", "gm", &id);
        vcs.extend(member_vcs("gm", "fm", &id));
        vcs.push(conclusion_vc(var("e"), var("e")));
        vcs
    }

    /// The emitted bundle when ONE member (gm) carries the FALSE postcondition
    /// `gm fuel e = B e` (fm stays identity) — the mutual negative control.
    /// The wrong rhs flows into gm's own arms AND into fm's step-B IH atom
    /// (the atom is the callee's postcondition), exactly as vcgen emits it.
    fn wrong_gm_bundle() -> Vec<VerificationCondition> {
        let wrap_b = |t: Formula| ctor("B", vec![t]);

        // fm: arms against its own identity rhs, but the step-B IH atom uses
        // gm's wrong rhs.
        let mut vcs = vec![
            vc(
                &format!("{BASE_PROPERTY_PREFIX}fm::A"),
                "fm",
                Formula::Eq(Box::new(ctor("A", vec![])), Box::new(ctor("A", vec![]))),
            ),
            vc(
                &format!("{BASE_PROPERTY_PREFIX}fm::B"),
                "fm",
                Formula::forall(
                    &[("__fld_B_0", e_sort())],
                    Formula::Eq(
                        Box::new(ctor("B", vec![var("__fld_B_0")])),
                        Box::new(ctor("B", vec![var("__fld_B_0")])),
                    ),
                ),
            ),
            vc(
                &format!("{CASE_PROPERTY_PREFIX}fm::A[calls=]"),
                "fm",
                Formula::forall(
                    &[("__fld_S_0", fuel_sort())],
                    Formula::Eq(Box::new(ctor("A", vec![])), Box::new(ctor("A", vec![]))),
                ),
            ),
            vc(
                &format!("{CASE_PROPERTY_PREFIX}fm::B[calls=gm]"),
                "fm",
                Formula::forall(
                    &[("__fld_S_0", fuel_sort()), ("__fld_B_0", e_sort()), ("__ih0", e_sort())],
                    Formula::Implies(
                        Box::new(Formula::Eq(
                            Box::new(var("__ih0")),
                            Box::new(wrap_b(var("__fld_B_0"))), // gm's WRONG post
                        )),
                        Box::new(Formula::Eq(
                            Box::new(ctor("B", vec![var("__ih0")])),
                            Box::new(ctor("B", vec![var("__fld_B_0")])),
                        )),
                    ),
                ),
            ),
        ];
        // gm: arms against its WRONG rhs `B e`; its step-B IH atom is fm's
        // identity post.
        vcs.extend(vec![
            vc(
                &format!("{BASE_PROPERTY_PREFIX}gm::A"),
                "gm",
                Formula::Eq(Box::new(ctor("A", vec![])), Box::new(wrap_b(ctor("A", vec![])))),
            ),
            vc(
                &format!("{BASE_PROPERTY_PREFIX}gm::B"),
                "gm",
                Formula::forall(
                    &[("__fld_B_0", e_sort())],
                    Formula::Eq(
                        Box::new(ctor("B", vec![var("__fld_B_0")])),
                        Box::new(wrap_b(ctor("B", vec![var("__fld_B_0")]))),
                    ),
                ),
            ),
            vc(
                &format!("{CASE_PROPERTY_PREFIX}gm::A[calls=]"),
                "gm",
                Formula::forall(
                    &[("__fld_S_0", fuel_sort())],
                    Formula::Eq(Box::new(ctor("A", vec![])), Box::new(wrap_b(ctor("A", vec![])))),
                ),
            ),
            vc(
                &format!("{CASE_PROPERTY_PREFIX}gm::B[calls=fm]"),
                "gm",
                Formula::forall(
                    &[("__fld_S_0", fuel_sort()), ("__fld_B_0", e_sort()), ("__ih0", e_sort())],
                    Formula::Implies(
                        Box::new(Formula::Eq(
                            Box::new(var("__ih0")),
                            Box::new(var("__fld_B_0")), // fm's identity post
                        )),
                        Box::new(Formula::Eq(
                            Box::new(ctor("B", vec![var("__ih0")])),
                            Box::new(wrap_b(ctor("B", vec![var("__fld_B_0")]))),
                        )),
                    ),
                ),
            ),
        ]);
        vcs.push(conclusion_vc(var("e"), wrap_b(var("e"))));
        vcs
    }

    // ── THE MILESTONE: the generated joint Fuel.rec term kernel-checks ────────

    #[test]
    fn certify_identity_cluster_bundle() {
        let bundle = identity_bundle();
        let evidence = certify_mutual_recursive_datatype_functional(&bundle)
            .expect("the identity mutual bundle must certify to a kernel-checked CleanCic term");
        let ProofEvidence::CleanCic { term, context, lineage, .. } = evidence else {
            panic!("expected CleanCic evidence");
        };
        assert!(!term.is_empty() && !context.is_empty(), "nonempty CleanCic payload");
        assert_ne!(lineage, trust_ir::ProofDigest::zero(), "lineage must be bound");
        assert!(
            recheck_mutual_recursive_datatype_functional(&bundle, &term, &context, &lineage),
            "serialized mutual-functional CleanCic payload must re-check"
        );
    }

    /// The joint induction is load-bearing: the refl-only pseudo-proof is
    /// REJECTED while the generated `Fuel.rec` proof is ACCEPTED.
    #[test]
    fn identity_cluster_requires_mutual_induction() {
        assert!(
            mutual_induction_is_load_bearing(&identity_bundle()),
            "the Fuel.rec proof must check AND the refl-only pseudo-proof must be rejected"
        );
    }

    /// The CROSS-MEMBER IH is load-bearing: projecting the caller's own
    /// component instead of the callee's is kernel-rejected.
    #[test]
    fn identity_cluster_cross_member_ih_is_load_bearing() {
        assert!(
            cross_member_ih_is_load_bearing(&identity_bundle()),
            "the callee projection must check AND the caller-self projection must be rejected"
        );
    }

    // ── NEGATIVE control: a WRONG postcondition on ONE member kills the WHOLE
    //    bundle at the kernel ──────────────────────────────────────────────────

    #[test]
    fn wrong_postcondition_on_one_member_rejected_by_kernel() {
        let bundle = wrong_gm_bundle();
        // Non-vacuity: the wrong bundle is well-formed enough to build a plan,
        // env, goal, and candidate proof term.
        let plan = parse_bundle(&bundle).expect("wrong bundle must PARSE (not a malformation)");
        let env = plan.build_env().expect("env builds");
        let goal = plan.goal().expect("goal builds");
        let proof = plan.proof().expect("candidate proof term builds");
        // The kernel is the gate that rejects it — and the WHOLE joint proof
        // dies, not just gm's leg (mutual induction is all-or-nothing).
        assert!(
            !kernel_checks_goal(&env, &proof, &goal),
            "the clean kernel must REJECT the joint proof when one member's post is false"
        );
        assert!(
            certify_mutual_recursive_datatype_functional(&bundle).is_none(),
            "a false postcondition on any cluster member must never mint a certificate"
        );
    }

    // ── fail-closed shape gates ────────────────────────────────────────────────

    #[test]
    fn missing_conclusion_fails_closed() {
        let mut bundle = identity_bundle();
        bundle.pop();
        assert!(certify_mutual_recursive_datatype_functional(&bundle).is_none());
    }

    /// Dropping a case VC breaks the `cases=<n>` coverage marker: a partial
    /// mutual bundle certifies NOTHING.
    #[test]
    fn missing_case_fails_closed() {
        let bundle = identity_bundle();
        let partial: Vec<VerificationCondition> =
            bundle.iter().enumerate().filter(|(i, _)| *i != 3).map(|(_, v)| v.clone()).collect();
        assert!(
            certify_mutual_recursive_datatype_functional(&partial).is_none(),
            "a bundle whose cases do not match the conclusion's coverage marker must fail closed"
        );
    }

    /// Dropping a whole MEMBER (its 4 VCs) breaks the members marker.
    #[test]
    fn missing_member_fails_closed() {
        let bundle = identity_bundle();
        let partial: Vec<VerificationCondition> = bundle.iter().skip(4).cloned().collect();
        assert!(
            certify_mutual_recursive_datatype_functional(&partial).is_none(),
            "a bundle missing a cluster member must fail closed"
        );
    }

    #[test]
    fn tampered_term_rejected() {
        let bundle = identity_bundle();
        let evidence = certify_mutual_recursive_datatype_functional(&bundle).expect("certify");
        let ProofEvidence::CleanCic { term, context, lineage, .. } = evidence else {
            panic!("expected CleanCic evidence");
        };
        let mut tampered = term.clone();
        tampered[0] ^= 0xff;
        assert!(
            !recheck_mutual_recursive_datatype_functional(&bundle, &tampered, &context, &lineage),
            "tampered term must fail the offline kernel re-check"
        );
    }

    #[test]
    fn swapped_lineage_rejected() {
        let bundle = identity_bundle();
        let evidence = certify_mutual_recursive_datatype_functional(&bundle).expect("certify");
        let ProofEvidence::CleanCic { term, context, .. } = evidence else {
            panic!("expected CleanCic evidence");
        };
        assert!(
            !recheck_mutual_recursive_datatype_functional(
                &bundle,
                &term,
                &context,
                &trust_ir::ProofDigest::zero()
            ),
            "a zeroed lineage must fail closed"
        );
    }

    #[test]
    fn relineaged_ambient_sorry_beta_proof_context_and_vc_drift_are_rejected() {
        let bundle = identity_bundle();
        let plan = parse_bundle(&bundle).expect("bundle parses");
        let env = plan.build_env().expect("minimal env");
        let goal = plan.goal().expect("goal");
        let proof = plan.proof().expect("canonical proof");
        let context = crate::canonical_empty_context_bytes().expect("canonical context");

        let mut ambient = env.clone();
        let sorry = crate::install_adversarial_trust_marker(&mut ambient, &goal)
            .expect("install adversarial trusted marker");
        assert!(kernel_checks_goal(&ambient, &sorry, &goal));
        let sorry_bytes = serialize_term(&sorry).expect("serialize sorry");
        let sorry_lineage =
            mutual_functional_lineage_digest(&bundle, &sorry_bytes, &context, &plan.label)
                .expect("lineage");
        assert!(!recheck_mutual_recursive_datatype_functional(
            &bundle,
            &sorry_bytes,
            &context,
            &sorry_lineage,
        ));

        let beta =
            Expr::app(Expr::lam(BinderInfo::Default, goal.clone(), Expr::bvar(0)), proof.clone());
        assert!(kernel_checks_goal(&env, &beta, &goal));
        let beta_bytes = serialize_term(&beta).expect("serialize beta proof");
        let beta_lineage =
            mutual_functional_lineage_digest(&bundle, &beta_bytes, &context, &plan.label)
                .expect("lineage");
        assert!(!recheck_mutual_recursive_datatype_functional(
            &bundle,
            &beta_bytes,
            &context,
            &beta_lineage,
        ));

        let term = serialize_term(&proof).expect("canonical proof");
        let mut noncanonical_context = context.clone();
        noncanonical_context.push(0);
        let relined =
            mutual_functional_lineage_digest(&bundle, &term, &noncanonical_context, &plan.label)
                .expect("lineage");
        assert!(!recheck_mutual_recursive_datatype_functional(
            &bundle,
            &term,
            &noncanonical_context,
            &relined,
        ));

        let honest_lineage =
            mutual_functional_lineage_digest(&bundle, &term, &context, &plan.label)
                .expect("lineage");
        let mut drifted = bundle.clone();
        drifted[0].location.file = "different_source.rs".to_string();
        assert!(parse_bundle(&drifted).is_some());
        assert!(!recheck_mutual_recursive_datatype_functional(
            &drifted,
            &term,
            &context,
            &honest_lineage,
        ));
    }
}

#[cfg(test)]
mod multi_ih_opaque_tests {
    //! Items 1 + 2 of the literal-cluster extension, at the unit level: a
    //! 2-member cluster over `T = A | M(T, T) | P(Name)` — `M` has TWO
    //! recursive fields (two IHs per step arm), `P`'s field is an OPAQUE
    //! `name::Name` atom. Hand-built bundles in the exact vcgen shapes.

    use trust_ir::ProofEvidence;
    use trust_types::{SourceSpan, VcKind};

    use super::*;

    fn fuel_sort() -> Sort {
        Sort::Datatype {
            name: "fuel::Fuel".to_string(),
            constructors: vec![
                ("Z".to_string(), vec![]),
                (
                    "S".to_string(),
                    vec![(
                        "0".to_string(),
                        Sort::Datatype { name: "fuel::Fuel".to_string(), constructors: vec![] },
                    )],
                ),
            ],
        }
    }

    fn opaque_sort() -> Sort {
        Sort::Datatype { name: "name::Name".to_string(), constructors: vec![] }
    }

    fn t_sort() -> Sort {
        let t_ref = Sort::Datatype { name: "t::T".to_string(), constructors: vec![] };
        Sort::Datatype {
            name: "t::T".to_string(),
            constructors: vec![
                ("A".to_string(), vec![]),
                ("M".to_string(), vec![("0".to_string(), t_ref.clone()), ("1".to_string(), t_ref)]),
                ("P".to_string(), vec![("0".to_string(), opaque_sort())]),
            ],
        }
    }

    fn var(name: &str) -> Formula {
        Formula::var_owned(name.to_string(), t_sort())
    }

    fn ovar(name: &str) -> Formula {
        Formula::var_owned(name.to_string(), opaque_sort())
    }

    fn ctor(name: &str, args: Vec<Formula>) -> Formula {
        Formula::Ctor { ctor: name.to_string(), args, sort: t_sort() }
    }

    fn vc(property: &str, context: &str, formula: Formula) -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::FunctionalCorrectness {
                property: property.to_string(),
                context: context.to_string(),
            },
            function: context.into(),
            location: SourceSpan::default(),
            formula,
            contract_metadata: None,
            obligation: None,
        }
    }

    /// One member's 6 VCs (identity rhs; base per-ctor rebuild; the step M
    /// arm calls `callee` on BOTH fields — two IH atoms). `m_result` is the
    /// step-M arm's result over `(__ih0, __ih1)` (the true arm rebuilds
    /// `M(__ih0, __ih1)`).
    fn member_vcs(name: &str, callee: &str, m_result: Formula) -> Vec<VerificationCondition> {
        let base_a = Formula::Eq(Box::new(ctor("A", vec![])), Box::new(ctor("A", vec![])));
        let base_m = Formula::forall(
            &[("__fld_M_0", t_sort()), ("__fld_M_1", t_sort())],
            Formula::Eq(
                Box::new(ctor("M", vec![var("__fld_M_0"), var("__fld_M_1")])),
                Box::new(ctor("M", vec![var("__fld_M_0"), var("__fld_M_1")])),
            ),
        );
        let base_p = Formula::forall(
            &[("__fld_P_0", opaque_sort())],
            Formula::Eq(
                Box::new(ctor("P", vec![ovar("__fld_P_0")])),
                Box::new(ctor("P", vec![ovar("__fld_P_0")])),
            ),
        );
        let step_a = Formula::forall(
            &[("__fld_S_0", fuel_sort())],
            Formula::Eq(Box::new(ctor("A", vec![])), Box::new(ctor("A", vec![]))),
        );
        let step_m = Formula::forall(
            &[
                ("__fld_S_0", fuel_sort()),
                ("__fld_M_0", t_sort()),
                ("__fld_M_1", t_sort()),
                ("__ih0", t_sort()),
                ("__ih1", t_sort()),
            ],
            Formula::Implies(
                Box::new(Formula::And(vec![
                    Formula::Eq(Box::new(var("__ih0")), Box::new(var("__fld_M_0"))),
                    Formula::Eq(Box::new(var("__ih1")), Box::new(var("__fld_M_1"))),
                ])),
                Box::new(Formula::Eq(
                    Box::new(m_result),
                    Box::new(ctor("M", vec![var("__fld_M_0"), var("__fld_M_1")])),
                )),
            ),
        );
        let step_p = Formula::forall(
            &[("__fld_S_0", fuel_sort()), ("__fld_P_0", opaque_sort())],
            Formula::Eq(
                Box::new(ctor("P", vec![ovar("__fld_P_0")])),
                Box::new(ctor("P", vec![ovar("__fld_P_0")])),
            ),
        );
        vec![
            vc(&format!("{BASE_PROPERTY_PREFIX}{name}::A"), name, base_a),
            vc(&format!("{BASE_PROPERTY_PREFIX}{name}::M"), name, base_m),
            vc(&format!("{BASE_PROPERTY_PREFIX}{name}::P"), name, base_p),
            vc(&format!("{CASE_PROPERTY_PREFIX}{name}::A[calls=]"), name, step_a),
            vc(&format!("{CASE_PROPERTY_PREFIX}{name}::M[calls={callee},{callee}]"), name, step_m),
            vc(&format!("{CASE_PROPERTY_PREFIX}{name}::P[calls=]"), name, step_p),
        ]
    }

    fn conclusion_vc() -> VerificationCondition {
        let conj = || {
            Formula::forall(
                &[("fuel", fuel_sort()), ("e", t_sort())],
                Formula::Eq(Box::new(var("_0")), Box::new(var("e"))),
            )
        };
        vc(
            &format!(
                "{CONCLUSION_PROPERTY_PREFIX}[mutual-induction:fuel=fuel::Fuel:Z|S;\
                 data=t::T;members=fm,gm;bases=6;cases=6]"
            ),
            "fm+gm",
            Formula::And(vec![conj(), conj()]),
        )
    }

    fn multi_ih_bundle() -> Vec<VerificationCondition> {
        let mut vcs = member_vcs("fm", "gm", ctor("M", vec![var("__ih0"), var("__ih1")]));
        vcs.extend(member_vcs("gm", "fm", ctor("M", vec![var("__ih0"), var("__ih1")])));
        vcs.push(conclusion_vc());
        vcs
    }

    /// THE ITEM-1 MILESTONE: a two-IH constructor arm — the discharge chains
    /// `congrArg` through both call-result occurrences — kernel-checks, with
    /// an opaque `Param`-style field transported alongside (item 2).
    #[test]
    fn certify_multi_ih_opaque_bundle() {
        let bundle = multi_ih_bundle();
        let evidence = certify_mutual_recursive_datatype_functional(&bundle)
            .expect("the two-IH + opaque bundle must certify (kernel-checked joint term)");
        let ProofEvidence::CleanCic { term, context, lineage, .. } = evidence else {
            panic!("expected CleanCic evidence");
        };
        assert!(
            recheck_mutual_recursive_datatype_functional(&bundle, &term, &context, &lineage),
            "serialized multi-IH CleanCic payload must re-check"
        );
    }

    /// The induction and the cross-member edges stay load-bearing on the
    /// multi-IH bundle.
    #[test]
    fn multi_ih_bundle_witnesses() {
        let bundle = multi_ih_bundle();
        assert!(mutual_induction_is_load_bearing(&bundle));
        assert!(cross_member_ih_is_load_bearing(&bundle));
    }

    /// NEGATIVE (item 1): wrong on ONE branch of the two-IH arm — gm's step-M
    /// result uses the FIRST IH for both fields (`M(__ih0, __ih0)`). The
    /// bundle parses and builds; the kernel rejects the joint proof.
    #[test]
    fn wrong_single_leg_of_two_ih_arm_rejected_by_kernel() {
        let mut vcs = member_vcs("fm", "gm", ctor("M", vec![var("__ih0"), var("__ih1")]));
        vcs.extend(member_vcs("gm", "fm", ctor("M", vec![var("__ih0"), var("__ih0")])));
        vcs.push(conclusion_vc());
        let plan = parse_bundle(&vcs).expect("wrong-leg bundle must PARSE (not a malformation)");
        let env = plan.build_env().expect("env builds");
        let goal = plan.goal().expect("goal builds");
        let proof = plan.proof().expect("candidate proof term builds");
        assert!(
            !kernel_checks_goal(&env, &proof, &goal),
            "the kernel must REJECT a two-IH arm that is wrong in one leg"
        );
        assert!(certify_mutual_recursive_datatype_functional(&vcs).is_none());
    }

    /// NEGATIVE (item 2): a wrong `P` arm (drops the opaque payload,
    /// rebuilding `A` instead of `P(n)`) is kernel-rejected.
    #[test]
    fn wrong_param_arm_rejected_by_kernel() {
        let mut vcs = member_vcs("fm", "gm", ctor("M", vec![var("__ih0"), var("__ih1")]));
        let mut gm = member_vcs("gm", "fm", ctor("M", vec![var("__ih0"), var("__ih1")]));
        // gm's base-P arm claims `A = P(n)` (the arm result is A).
        gm[2] = vc(
            &format!("{BASE_PROPERTY_PREFIX}gm::P"),
            "gm",
            Formula::forall(
                &[("__fld_P_0", opaque_sort())],
                Formula::Eq(
                    Box::new(ctor("A", vec![])),
                    Box::new(ctor("P", vec![ovar("__fld_P_0")])),
                ),
            ),
        );
        vcs.extend(gm);
        vcs.push(conclusion_vc());
        let plan = parse_bundle(&vcs).expect("wrong-P bundle must PARSE");
        let env = plan.build_env().expect("env builds");
        let goal = plan.goal().expect("goal builds");
        let proof = plan.proof().expect("candidate proof term builds");
        assert!(
            !kernel_checks_goal(&env, &proof, &goal),
            "the kernel must REJECT a wrong opaque-payload arm"
        );
        assert!(certify_mutual_recursive_datatype_functional(&vcs).is_none());
    }

    /// NEGATIVE (item 2, the CARRIER-CHOICE witness): a bundle whose arm
    /// SWAPS two opaque fields (`Q(n0, n1) -> Q(n1, n0)` against the identity
    /// postcondition) must be kernel-rejected. This is exactly what a
    /// unit-like opaque carrier would silently accept (structure eta
    /// identifies all values of a one-constructor type) — the two-constructor
    /// `__opaque_k` keeps distinct opaque atoms definitionally distinct.
    #[test]
    fn opaque_field_swap_is_rejected() {
        fn q_sort() -> Sort {
            Sort::Datatype {
                name: "q::Q".to_string(),
                constructors: vec![
                    ("A".to_string(), vec![]),
                    (
                        "Q".to_string(),
                        vec![("0".to_string(), opaque_sort()), ("1".to_string(), opaque_sort())],
                    ),
                ],
            }
        }
        let qvar = |name: &str| Formula::var_owned(name.to_string(), q_sort());
        let qctor = |name: &str, args: Vec<Formula>| Formula::Ctor {
            ctor: name.to_string(),
            args,
            sort: q_sort(),
        };
        let member = |name: &str, swap: bool| {
            let q_fields = |a: &str, b: &str| vec![ovar(a), ovar(b)];
            let (r0, r1) =
                if swap { ("__fld_Q_1", "__fld_Q_0") } else { ("__fld_Q_0", "__fld_Q_1") };
            vec![
                vc(
                    &format!("{BASE_PROPERTY_PREFIX}{name}::A"),
                    name,
                    Formula::Eq(Box::new(qctor("A", vec![])), Box::new(qctor("A", vec![]))),
                ),
                vc(
                    &format!("{BASE_PROPERTY_PREFIX}{name}::Q"),
                    name,
                    Formula::forall(
                        &[("__fld_Q_0", opaque_sort()), ("__fld_Q_1", opaque_sort())],
                        Formula::Eq(
                            Box::new(qctor("Q", q_fields(r0, r1))),
                            Box::new(qctor("Q", q_fields("__fld_Q_0", "__fld_Q_1"))),
                        ),
                    ),
                ),
                vc(
                    &format!("{CASE_PROPERTY_PREFIX}{name}::A[calls=]"),
                    name,
                    Formula::forall(
                        &[("__fld_S_0", fuel_sort())],
                        Formula::Eq(Box::new(qctor("A", vec![])), Box::new(qctor("A", vec![]))),
                    ),
                ),
                vc(
                    &format!("{CASE_PROPERTY_PREFIX}{name}::Q[calls=]"),
                    name,
                    Formula::forall(
                        &[
                            ("__fld_S_0", fuel_sort()),
                            ("__fld_Q_0", opaque_sort()),
                            ("__fld_Q_1", opaque_sort()),
                        ],
                        Formula::Eq(
                            Box::new(qctor("Q", q_fields(r0, r1))),
                            Box::new(qctor("Q", q_fields("__fld_Q_0", "__fld_Q_1"))),
                        ),
                    ),
                ),
            ]
        };
        let conclusion = vc(
            &format!(
                "{CONCLUSION_PROPERTY_PREFIX}[mutual-induction:fuel=fuel::Fuel:Z|S;\
                 data=q::Q;members=fm,gm;bases=4;cases=4]"
            ),
            "fm+gm",
            Formula::And(vec![
                Formula::forall(
                    &[("fuel", fuel_sort()), ("e", q_sort())],
                    Formula::Eq(Box::new(qvar("_0")), Box::new(qvar("e"))),
                ),
                Formula::forall(
                    &[("fuel", fuel_sort()), ("e", q_sort())],
                    Formula::Eq(Box::new(qvar("_0")), Box::new(qvar("e"))),
                ),
            ]),
        );
        // Sanity: the UNSWAPPED twin certifies (this bundle shape is in scope,
        // so the swap rejection below is the kernel's verdict, not a parse gap).
        let mut good = member("fm", false);
        good.extend(member("gm", false));
        good.push(conclusion.clone());
        assert!(
            certify_mutual_recursive_datatype_functional(&good).is_some(),
            "the unswapped opaque-pair bundle must certify"
        );
        // The swapped bundle: `Q(n1, n0) = Q(n0, n1)` — false over an
        // uninterpreted domain; the kernel must reject it.
        let mut bad = member("fm", true);
        bad.extend(member("gm", false));
        bad.push(conclusion);
        let plan = parse_bundle(&bad).expect("swap bundle must PARSE");
        let env = plan.build_env().expect("env builds");
        let goal = plan.goal().expect("goal builds");
        let proof = plan.proof().expect("candidate proof term builds");
        assert!(
            !kernel_checks_goal(&env, &proof, &goal),
            "distinct opaque atoms must never be identified by the kernel carrier"
        );
        assert!(certify_mutual_recursive_datatype_functional(&bad).is_none());
    }
}

#[cfg(test)]
mod ref_fn_tests {
    //! Item 3 of the literal-cluster extension, at the unit level: the
    //! model=reference (`bootstrap_model_fidelity`) postcondition shape over
    //! `T = A | M(T, T) | P(Name)` — members rebuild per-constructor at fuel
    //! zero, references return DIRECTLY (different folds, pointwise equal), so
    //! the goal `model_i n e = ref_i n e` is `Eq` of two genuinely different
    //! `Fuel.rec` folds.

    use trust_ir::ProofEvidence;
    use trust_types::{SourceSpan, VcKind};

    use super::*;

    fn fuel_sort() -> Sort {
        Sort::Datatype {
            name: "fuel::Fuel".to_string(),
            constructors: vec![
                ("Z".to_string(), vec![]),
                (
                    "S".to_string(),
                    vec![(
                        "0".to_string(),
                        Sort::Datatype { name: "fuel::Fuel".to_string(), constructors: vec![] },
                    )],
                ),
            ],
        }
    }

    fn opaque_sort() -> Sort {
        Sort::Datatype { name: "name::Name".to_string(), constructors: vec![] }
    }

    fn t_sort() -> Sort {
        let t_ref = Sort::Datatype { name: "t::T".to_string(), constructors: vec![] };
        Sort::Datatype {
            name: "t::T".to_string(),
            constructors: vec![
                ("A".to_string(), vec![]),
                ("M".to_string(), vec![("0".to_string(), t_ref.clone()), ("1".to_string(), t_ref)]),
                ("P".to_string(), vec![("0".to_string(), opaque_sort())]),
            ],
        }
    }

    fn fuel_ctor(name: &str, args: Vec<Formula>) -> Formula {
        Formula::Ctor { ctor: name.to_string(), args, sort: fuel_sort() }
    }

    fn fvar(name: &str) -> Formula {
        Formula::var_owned(name.to_string(), fuel_sort())
    }

    fn var(name: &str) -> Formula {
        Formula::var_owned(name.to_string(), t_sort())
    }

    fn ovar(name: &str) -> Formula {
        Formula::var_owned(name.to_string(), opaque_sort())
    }

    fn ctor(name: &str, args: Vec<Formula>) -> Formula {
        Formula::Ctor { ctor: name.to_string(), args, sort: t_sort() }
    }

    fn fnapp(func: &str, args: Vec<Formula>) -> Formula {
        Formula::FnApp { func: func.to_string(), args, sort: t_sort() }
    }

    fn vc(property: &str, context: &str, formula: Formula) -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::FunctionalCorrectness {
                property: property.to_string(),
                context: context.to_string(),
            },
            function: context.into(),
            location: SourceSpan::default(),
            formula,
            contract_metadata: None,
            obligation: None,
        }
    }

    /// One MEMBER's 6 VCs against the reference postcondition
    /// `_0 = FnApp(my_ref, [fuel, e])` (base = per-ctor rebuild; the step M
    /// arm calls `callee` on both fields — the IH atoms carry the CALLEE's
    /// reference `callee_ref`).
    fn member_vcs(
        name: &str,
        my_ref: &str,
        callee: &str,
        callee_ref: &str,
    ) -> Vec<VerificationCondition> {
        let z = || fuel_ctor("Z", vec![]);
        let s_k = || fuel_ctor("S", vec![fvar("__fld_S_0")]);
        vec![
            vc(
                &format!("{BASE_PROPERTY_PREFIX}{name}::A"),
                name,
                Formula::Eq(
                    Box::new(ctor("A", vec![])),
                    Box::new(fnapp(my_ref, vec![z(), ctor("A", vec![])])),
                ),
            ),
            vc(
                &format!("{BASE_PROPERTY_PREFIX}{name}::M"),
                name,
                Formula::forall(
                    &[("__fld_M_0", t_sort()), ("__fld_M_1", t_sort())],
                    Formula::Eq(
                        Box::new(ctor("M", vec![var("__fld_M_0"), var("__fld_M_1")])),
                        Box::new(fnapp(
                            my_ref,
                            vec![z(), ctor("M", vec![var("__fld_M_0"), var("__fld_M_1")])],
                        )),
                    ),
                ),
            ),
            vc(
                &format!("{BASE_PROPERTY_PREFIX}{name}::P"),
                name,
                Formula::forall(
                    &[("__fld_P_0", opaque_sort())],
                    Formula::Eq(
                        Box::new(ctor("P", vec![ovar("__fld_P_0")])),
                        Box::new(fnapp(my_ref, vec![z(), ctor("P", vec![ovar("__fld_P_0")])])),
                    ),
                ),
            ),
            vc(
                &format!("{CASE_PROPERTY_PREFIX}{name}::A[calls=]"),
                name,
                Formula::forall(
                    &[("__fld_S_0", fuel_sort())],
                    Formula::Eq(
                        Box::new(ctor("A", vec![])),
                        Box::new(fnapp(my_ref, vec![s_k(), ctor("A", vec![])])),
                    ),
                ),
            ),
            vc(
                &format!("{CASE_PROPERTY_PREFIX}{name}::M[calls={callee},{callee}]"),
                name,
                Formula::forall(
                    &[
                        ("__fld_S_0", fuel_sort()),
                        ("__fld_M_0", t_sort()),
                        ("__fld_M_1", t_sort()),
                        ("__ih0", t_sort()),
                        ("__ih1", t_sort()),
                    ],
                    Formula::Implies(
                        Box::new(Formula::And(vec![
                            Formula::Eq(
                                Box::new(var("__ih0")),
                                Box::new(fnapp(
                                    callee_ref,
                                    vec![fvar("__fld_S_0"), var("__fld_M_0")],
                                )),
                            ),
                            Formula::Eq(
                                Box::new(var("__ih1")),
                                Box::new(fnapp(
                                    callee_ref,
                                    vec![fvar("__fld_S_0"), var("__fld_M_1")],
                                )),
                            ),
                        ])),
                        Box::new(Formula::Eq(
                            Box::new(ctor("M", vec![var("__ih0"), var("__ih1")])),
                            Box::new(fnapp(
                                my_ref,
                                vec![s_k(), ctor("M", vec![var("__fld_M_0"), var("__fld_M_1")])],
                            )),
                        )),
                    ),
                ),
            ),
            vc(
                &format!("{CASE_PROPERTY_PREFIX}{name}::P[calls=]"),
                name,
                Formula::forall(
                    &[("__fld_S_0", fuel_sort()), ("__fld_P_0", opaque_sort())],
                    Formula::Eq(
                        Box::new(ctor("P", vec![ovar("__fld_P_0")])),
                        Box::new(fnapp(my_ref, vec![s_k(), ctor("P", vec![ovar("__fld_P_0")])])),
                    ),
                ),
            ),
        ]
    }

    /// One REFERENCE's definitional VCs: base = DIRECT return (a different
    /// fold shape than the members' per-ctor rebuild); step arms mirror the
    /// members', with `swap_m` optionally COMMUTING the M arm's call
    /// arguments (the negative control).
    fn ref_vcs(name: &str, callee_ref: &str, swap_m: bool) -> Vec<VerificationCondition> {
        let z = || fuel_ctor("Z", vec![]);
        let s_k = || fuel_ctor("S", vec![fvar("__fld_S_0")]);
        let (m0, m1) = if swap_m { ("__fld_M_1", "__fld_M_0") } else { ("__fld_M_0", "__fld_M_1") };
        vec![
            vc(
                &format!("{REF_BASE_PROPERTY_PREFIX}{name}"),
                name,
                Formula::forall(
                    &[("e", t_sort())],
                    Formula::Eq(Box::new(fnapp(name, vec![z(), var("e")])), Box::new(var("e"))),
                ),
            ),
            vc(
                &format!("{REF_STEP_PROPERTY_PREFIX}{name}::A[calls=]"),
                name,
                Formula::forall(
                    &[("__fld_S_0", fuel_sort())],
                    Formula::Eq(
                        Box::new(fnapp(name, vec![s_k(), ctor("A", vec![])])),
                        Box::new(ctor("A", vec![])),
                    ),
                ),
            ),
            vc(
                &format!("{REF_STEP_PROPERTY_PREFIX}{name}::M[calls={callee_ref},{callee_ref}]"),
                name,
                Formula::forall(
                    &[("__fld_S_0", fuel_sort()), ("__fld_M_0", t_sort()), ("__fld_M_1", t_sort())],
                    Formula::Eq(
                        Box::new(fnapp(
                            name,
                            vec![s_k(), ctor("M", vec![var("__fld_M_0"), var("__fld_M_1")])],
                        )),
                        Box::new(ctor(
                            "M",
                            vec![
                                fnapp(callee_ref, vec![fvar("__fld_S_0"), var(m0)]),
                                fnapp(callee_ref, vec![fvar("__fld_S_0"), var(m1)]),
                            ],
                        )),
                    ),
                ),
            ),
            vc(
                &format!("{REF_STEP_PROPERTY_PREFIX}{name}::P[calls=]"),
                name,
                Formula::forall(
                    &[("__fld_S_0", fuel_sort()), ("__fld_P_0", opaque_sort())],
                    Formula::Eq(
                        Box::new(fnapp(name, vec![s_k(), ctor("P", vec![ovar("__fld_P_0")])])),
                        Box::new(ctor("P", vec![ovar("__fld_P_0")])),
                    ),
                ),
            ),
        ]
    }

    fn conclusion_vc() -> VerificationCondition {
        let conj = |r: &str| {
            Formula::forall(
                &[("fuel", fuel_sort()), ("e", t_sort())],
                Formula::Eq(Box::new(var("_0")), Box::new(fnapp(r, vec![fvar("fuel"), var("e")]))),
            )
        };
        vc(
            &format!(
                "{CONCLUSION_PROPERTY_PREFIX}[mutual-induction:fuel=fuel::Fuel:Z|S;\
                 data=t::T;members=fm,gm;bases=6;cases=6;refs=fr,gr;refbases=2;refcases=6]"
            ),
            "fm+gm",
            Formula::And(vec![conj("fr"), conj("gr")]),
        )
    }

    fn model_vs_reference_bundle(swap_ref_m: bool) -> Vec<VerificationCondition> {
        let mut vcs = member_vcs("fm", "fr", "gm", "gr");
        vcs.extend(member_vcs("gm", "gr", "fm", "fr"));
        vcs.extend(ref_vcs("fr", "gr", swap_ref_m));
        vcs.extend(ref_vcs("gr", "fr", false));
        vcs.push(conclusion_vc());
        vcs
    }

    /// THE ITEM-3 MILESTONE: the model=reference goal — `Eq` of two
    /// genuinely different `Fuel.rec` folds (per-ctor base vs direct base) —
    /// is machine-discharged and kernel-checked, with the multi-IH arm and
    /// the opaque payload riding along.
    #[test]
    fn certify_model_vs_reference_bundle() {
        let bundle = model_vs_reference_bundle(false);
        let evidence = certify_mutual_recursive_datatype_functional(&bundle)
            .expect("the model=reference bundle must certify (kernel-checked joint term)");
        let ProofEvidence::CleanCic { term, context, lineage, .. } = evidence else {
            panic!("expected CleanCic evidence");
        };
        assert!(
            recheck_mutual_recursive_datatype_functional(&bundle, &term, &context, &lineage),
            "serialized model=reference CleanCic payload must re-check"
        );
    }

    /// The induction and cross-member edges stay load-bearing in
    /// function-vs-function mode.
    #[test]
    fn model_vs_reference_witnesses() {
        let bundle = model_vs_reference_bundle(false);
        assert!(mutual_induction_is_load_bearing(&bundle));
        assert!(cross_member_ih_is_load_bearing(&bundle));
    }

    /// NEGATIVE (item 3): a reference whose M arm COMMUTES its call arguments
    /// (`M(gr k r, gr k l)`) defines a genuinely different function — the
    /// bundle parses and builds, and the kernel rejects the joint proof.
    #[test]
    fn commuted_reference_arm_rejected_by_kernel() {
        let bundle = model_vs_reference_bundle(true);
        let plan = parse_bundle(&bundle).expect("commuted-ref bundle must PARSE");
        let env = plan.build_env().expect("env builds");
        let goal = plan.goal().expect("goal builds");
        let proof = plan.proof().expect("candidate proof term builds");
        assert!(
            !kernel_checks_goal(&env, &proof, &goal),
            "a commuted reference arm must be kernel-rejected"
        );
        assert!(certify_mutual_recursive_datatype_functional(&bundle).is_none());
    }

    /// Dropping a reference definitional VC breaks the `refcases=<n>` marker:
    /// the definition transport is coverage-pinned, fail-closed.
    #[test]
    fn missing_ref_vc_fails_closed() {
        let bundle = model_vs_reference_bundle(false);
        let partial: Vec<VerificationCondition> = bundle
            .iter()
            .filter(|v| {
                let VcKind::FunctionalCorrectness { property, .. } = &v.kind else {
                    return true;
                };
                property != &format!("{REF_STEP_PROPERTY_PREFIX}fr::M[calls=gr,gr]")
            })
            .cloned()
            .collect();
        assert_eq!(partial.len(), bundle.len() - 1, "exactly one ref VC dropped");
        assert!(
            certify_mutual_recursive_datatype_functional(&partial).is_none(),
            "a bundle missing a reference definitional VC must fail closed"
        );
    }
}
