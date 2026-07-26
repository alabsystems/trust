// trust-certify: RECURSIVE datatype-function INDUCTION discharge lane (WALL C).
//
// The sibling `datatype_functional` lane discharges the NON-recursive sort-arm
// functional VC by kernel reflexivity, and `tests/level_recursive_functional.rs`
// demonstrated (hand-built) that a `Level.rec` induction term kernel-checks the
// recursive fact `forall l, mirror l = l`. THIS lane closes the gap between the
// two: it takes the INDUCTION VC BUNDLE that trust-vcgen's
// `recursive_datatype_functional` lane emits for a SELF-recursive extracted
// datatype function — the per-constructor induction cases (recursive calls
// replaced by IH variables) plus the `[induction:..]`-tagged conclusion — and
// GENERATES the corresponding `.rec` CIC induction term, which the clean kernel
// re-checks (the Certified tier). The `level_recursive_functional` proof shape
// is now MACHINE-BUILT from the VCs instead of hand-written.
//
// INPUT (the emitted bundle, `trust_types::VerificationCondition`s):
//   case Zero:  `Eq(Ctor Zero, Ctor Zero)`
//   case Succ:  `Forall [__fld_Succ_0, __ih0]
//                  (Implies (Eq(__ih0, __fld_Succ_0))
//                           (Eq(Ctor(Succ,[__ih0]), Ctor(Succ,[__fld_Succ_0]))))`
//   conclusion: `Forall [l] Eq(_0, l)`  [induction:level::Level;cases=2]
//
// GENERATED DISCHARGE (all machine-built from the bundle):
//   1. the datatype is RECONSTRUCTED from the case patterns (ctor names +
//      arities, in case order) and registered via `add_inductive` (=> `DT.rec`
//      and its iota rules);
//   2. the MODEL function is BUILT FROM THE ARM RESULTS as a `DT.rec` fold
//      (`mirror_model := fun l => Level.rec (fun _ => Level) zero
//        (fun pred ih => succ ih) l`) and registered as a real
//      `Declaration::Definition` (the kernel type-checks it);
//   3. the goal `forall x, Eq DT (model x) rhs(x)` (the conclusion VC with `_0`
//      bound to the model's output) is proved by the GENERATED induction term
//        `fun x => DT.rec.{0} (motive := fun y => Eq (model y) rhs(y))
//           <base: Eq.refl (rhs[ctor])>
//           <step: fun f ih => congrArg DT DT (model f) (rhs f) DT.C ih> x`
//      whose minor premises come 1:1 from the case VCs — the IH variable of the
//      emitted case IS the `ih` the `.rec` minor consumes.
//
// NO MASQUERADE (the IH is load-bearing, kernel-witnessed):
//   * a WRONG postcondition bundle (e.g. `mirror l = succ l`, emitted by the
//     same vcgen lane from the false spec) PARSES and BUILDS, and the clean
//     KERNEL rejects the generated proof (the base minor's refl does not
//     type-check against the false instance) — the mint fails closed (`None`);
//   * the refl-only pseudo-proof `fun x => Eq.refl DT (model x)` of the TRUE
//     goal is REJECTED (`model x` is stuck on the free `x`; only the `.rec`
//     term carrying the IH closes it) — `refl_only_pseudo_proof_is_rejected`
//     exposes this witness to the integration test.
//
// SOUNDNESS (fail-closed, never a false `Certified`):
//   * evidence is minted ONLY when the clean kernel certifies `proof : goal`;
//   * env = a MINIMAL environment (no ambient `sorry`/`trusted*`) + `init_eq` +
//     opaque scalar TYPE declarations (never scalar inhabitants) + reconstructed
//     payload/main inductives + the model definition, in a closed context;
//   * the canonical term + canonical empty context + the FULL serialized VC
//     bundle are digest-bound; consumer re-check independently rebuilds the same
//     plan and requires byte-identical canonical term/context before kernel check;
//   * every unsupported shape (non-self-recursive spec forms, multi-parameter
//     functions, compound non-datatype fields, cross-mutual payload definitions,
//     arm results other than exact payload passthrough + ctor-of-IHs) returns
//     `None`.
//
// HONEST SCOPE — the recursion PRIMITIVE, not the kernel cluster:
//   * this lane certifies the reconstructed kernel model represented by the
//     supplied typed VC bundle; absent a separate extraction/provenance bridge,
//     it does NOT prove that bundle came from a literal Rust/TrustIR function;
//   * SELF-recursion over a single-parameter function on one datatype whose
//     constructors may have general-N recursive fields plus held-fixed datatype
//     or scalar payload fields, postcondition `_0 = rhs(param)` with `rhs` a
//     constructor tree over the parameter;
//   * MUTUAL induction over a call-graph SCC of size N > 1 (fuel-indexed) is
//     the sibling `mutual_recursive_datatype_functional` lane; function-vs-
//     function postconditions and compound/parametric payload types remain out
//     of scope.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::HashMap;

use clean_auto::bridge::ay_contract::{
    ReducedContext, deserialize_term, serialize_context, serialize_term,
};
use clean_kernel::name::Name;
use clean_kernel::{
    BinderInfo, Constructor, Declaration, Environment, Expr, InductiveDecl, InductiveType, Level,
    LocalContext, TypeChecker,
};
use sha2::{Digest, Sha256};
use trust_types::{Formula, Sort, VcKind, VerificationCondition};

/// Lineage domain tag — distinct from every sibling lane.
const RECURSIVE_FUNCTIONAL_LINEAGE_DOMAIN: &str =
    "trust-certify.cleancic.recursive-datatype-functional.v2";

/// Property-tag prefixes of the emitted bundle (kept in lockstep with
/// `trust-vcgen/src/recursive_datatype_functional.rs`; the integration test
/// drives the literal emitted VCs through this lane).
const CASE_PROPERTY_PREFIX: &str = "recursive_datatype_functional_case::";
const CONCLUSION_PROPERTY_PREFIX: &str = "recursive_datatype_functional_conclusion";

// ---------------------------------------------------------------------------
// Bundle parsing: VCs -> induction plan.
// ---------------------------------------------------------------------------

/// One parsed constructor case.
struct CaseArm {
    /// Constructor name (from the case pattern; cross-checked against the
    /// VC's property tag).
    ctor: String,
    /// Pattern field variable names, in order.
    fields: Vec<String>,
    /// Sort of each field, parallel to `fields`. A field is RECURSIVE iff its
    /// sort is the modeled datatype `DT`; otherwise it is a non-recursive PAYLOAD
    /// (carries no IH; passed through unchanged by the model).
    field_sorts: Vec<Sort>,
    /// IH variables: `(ih_var_name, index of the RECURSIVE field it recurses on)`.
    ihs: Vec<(String, usize)>,
    /// The arm's result term over field/IH variables.
    result: Formula,
}

/// The parsed induction plan for one bundle.
struct InductionPlan {
    /// Kernel-safe datatype name (last `::` segment of the modeled name).
    dt: String,
    /// Full (qualified) datatype name — used to classify a field sort as the
    /// recursive `DT` vs a non-recursive payload.
    dt_full: String,
    /// Cases in constructor (variant) order.
    arms: Vec<CaseArm>,
    /// The scrutinee variable name of the conclusion.
    x: String,
    /// The postcondition rhs `rhs(x)` (a constructor tree over `x`).
    rhs: Formula,
    /// Stable label material: function name + property tags + conclusion.
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

/// Match the postcondition rhs (a term over the scrutinee variable `x`)
/// against an instance; return the term substituted for `x`. All occurrences
/// must agree; constructor spines must match exactly.
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

/// Parse the emitted bundle into an induction plan. `None` (fail-closed) on any
/// shape outside the supported scope.
fn parse_bundle(vcs: &[VerificationCondition]) -> Option<InductionPlan> {
    // 1. Split cases / conclusion by property tag, preserving case order.
    let mut cases: Vec<(&str, &VerificationCondition)> = Vec::new();
    let mut conclusion: Option<&VerificationCondition> = None;
    let mut function: Option<&str> = None;
    let mut properties: Vec<String> = Vec::new();
    for vc in vcs {
        let VcKind::FunctionalCorrectness { property, context } = &vc.kind else {
            return None;
        };
        match function {
            None => function = Some(context.as_str()),
            Some(f) if f == context => {}
            Some(_) => return None, // mixed-function bundle
        }
        properties.push(property.clone());
        if let Some(ctor) = property.strip_prefix(CASE_PROPERTY_PREFIX) {
            cases.push((ctor, vc));
        } else if property.starts_with(CONCLUSION_PROPERTY_PREFIX) {
            if conclusion.is_some() {
                return None;
            }
            conclusion = Some(vc);
        } else {
            return None;
        }
    }
    let conclusion = conclusion?;
    if cases.is_empty() {
        return None;
    }

    // 2. Conclusion: `Forall [(x, Datatype dt)] Eq(Var _0, rhs(x))`, whose
    //    `[induction:<dt>;cases=<n>]` tag must MATCH the bundle (a bundle with
    //    dropped/extra cases certifies nothing — coverage is part of the plan).
    let VcKind::FunctionalCorrectness { property: c_prop, .. } = &conclusion.kind else {
        return None;
    };
    let marker = c_prop.strip_prefix(CONCLUSION_PROPERTY_PREFIX)?;
    let marker = marker.strip_prefix("[induction:")?.strip_suffix(']')?;
    let (marker_dt, marker_cases) = marker.rsplit_once(";cases=")?;
    if marker_cases.parse::<usize>().ok()? != cases.len() {
        return None;
    }
    let (c_binders, c_body) = split_forall(&conclusion.formula);
    let [(x, x_sort)] = c_binders.as_slice() else {
        return None; // single-parameter scope
    };
    let Sort::Datatype { name: dt_full, .. } = x_sort else {
        return None;
    };
    if marker_dt != dt_full {
        return None;
    }
    let dt = dt_full.rsplit("::").next()?.to_string();
    let Formula::Eq(lhs, rhs) = c_body else {
        return None;
    };
    if lhs.var_name() != Some("_0") {
        return None;
    }
    let rhs = rhs.as_ref().clone();
    // rhs must be a constructor tree over `x` referencing it at least once
    // (otherwise the case patterns are unrecoverable).
    if !formula_mentions_var(&rhs, x) {
        return None;
    }

    // 3. Cases.
    let mut arms = Vec::with_capacity(cases.len());
    for (tag_ctor, vc) in cases {
        let (binders, body) = split_forall(&vc.formula);
        // Split binders into pattern fields (any sort — datatype-sorted fields
        // are recursive, other sorts are non-recursive payloads) and IH result
        // variables (`__ih` prefix by emission convention).
        let mut fields: Vec<String> = Vec::new();
        let mut field_sorts: Vec<Sort> = Vec::new();
        let mut ih_names: Vec<String> = Vec::new();
        for (name, sort) in &binders {
            if name.starts_with("__ih") {
                ih_names.push(name.clone());
            } else {
                fields.push(name.clone());
                field_sorts.push(sort.clone());
            }
        }
        let (ih_formulas, concl) = match body {
            Formula::Implies(ih, concl) => {
                let atoms: Vec<&Formula> = match ih.as_ref() {
                    Formula::And(parts) => parts.iter().collect(),
                    single => vec![single],
                };
                (atoms, concl.as_ref())
            }
            other => (Vec::new(), other),
        };
        if ih_formulas.len() != ih_names.len() {
            return None;
        }

        // Conclusion instance: `Eq(result, rhs[x := pattern])`.
        let Formula::Eq(res, rhs_inst) = concl else {
            return None;
        };
        let pattern = match_scrutinee(&rhs, rhs_inst, x)?;
        let Formula::Ctor { ctor, args, .. } = &pattern else {
            return None;
        };
        if ctor != tag_ctor {
            return None; // pattern must agree with the property tag
        }
        // Pattern args must be exactly the field variables, in order.
        if args.len() != fields.len()
            || !args.iter().zip(&fields).all(|(a, f)| a.var_name() == Some(f.as_str()))
        {
            return None;
        }

        // IH atoms: each is `Eq(Var ih_k, rhs[x := field])` — the postcondition
        // assumed at a structurally-smaller recursive call.
        let mut ihs = Vec::with_capacity(ih_formulas.len());
        for atom in ih_formulas {
            let Formula::Eq(ih_var, ih_rhs) = atom else {
                return None;
            };
            let ih_name = ih_var.var_name()?;
            if !ih_names.iter().any(|n| n == ih_name) {
                return None;
            }
            let arg = match_scrutinee(&rhs, ih_rhs, x)?;
            let field_idx = fields.iter().position(|f| arg.var_name() == Some(f.as_str()))?;
            ihs.push((ih_name.to_string(), field_idx));
        }

        // One IH per RECURSIVE (datatype-sorted) field, no more, no fewer.
        let recursive_count = field_sorts.iter().filter(|s| is_datatype_sort(s, dt_full)).count();
        if ihs.len() != recursive_count {
            return None;
        }
        // Every IH must recurse on a datatype-sorted (recursive) field.
        if !ihs
            .iter()
            .all(|(_, idx)| field_sorts.get(*idx).is_some_and(|s| is_datatype_sort(s, dt_full)))
        {
            return None;
        }

        arms.push(CaseArm {
            ctor: ctor.clone(),
            fields,
            field_sorts,
            ihs,
            result: res.as_ref().clone(),
        });
    }

    // 4. Supported constructor shapes: nullary; or a constructor with N >= 1
    //    fields where the arm result is the constructor applied slot-for-slot to
    //    — the IH for each RECURSIVE (datatype-sorted) field, and the field
    //    variable itself for each non-recursive PAYLOAD field ("rebuild each
    //    recursive child in place, pass payloads through"). N=1 all-recursive is
    //    the original unary case; N>=2 recursive is multi-IH `Max`/`IMax`;
    //    payload fields make it e.g. `param (n : Name)` / `Cons (h) (t)`-shaped.
    for arm in &arms {
        if arm.fields.is_empty() {
            if !arm.ihs.is_empty() || !formula_is_ground_ctor_tree(&arm.result) {
                return None;
            }
            continue;
        }
        let Formula::Ctor { args, .. } = &arm.result else {
            return None;
        };
        if args.len() != arm.fields.len() {
            return None;
        }
        for (k, arg) in args.iter().enumerate() {
            let recursive = is_datatype_sort(&arm.field_sorts[k], dt_full);
            if recursive {
                // slot k must be the IH that recurses on field k
                let Some(ih_k) = arm.ihs.iter().find(|(_, idx)| *idx == k) else {
                    return None;
                };
                if arg.var_name() != Some(ih_k.0.as_str()) {
                    return None;
                }
            } else {
                // payload slot k must be the field variable itself (passed through)
                if arg.var_name() != Some(arm.fields[k].as_str()) {
                    return None;
                }
            }
        }
    }

    let function = function?.to_string();
    let label = format!(
        "recursive_datatype_functional:{function}:[{}]:{:?}",
        properties.join(";"),
        conclusion.formula
    );
    Some(InductionPlan { dt, dt_full: dt_full.clone(), arms, x: x.to_string(), rhs, label })
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

fn formula_is_ground_ctor_tree(f: &Formula) -> bool {
    match f {
        Formula::Ctor { args, .. } => args.iter().all(formula_is_ground_ctor_tree),
        _ => false,
    }
}

/// A stable OPAQUE `Type`-constant name for a NON-DATATYPE SCALAR payload sort.
/// A `u32` field lowers to `Sort::BitVec(32)`, a `bool` to `Sort::Bool`, a raw
/// pointer / unmodeled scalar to `Sort::Int`. The scalar's internal structure is
/// irrelevant to an identity-family proof — the payload is held fixed — so it is
/// modeled by a fresh opaque `Type` the payload variable inhabits. `None` for a
/// datatype sort (handled by `payload_inductives`) or an unsupported compound
/// sort (`Array`/…), which fails closed.
fn scalar_type_name(sort: &Sort) -> Option<String> {
    match sort {
        Sort::Datatype { .. } => None,
        Sort::BitVec(w) => Some(format!("__TrustCertifyScalar_BitVec_{w}")),
        Sort::Bool => Some("__TrustCertifyScalar_Bool".to_string()),
        Sort::Int => Some("__TrustCertifyScalar_Int".to_string()),
        _ => None,
    }
}

/// Recursively collect (into `acc`, deduped, in first-seen order) the opaque
/// type name of every NON-datatype SCALAR sort reachable from `sort` — both at the
/// top level (a main-DT scalar field) AND nested inside payload-datatype
/// constructors (e.g. a `NameLike = Anon | Num(u32)` payload whose `Num` carries a
/// scalar). Name-only datatype references (`constructors: []`) terminate the walk.
fn collect_scalar_names(sort: &Sort, acc: &mut Vec<String>) {
    match sort {
        Sort::Datatype { constructors, .. } => {
            for (_, fields) in constructors {
                for (_, fsort) in fields {
                    collect_scalar_names(fsort, acc);
                }
            }
        }
        other => {
            if let Some(name) = scalar_type_name(other) {
                if !acc.contains(&name) {
                    acc.push(name);
                }
            }
        }
    }
}

/// Recursively record, into `acc` keyed by short name, every `Sort::Datatype`
/// that carries FULL constructor info (non-empty `constructors`). Name-only
/// references (`constructors: []`, the convention for a recursive self-mention)
/// are skipped — their full definition is picked up wherever it appears at top
/// level. Used to reconstruct payload datatypes (a self-recursive `Nat`, a
/// `Level`-shaped payload) from the sorts the arm field binders carry.
fn collect_full_defs(sort: &Sort, acc: &mut HashMap<String, Sort>) {
    let Sort::Datatype { name, constructors } = sort else {
        return;
    };
    if constructors.is_empty() {
        return;
    }
    if let Some(short) = name.rsplit("::").next() {
        acc.entry(short.to_string()).or_insert_with(|| sort.clone());
    }
    for (_, fields) in constructors {
        for (_, fsort) in fields {
            collect_full_defs(fsort, acc);
        }
    }
}

// ---------------------------------------------------------------------------
// CIC construction (raw kernel Expr, de Bruijn indices).
// ---------------------------------------------------------------------------

/// `DT : Type 0 = Sort 1` — `Eq`/`Eq.refl`/`congrArg` over it take `u = 1`.
fn level1() -> Level {
    Level::succ(Level::zero())
}

impl InductionPlan {
    fn dt_name(&self) -> Name {
        Name::from_string(&self.dt)
    }

    fn dt_expr(&self) -> Expr {
        Expr::const_(self.dt_name(), Vec::new())
    }

    fn ctor_const(&self, ctor: &str) -> Option<Expr> {
        // Only the datatype's own constructors are nameable.
        if !self.arms.iter().any(|a| a.ctor == ctor) {
            return None;
        }
        Some(Expr::const_(Name::from_string(&format!("{}.{ctor}", self.dt)), Vec::new()))
    }

    fn model_name(&self) -> Name {
        Name::from_string("__recursive_functional_model")
    }

    fn model_const(&self) -> Expr {
        Expr::const_(self.model_name(), Vec::new())
    }

    /// `Eq.{1} DT a b`.
    fn eq_dt(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(Expr::const_(Name::from_string("Eq"), vec![level1()]), [self.dt_expr(), a, b])
    }

    /// True iff `sort` is the recursive datatype `DT` (vs a non-recursive payload).
    fn is_recursive_sort(&self, sort: &Sort) -> bool {
        is_datatype_sort(sort, &self.dt_full)
    }

    /// The CIC type for a field sort: the recursive `DT`, a PAYLOAD datatype
    /// referenced by its short-name `Const` (reconstructed + registered by
    /// `payload_inductives` — a nullary enum `Bit`, a self-recursive `Nat`, a
    /// `Level`-shaped payload), or a NON-DATATYPE SCALAR payload (a `u32` field
    /// lowers to `Sort::BitVec(32)`, a `bool` to `Sort::Bool`, a raw pointer to
    /// `Sort::Int`) modeled by a fresh opaque `Type` constant (registered by
    /// `scalar_opaque_axioms`). Scalar payloads are held FIXED by identity-family
    /// proofs, so their internal structure is irrelevant — the opaque type only has
    /// to exist for the constructor to type-check. `None` (fail-closed) for an
    /// unsupported compound sort (`Array`/…).
    fn sort_type_expr(&self, sort: &Sort) -> Option<Expr> {
        if self.is_recursive_sort(sort) {
            return Some(self.dt_expr());
        }
        match sort {
            Sort::Datatype { name, .. } => {
                Some(Expr::const_(Name::from_string(name.rsplit("::").next()?), Vec::new()))
            }
            other => {
                scalar_type_name(other).map(|n| Expr::const_(Name::from_string(&n), Vec::new()))
            }
        }
    }

    /// Number of RECURSIVE (datatype-sorted) fields in an arm.
    fn recursive_count(&self, arm: &CaseArm) -> usize {
        arm.field_sorts.iter().filter(|s| self.is_recursive_sort(s)).count()
    }

    /// 0-based position of the field at `field_idx` among the RECURSIVE fields
    /// (how many recursive fields precede it) — the IH-binder ordering.
    fn recursive_position(&self, arm: &CaseArm, field_idx: usize) -> usize {
        arm.field_sorts[..field_idx].iter().filter(|s| self.is_recursive_sort(s)).count()
    }

    /// The distinct PAYLOAD datatypes referenced by any arm's fields,
    /// reconstructed as real inductives and returned in dependency order (each
    /// registered before every datatype that references it, so `build_env` can
    /// `add_inductive` them ahead of `DT`). A payload may be a nullary-ctor enum
    /// (`Bit`), a self-recursive inductive (`Nat = Z | S (Nat)`), or a
    /// multi-field one — the constructor shape real `Expr` payloads (`Level`,
    /// `Name`) carry. Self-references are intra-decl; each constructor field must
    /// be the payload itself or another collected payload. `None` (fail-closed) if
    /// a field sort is a non-datatype, references an uncollected datatype, or the
    /// payloads form a cross-cycle (a mutual-inductive block — out of scope here).
    fn payload_inductives(&self) -> Option<Vec<InductiveDecl>> {
        // 1. Gather the FULL definition of every datatype any arm field mentions
        //    (top-level occurrences carry full constructors; name-only references
        //    `constructors: []` are resolved wherever they appear in full).
        let mut full: HashMap<String, Sort> = HashMap::new();
        for arm in &self.arms {
            for sort in &arm.field_sorts {
                collect_full_defs(sort, &mut full);
            }
        }
        // The modeled datatype is registered separately; never as a payload.
        full.remove(&self.dt);

        // 2. Reconstruct each payload's InductiveDecl + its cross-dependencies
        //    (referenced short-names other than itself). Deterministic order.
        let mut shorts: Vec<&String> = full.keys().collect();
        shorts.sort();
        let mut pending: Vec<(String, InductiveDecl, Vec<String>)> = Vec::new();
        for short in shorts {
            let Some(Sort::Datatype { constructors, .. }) = full.get(short) else {
                return None;
            };
            let dt_ref = Expr::const_(Name::from_string(short), vec![]);
            let mut ctors = Vec::with_capacity(constructors.len());
            let mut deps: Vec<String> = Vec::new();
            for (cname, fields) in constructors {
                // Constructor type `F_0 -> ... -> F_{m-1} -> Payload`. A field is a
                // datatype (this payload, or another collected one) or a NESTED
                // non-datatype SCALAR (`Num(u32)`) resolved to its opaque `Type`.
                let mut type_ = dt_ref.clone();
                for (_, fsort) in fields.iter().rev() {
                    let field_ty = match fsort {
                        Sort::Datatype { name: fname, .. } => {
                            let fshort = fname.rsplit("::").next()?.to_string();
                            if fshort != *short && !full.contains_key(&fshort) {
                                return None; // references an uncollected datatype
                            }
                            if fshort != *short && !deps.contains(&fshort) {
                                deps.push(fshort.clone());
                            }
                            Expr::const_(Name::from_string(&fshort), vec![])
                        }
                        // A NESTED scalar payload field: the opaque `Type` constant
                        // registered by `scalar_opaque_axioms` ahead of all payloads.
                        other => Expr::const_(Name::from_string(&scalar_type_name(other)?), vec![]),
                    };
                    type_ = Expr::pi(BinderInfo::Default, field_ty, type_);
                }
                ctors.push(Constructor {
                    name: Name::from_string(&format!("{short}.{cname}")),
                    type_,
                });
            }
            pending.push((
                short.clone(),
                InductiveDecl {
                    level_params: vec![],
                    num_params: 0,
                    types: vec![InductiveType {
                        name: Name::from_string(short),
                        type_: Expr::type_(),
                        constructors: ctors,
                    }],
                },
                deps,
            ));
        }

        // 3. Topologically order: emit a payload only once all OTHER payloads it
        //    references are emitted (self-references are handled within the decl).
        //    No progress in a full pass => a cross-cycle => fail closed.
        let mut ordered: Vec<InductiveDecl> = Vec::new();
        let mut done: Vec<String> = Vec::new();
        while done.len() < pending.len() {
            let mut progressed = false;
            for (short, decl, deps) in &pending {
                if done.contains(short) {
                    continue;
                }
                if deps.iter().all(|d| done.contains(d)) {
                    ordered.push(decl.clone());
                    done.push(short.clone());
                    progressed = true;
                }
            }
            if !progressed {
                return None;
            }
        }
        Some(ordered)
    }

    /// Convert a bundle `Formula` term to a CIC term. `ctx` maps variable names
    /// to their de Bruijn LEVEL; `depth` is the current binder depth.
    fn term_to_cic(&self, f: &Formula, ctx: &HashMap<String, usize>, depth: usize) -> Option<Expr> {
        if let Some(name) = f.var_name() {
            let level = *ctx.get(name)?;
            return Some(Expr::bvar((depth - 1 - level) as u32));
        }
        match f {
            Formula::Ctor { ctor, args, .. } => {
                let head = self.ctor_const(ctor)?;
                let mut expr = head;
                for arg in args {
                    expr = Expr::app(expr, self.term_to_cic(arg, ctx, depth)?);
                }
                Some(expr)
            }
            _ => None,
        }
    }

    /// `rhs[x := t]` as CIC, where `t` is already a CIC term at the current depth.
    fn rhs_cic_at(&self, t: &Expr, ctx: &HashMap<String, usize>, depth: usize) -> Option<Expr> {
        self.rhs_subst_cic(&self.rhs, t, ctx, depth)
    }

    fn rhs_subst_cic(
        &self,
        f: &Formula,
        t: &Expr,
        ctx: &HashMap<String, usize>,
        depth: usize,
    ) -> Option<Expr> {
        if f.var_name() == Some(self.x.as_str()) {
            return Some(t.clone());
        }
        if let Some(name) = f.var_name() {
            let level = *ctx.get(name)?;
            return Some(Expr::bvar((depth - 1 - level) as u32));
        }
        match f {
            Formula::Ctor { ctor, args, .. } => {
                let mut expr = self.ctor_const(ctor)?;
                for arg in args {
                    expr = Expr::app(expr, self.rhs_subst_cic(arg, t, ctx, depth)?);
                }
                Some(expr)
            }
            _ => None,
        }
    }

    /// The reconstructed inductive declaration:
    /// `inductive DT : Type where | c0 ... | c{n-1}` in case order. Each
    /// constructor's field types come from the parsed field sorts (the recursive
    /// `DT` or a payload type), so payload-carrying constructors like
    /// `param (n : Name)` / `Cons (h : α) (t : DT)` reconstruct faithfully.
    /// `None` if any field sort is unsupported (fail-closed).
    fn inductive_decl(&self) -> Option<InductiveDecl> {
        let dt_ref = self.dt_expr();
        let mut constructors = Vec::with_capacity(self.arms.len());
        for arm in &self.arms {
            // Constructor type `T_0 -> ... -> T_{N-1} -> DT` (T_k the field's type).
            let mut type_ = dt_ref.clone();
            for sort in arm.field_sorts.iter().rev() {
                type_ = Expr::pi(BinderInfo::Default, self.sort_type_expr(sort)?, type_);
            }
            constructors.push(Constructor {
                name: Name::from_string(&format!("{}.{}", self.dt, arm.ctor)),
                type_,
            });
        }
        Some(InductiveDecl {
            level_params: vec![],
            num_params: 0,
            types: vec![InductiveType { name: self.dt_name(), type_: Expr::type_(), constructors }],
        })
    }

    /// The MODEL function built from the arm results:
    /// `fun (x:DT) => DT.rec.{1} (fun _ => DT) <arm results> x`.
    fn model_value(&self) -> Option<Expr> {
        let motive = Expr::lam(BinderInfo::Default, self.dt_expr(), self.dt_expr());
        let mut rec_args = vec![motive];
        for arm in &self.arms {
            if arm.fields.is_empty() {
                // Closed constructor tree; no binders.
                rec_args.push(self.term_to_cic(&arm.result, &HashMap::new(), 0)?);
            } else {
                // Minor: `fun (f_0..f_{N-1} : T_k) (ih_0..ih_{R-1} : DT) => result`,
                // R = recursive-field count. Recursor minor = all-fields-then-IHs
                // (one IH per RECURSIVE field, in recursive-field order): f_k at
                // level 1+k; the IH of the r-th recursive field at 1+N+r; body
                // depth 1+N+R.
                let n = arm.fields.len();
                let r = self.recursive_count(arm);
                let mut ctx = HashMap::new();
                for (k, field) in arm.fields.iter().enumerate() {
                    ctx.insert(field.clone(), 1 + k);
                }
                for (ih_name, field_idx) in &arm.ihs {
                    ctx.insert(ih_name.clone(), 1 + n + self.recursive_position(arm, *field_idx));
                }
                let body = self.term_to_cic(&arm.result, &ctx, 1 + n + r)?;
                // wrap R IH binders (DT-typed, innermost) then N field binders
                // (each its own type, reversed so f_0 is outermost).
                let mut lam = body;
                for _ in 0..r {
                    lam = Expr::lam(BinderInfo::Default, self.dt_expr(), lam);
                }
                for sort in arm.field_sorts.iter().rev() {
                    lam = Expr::lam(BinderInfo::Default, self.sort_type_expr(sort)?, lam);
                }
                rec_args.push(lam);
            }
        }
        rec_args.push(Expr::bvar(0)); // the outer x
        let rec_app = Expr::apps(
            Expr::const_(Name::from_string(&format!("{}.rec", self.dt)), vec![level1()]),
            rec_args,
        );
        Some(Expr::lam(BinderInfo::Default, self.dt_expr(), rec_app))
    }

    fn model_type(&self) -> Expr {
        Expr::pi(BinderInfo::Default, self.dt_expr(), self.dt_expr())
    }

    /// The goal — the conclusion VC with `_0` bound to the model's output:
    /// `forall (x:DT), Eq DT (model x) rhs(x)`.
    fn goal(&self) -> Option<Expr> {
        let ctx = HashMap::new();
        // Under the pi binder: x at level 0, depth 1.
        let model_x = Expr::app(self.model_const(), Expr::bvar(0));
        let rhs_x = self.rhs_cic_at(&Expr::bvar(0), &ctx, 1)?;
        Some(Expr::pi(BinderInfo::Default, self.dt_expr(), self.eq_dt(model_x, rhs_x)))
    }

    /// The GENERATED induction proof:
    /// `fun (x:DT) => DT.rec.{0} (motive := fun y => Eq (model y) rhs(y))
    ///    <minor premises from the case VCs> x`.
    fn proof(&self) -> Option<Expr> {
        let ctx = HashMap::new();
        // motive := fun (y:DT) => Eq (model y) rhs(y)   (y at depth 2 under fun x, fun y)
        let motive_body = self.eq_dt(
            Expr::app(self.model_const(), Expr::bvar(0)),
            self.rhs_cic_at(&Expr::bvar(0), &ctx, 2)?,
        );
        let motive = Expr::lam(BinderInfo::Default, self.dt_expr(), motive_body);

        let mut rec_args = vec![motive];
        for arm in &self.arms {
            if arm.fields.is_empty() {
                // base minor: Eq.refl.{1} DT (rhs[x := C]) — the kernel accepts
                // it against `Eq (model C) (rhs C)` iff the arm result is
                // def-eq to the instantiated postcondition (iota + delta).
                let pattern = self.ctor_const(&arm.ctor)?;
                let inst = self.rhs_cic_at(&pattern, &ctx, 1)?; // closed; depth irrelevant
                rec_args.push(Expr::apps(
                    Expr::const_(Name::from_string("Eq.refl"), vec![level1()]),
                    [self.dt_expr(), inst],
                ));
            } else {
                // step minor over an N-recursive-field constructor: N congrArgs
                // (one per field, rewriting `model f_k` to `rhs f_k` via `ih_k`)
                // joined by `Eq.trans`. N=1 is the original single-congrArg case.
                rec_args.push(self.build_step_minor(arm, &ctx)?);
            }
        }
        rec_args.push(Expr::bvar(0)); // the outer x
        let rec_app = Expr::apps(
            Expr::const_(Name::from_string(&format!("{}.rec", self.dt)), vec![Level::zero()]),
            rec_args,
        );
        Some(Expr::lam(BinderInfo::Default, self.dt_expr(), rec_app))
    }

    /// The step minor for a constructor `C'` with N fields, R of them recursive:
    /// `fun (f_0..f_{N-1} : T_k) (ih_0..ih_{R-1} : Eq (model f) (rhs f)) =>
    ///     <R congrArgs chained by Eq.trans>`, proving
    /// `Eq (model (C' f...)) (rhs (C' f...))`. The model iota-reduces the RECURSIVE
    /// slots (`model f_k`) while PAYLOAD slots pass through unchanged on both
    /// sides; each recursive slot is rewritten `model f_k` -> `rhs f_k` by
    /// `congrArg` on its IH, folded left-to-right over the recursive fields only.
    /// R=N (all recursive) is the multi-IH case; R=1 the original unary step;
    /// payload slots are held fixed.
    ///
    /// Binder levels (recursor minor = all-fields-then-IHs; one IH per recursive
    /// field, in recursive-field order; under the outer `fun x` at level 0): field
    /// `f_k` at `1+k`, the IH of the r-th recursive field at `1+N+r`; body depth
    /// `1+N+R`. `bv` converts a level to a de Bruijn index (saturating, so a
    /// malformed bundle fails the kernel check rather than panicking).
    fn build_step_minor(&self, arm: &CaseArm, outer_ctx: &HashMap<String, usize>) -> Option<Expr> {
        let n = arm.fields.len();
        let Formula::Ctor { ctor: result_ctor, .. } = &arm.result else {
            return None;
        };
        let rec_idx: Vec<usize> =
            (0..n).filter(|&k| self.is_recursive_sort(&arm.field_sorts[k])).collect();
        let r = rec_idx.len();
        let d = 1 + n + r; // outer `fun x` + N field binders + R IH binders
        let bv = |level: usize, depth: usize| {
            Expr::bvar(depth.saturating_sub(1).saturating_sub(level) as u32)
        };
        // Arg at field position `i`, at `depth`, with `rewritten` recursive slots
        // already rewritten to `rhs`: payload -> the field var; recursive ->
        // `rhs f_i` if its recursive-position < rewritten, else `model f_i`.
        let arg_at = |i: usize, depth: usize, rewritten: usize| -> Option<Expr> {
            if self.is_recursive_sort(&arm.field_sorts[i]) {
                let rpos = rec_idx.iter().position(|&j| j == i)?;
                if rpos < rewritten {
                    self.rhs_cic_at(&bv(1 + i, depth), outer_ctx, depth)
                } else {
                    Some(Expr::app(self.model_const(), bv(1 + i, depth)))
                }
            } else {
                Some(bv(1 + i, depth)) // payload passthrough
            }
        };
        let apply_ctor = |args: &[Expr]| -> Option<Expr> {
            let mut e = self.ctor_const(result_ctor)?;
            for a in args {
                e = Expr::app(e, a.clone());
            }
            Some(e)
        };

        // ALL-PAYLOAD constructor (fields but no recursive field, e.g. `Lit(v:Bit)`):
        // `model (C' fields) ≡ rhs (C' fields)` by iota — no IH needed — closed by
        // `Eq.refl DT (rhs (C' fields))`, wrapped in the field binders.
        if rec_idx.is_empty() {
            let args: Vec<Expr> = (0..n).map(|k| bv(1 + k, d)).collect();
            let inst = self.rhs_cic_at(&apply_ctor(&args)?, outer_ctx, d)?;
            let mut term = Expr::apps(
                Expr::const_(Name::from_string("Eq.refl"), vec![level1()]),
                [self.dt_expr(), inst],
            );
            for sort in arm.field_sorts.iter().rev() {
                term = Expr::lam(BinderInfo::Default, self.sort_type_expr(sort)?, term);
            }
            return Some(term);
        }

        // Fold the R-fold congrArg chain (one per recursive field) with Eq.trans.
        let mut proof: Option<Expr> = None;
        for (rewritten, &k) in rec_idx.iter().enumerate() {
            // f_k function: `fun (z:DT) => C'(args, slot k = z, rewritten = current)`,
            // built one binder deeper (depth d+1).
            let mut fn_args: Vec<Expr> = Vec::with_capacity(n);
            for i in 0..n {
                if i == k {
                    fn_args.push(Expr::bvar(0)); // z
                } else {
                    fn_args.push(arg_at(i, d + 1, rewritten)?);
                }
            }
            let fk_fn = Expr::lam(BinderInfo::Default, self.dt_expr(), apply_ctor(&fn_args)?);
            let step = Expr::apps(
                Expr::const_(Name::from_string("congrArg"), vec![level1(), level1()]),
                [
                    self.dt_expr(),
                    self.dt_expr(),
                    Expr::app(self.model_const(), bv(1 + k, d)), // a₁ = model f_k
                    self.rhs_cic_at(&bv(1 + k, d), outer_ctx, d)?, // a₂ = rhs f_k
                    fk_fn,
                    bv(1 + n + rewritten, d), // h = ih of the r-th recursive field
                ],
            );
            proof = Some(match proof.take() {
                None => step,
                Some(acc) => {
                    let mut t0 = Vec::with_capacity(n);
                    let mut tk = Vec::with_capacity(n);
                    let mut tk1 = Vec::with_capacity(n);
                    for i in 0..n {
                        t0.push(arg_at(i, d, 0)?);
                        tk.push(arg_at(i, d, rewritten)?);
                        tk1.push(arg_at(i, d, rewritten + 1)?);
                    }
                    Expr::apps(
                        Expr::const_(Name::from_string("Eq.trans"), vec![level1()]),
                        [
                            self.dt_expr(),
                            apply_ctor(&t0)?,
                            apply_ctor(&tk)?,
                            apply_ctor(&tk1)?,
                            acc,
                            step,
                        ],
                    )
                }
            });
        }
        let mut term = proof?;

        // Wrap IH binders innermost-first (recursive-field order). The IH of the
        // r-th recursive field (field `k`): Eq (model f_k) (rhs f_k), at its binder
        // depth 1+N+r, where f_k = bv(1+k, 1+N+r).
        for (rpos, &k) in rec_idx.iter().enumerate().rev() {
            let dep = 1 + n + rpos;
            let ih_ty = self.eq_dt(
                Expr::app(self.model_const(), bv(1 + k, dep)),
                self.rhs_cic_at(&bv(1 + k, dep), outer_ctx, dep)?,
            );
            term = Expr::lam(BinderInfo::Default, ih_ty, term);
        }
        // Wrap the N field binders (each its own type; reversed so f_0 outermost).
        for sort in arm.field_sorts.iter().rev() {
            term = Expr::lam(BinderInfo::Default, self.sort_type_expr(sort)?, term);
        }
        Some(term)
    }

    /// The refl-only PSEUDO-proof `fun x => Eq.refl DT (model x)` — well-typed,
    /// but its type is `Eq (model x) (model x)`, NOT the goal (`model x` is
    /// stuck on the free `x`). The kernel must reject it against the goal.
    fn refl_only_pseudo_proof(&self) -> Expr {
        let refl = Expr::apps(
            Expr::const_(Name::from_string("Eq.refl"), vec![level1()]),
            [self.dt_expr(), Expr::app(self.model_const(), Expr::bvar(0))],
        );
        Expr::lam(BinderInfo::Default, self.dt_expr(), refl)
    }

    /// One opaque `Type` axiom per DISTINCT non-datatype SCALAR sort any arm field
    /// carries — at the top level (`u32` -> `Sort::BitVec(32)`, `bool` ->
    /// `Sort::Bool`, …) OR nested inside a payload datatype's constructors (via
    /// `collect_scalar_names`). Registered ahead of every datatype so a constructor
    /// like `KVar : <scalar> -> DT` (or a payload `Num : <scalar> -> NameLike`)
    /// type-checks. The axiom is a bare `T : Type` — no inhabitant is assumed and
    /// none is needed (the scalar payload is a bound variable held fixed by the
    /// identity proof), so this introduces no domain assumption about the scalar.
    fn scalar_opaque_axioms(&self) -> Vec<Declaration> {
        let mut names: Vec<String> = Vec::new();
        for arm in &self.arms {
            for sort in &arm.field_sorts {
                collect_scalar_names(sort, &mut names);
            }
        }
        names
            .into_iter()
            .map(|name| Declaration::Axiom {
                name: Name::from_string(&name),
                level_params: vec![],
                type_: Expr::type_(),
            })
            .collect()
    }

    /// Build the kernel environment: `Eq` (+ `Eq.refl`, `congrArg`), the opaque
    /// scalar-payload types, the reconstructed inductive (=> `DT.rec` + iota), and
    /// the model definition (registering it kernel-type-checks the `.rec` fold
    /// against `DT -> DT`).
    fn build_env_from(&self, mut env: Environment) -> Option<Environment> {
        env.init_eq().ok()?;
        // Register the opaque scalar payload types (u32/bool/… -> `Type`) first —
        // constructor field types of DT reference them.
        for axiom in self.scalar_opaque_axioms() {
            env.add_decl(axiom).ok()?;
        }
        // Register any PAYLOAD datatypes next (field types of DT reference them).
        for payload in self.payload_inductives()? {
            env.add_inductive(payload).ok()?;
        }
        env.add_inductive(self.inductive_decl()?).ok()?;
        env.add_decl(Declaration::Definition {
            name: self.model_name(),
            level_params: vec![],
            type_: self.model_type(),
            value: self.model_value()?,
            is_reducible: true,
        })
        .ok()?;
        Some(env)
    }

    /// Build the smallest proof environment needed by this lane.  In
    /// particular, do not inherit `Environment::new()`'s polymorphic `sorry`,
    /// `trustedArith`, or `trustedAy` axioms into an evidence-recheck boundary.
    fn build_env(&self) -> Option<Environment> {
        self.build_env_from(Environment::default())
    }

    /// Test-only reproduction of the formerly vulnerable ambient environment:
    /// it demonstrates that `@sorry goal` is well typed there, so the forged-term
    /// rejection regression below is authority-bearing rather than malformed.
    #[cfg(test)]
    fn build_env_with_ambient_trust_markers(&self) -> Option<Environment> {
        self.build_env_from(Environment::new())
    }
}

/// Full kernel re-check (`infer_only = false`) that `term : goal` in the empty
/// closed context.
fn kernel_checks_goal(env: &Environment, term: &Expr, goal: &Expr) -> bool {
    TypeChecker::with_context(env, LocalContext::new()).check_type(term, goal).is_ok()
}

/// SHA-256 lineage digest binding the canonical term/context and the complete
/// serialized VC bundle (the label remains an explicit domain-readable field).
fn recursive_functional_lineage_digest(
    vcs: &[VerificationCondition],
    term_bytes: &[u8],
    context_bytes: &[u8],
    label: &str,
) -> Option<trust_ir::ProofDigest> {
    let encoded_vcs = bincode::serialize(vcs).ok()?;
    let mut hasher = Sha256::new();
    hasher.update(RECURSIVE_FUNCTIONAL_LINEAGE_DOMAIN.as_bytes());
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

fn canonical_empty_context_bytes() -> Option<Vec<u8>> {
    serialize_context(&ReducedContext { decls: Vec::new() }).ok()
}

/// Mint a kernel-CHECKED `CleanCic` certificate discharging a recursive-
/// datatype-functional induction bundle (the VCs emitted by trust-vcgen's
/// `recursive_datatype_functional` lane) by a GENERATED `.rec` induction term.
///
/// Fail-closed on every count: unsupported bundle shapes parse to `None`; a
/// false postcondition's generated proof is REJECTED by the clean kernel; the
/// serialized payload must re-check after a round-trip.
#[must_use]
pub fn certify_recursive_datatype_functional(
    vcs: &[VerificationCondition],
) -> Option<trust_ir::ProofEvidence> {
    let plan = parse_bundle(vcs)?;
    let env = plan.build_env()?;
    let goal = plan.goal()?;
    let proof = plan.proof()?;

    // TCB gate: the clean kernel independently type-checks the induction term.
    if !kernel_checks_goal(&env, &proof, &goal) {
        return None;
    }

    let term_bytes = serialize_term(&proof).ok()?;
    let context_bytes = canonical_empty_context_bytes()?;
    let lineage =
        recursive_functional_lineage_digest(vcs, &term_bytes, &context_bytes, &plan.label)?;
    if !recheck_recursive_datatype_functional(vcs, &term_bytes, &context_bytes, &lineage) {
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
pub fn recheck_recursive_datatype_functional(
    vcs: &[VerificationCondition],
    term_bytes: &[u8],
    context_bytes: &[u8],
    lineage: &trust_ir::ProofDigest,
) -> bool {
    if canonical_empty_context_bytes().as_deref() != Some(context_bytes) {
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

    // Accept exactly the proof this independently rebuilt induction plan emits,
    // never merely "any term" the ambient kernel can assign the goal.  Without
    // this authority pin, a caller can submit polymorphic `@sorry goal` and
    // recompute the public lineage digest.
    let Some(canonical_proof) = plan.proof() else {
        return false;
    };
    let Ok(canonical_term_bytes) = serialize_term(&canonical_proof) else {
        return false;
    };
    if term_bytes != canonical_term_bytes.as_slice() {
        return false;
    }
    let Ok(term) = deserialize_term(term_bytes) else {
        return false;
    };
    if !kernel_checks_goal(&env, &term, &goal) {
        return false;
    }
    recursive_functional_lineage_digest(vcs, term_bytes, context_bytes, &plan.label).as_ref()
        == Some(lineage)
}

/// LOAD-BEARING-IH witness for a bundle: `true` iff the goal builds AND the
/// refl-only pseudo-proof (no induction, no IH) is REJECTED by the kernel while
/// the generated `.rec` induction proof is ACCEPTED. This is the no-masquerade
/// asymmetry (`level_recursive_functional`'s `mirror_id_requires_induction`),
/// now machine-checked on the emitted bundle.
#[must_use]
pub fn induction_is_load_bearing(vcs: &[VerificationCondition]) -> bool {
    let Some(plan) = parse_bundle(vcs) else {
        return false;
    };
    let (Some(env), Some(goal), Some(proof)) = (plan.build_env(), plan.goal(), plan.proof()) else {
        return false;
    };
    kernel_checks_goal(&env, &proof, &goal)
        && !kernel_checks_goal(&env, &plan.refl_only_pseudo_proof(), &goal)
}

#[cfg(test)]
mod tests {
    use trust_ir::ProofEvidence;
    use trust_types::{SourceSpan, VcKind};

    use super::*;

    // ── Bundle builders: the EXACT shapes trust-vcgen emits for the extracted
    //    `mirror : &Level -> Level` fixture (pinned by the trust-vcgen unit
    //    tests and driven literally in trust-integration-tests). ──────────────

    fn level_sort() -> Sort {
        Sort::Datatype {
            name: "level::Level".to_string(),
            constructors: vec![
                ("Zero".to_string(), vec![]),
                (
                    "Succ".to_string(),
                    vec![(
                        "0".to_string(),
                        Sort::Datatype { name: "level::Level".to_string(), constructors: vec![] },
                    )],
                ),
            ],
        }
    }

    fn var(name: &str) -> Formula {
        Formula::var_owned(name.to_string(), level_sort())
    }

    fn ctor(name: &str, args: Vec<Formula>) -> Formula {
        Formula::Ctor { ctor: name.to_string(), args, sort: level_sort() }
    }

    fn vc(property: &str, formula: Formula) -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::FunctionalCorrectness {
                property: property.to_string(),
                context: "mirror".to_string(),
            },
            function: "mirror".into(),
            location: SourceSpan::default(),
            formula,
            contract_metadata: None,
        }
    }

    /// The emitted bundle for the TRUE postcondition `mirror l = l`.
    fn mirror_identity_bundle() -> Vec<VerificationCondition> {
        let zero_case = Formula::Eq(Box::new(ctor("Zero", vec![])), Box::new(ctor("Zero", vec![])));
        let succ_case = Formula::forall(
            &[("__fld_Succ_0", level_sort()), ("__ih0", level_sort())],
            Formula::Implies(
                Box::new(Formula::Eq(Box::new(var("__ih0")), Box::new(var("__fld_Succ_0")))),
                Box::new(Formula::Eq(
                    Box::new(ctor("Succ", vec![var("__ih0")])),
                    Box::new(ctor("Succ", vec![var("__fld_Succ_0")])),
                )),
            ),
        );
        let conclusion = Formula::forall(
            &[("l", level_sort())],
            Formula::Eq(Box::new(var("_0")), Box::new(var("l"))),
        );
        vec![
            vc("recursive_datatype_functional_case::Zero", zero_case),
            vc("recursive_datatype_functional_case::Succ", succ_case),
            vc(
                "recursive_datatype_functional_conclusion[induction:level::Level;cases=2]",
                conclusion,
            ),
        ]
    }

    /// The emitted bundle for the FALSE postcondition `mirror l = Succ l`
    /// (same emission lane, wrong spec) — the negative control.
    fn mirror_wrong_succ_bundle() -> Vec<VerificationCondition> {
        let zero_case = Formula::Eq(
            Box::new(ctor("Zero", vec![])),
            Box::new(ctor("Succ", vec![ctor("Zero", vec![])])),
        );
        let succ_case = Formula::forall(
            &[("__fld_Succ_0", level_sort()), ("__ih0", level_sort())],
            Formula::Implies(
                Box::new(Formula::Eq(
                    Box::new(var("__ih0")),
                    Box::new(ctor("Succ", vec![var("__fld_Succ_0")])),
                )),
                Box::new(Formula::Eq(
                    Box::new(ctor("Succ", vec![var("__ih0")])),
                    Box::new(ctor("Succ", vec![ctor("Succ", vec![var("__fld_Succ_0")])])),
                )),
            ),
        );
        let conclusion = Formula::forall(
            &[("l", level_sort())],
            Formula::Eq(Box::new(var("_0")), Box::new(ctor("Succ", vec![var("l")]))),
        );
        vec![
            vc("recursive_datatype_functional_case::Zero", zero_case),
            vc("recursive_datatype_functional_case::Succ", succ_case),
            vc(
                "recursive_datatype_functional_conclusion[induction:level::Level;cases=2]",
                conclusion,
            ),
        ]
    }

    // ── MULTI-IH bundle: `BTree = Leaf | Node (BTree) (BTree)`, rebuild = id ──
    //    the two-recursive-field (`Max`/`IMax`-shaped) case.

    fn btree_sort() -> Sort {
        let bt = || Sort::Datatype { name: "btree::BTree".to_string(), constructors: vec![] };
        Sort::Datatype {
            name: "btree::BTree".to_string(),
            constructors: vec![
                ("Leaf".to_string(), vec![]),
                ("Node".to_string(), vec![("0".to_string(), bt()), ("1".to_string(), bt())]),
            ],
        }
    }
    fn bt_var(name: &str) -> Formula {
        Formula::var_owned(name.to_string(), btree_sort())
    }
    fn bt_ctor(name: &str, args: Vec<Formula>) -> Formula {
        Formula::Ctor { ctor: name.to_string(), args, sort: btree_sort() }
    }
    fn bt_vc(property: &str, formula: Formula) -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::FunctionalCorrectness {
                property: property.to_string(),
                context: "rebuild".to_string(),
            },
            function: "rebuild".into(),
            location: SourceSpan::default(),
            formula,
            contract_metadata: None,
        }
    }

    /// Emitted bundle for the TRUE multi-IH postcondition `rebuild t = t` over
    /// `Node` (two recursive fields, two IHs consumed).
    fn rebuild_identity_bundle() -> Vec<VerificationCondition> {
        let leaf_case =
            Formula::Eq(Box::new(bt_ctor("Leaf", vec![])), Box::new(bt_ctor("Leaf", vec![])));
        let node_case = Formula::forall(
            &[
                ("__fld_Node_0", btree_sort()),
                ("__fld_Node_1", btree_sort()),
                ("__ih0", btree_sort()),
                ("__ih1", btree_sort()),
            ],
            Formula::Implies(
                Box::new(Formula::And(vec![
                    Formula::Eq(Box::new(bt_var("__ih0")), Box::new(bt_var("__fld_Node_0"))),
                    Formula::Eq(Box::new(bt_var("__ih1")), Box::new(bt_var("__fld_Node_1"))),
                ])),
                Box::new(Formula::Eq(
                    Box::new(bt_ctor("Node", vec![bt_var("__ih0"), bt_var("__ih1")])),
                    Box::new(bt_ctor("Node", vec![bt_var("__fld_Node_0"), bt_var("__fld_Node_1")])),
                )),
            ),
        );
        let conclusion = Formula::forall(
            &[("t", btree_sort())],
            Formula::Eq(Box::new(bt_var("_0")), Box::new(bt_var("t"))),
        );
        vec![
            bt_vc("recursive_datatype_functional_case::Leaf", leaf_case),
            bt_vc("recursive_datatype_functional_case::Node", node_case),
            bt_vc(
                "recursive_datatype_functional_conclusion[induction:btree::BTree;cases=2]",
                conclusion,
            ),
        ]
    }

    /// THE MULTI-IH MILESTONE: the auto-generator emits a `BTree.rec` induction
    /// term whose `Node` minor consumes BOTH IHs (two `congrArg`s + `Eq.trans`),
    /// and the clean kernel accepts it — mechanizing the hand-built primitive from
    /// `tests/multi_ih_recursive_functional.rs`.
    #[test]
    fn certify_rebuild_identity_multi_ih_bundle() {
        let bundle = rebuild_identity_bundle();
        let evidence = certify_recursive_datatype_functional(&bundle).expect(
            "the multi-IH rebuild-identity bundle must certify to a kernel-checked CleanCic",
        );
        assert!(matches!(evidence, ProofEvidence::CleanCic { .. }));
        assert!(
            induction_is_load_bearing(&bundle),
            "multi-IH induction must be load-bearing (refl-only rejected, generated proof accepted)"
        );
    }

    /// MULTI-IH NEGATIVE CONTROL: a well-formed bundle for the FALSE postcondition
    /// `rebuild t = Node t t` (the same emission lane from a wrong spec) over the
    /// two-recursive-field `Node`. It PARSES and BUILDS a plan/env/goal/candidate
    /// proof (not a malformation), and the clean KERNEL rejects the generated term
    /// (the `Leaf` base minor's `Eq.refl (Node Leaf Leaf)` does not type-check
    /// against `Eq (model Leaf = Leaf) (Node Leaf Leaf)`) — no certificate. This
    /// extends the unary `wrong_postcondition_bundle_rejected_by_kernel` witness
    /// to the multi-IH surface.
    fn rebuild_wrong_node_bundle() -> Vec<VerificationCondition> {
        let node2 = |a: Formula, b: Formula| bt_ctor("Node", vec![a, b]);
        let leaf = || bt_ctor("Leaf", vec![]);
        let leaf_case = Formula::Eq(Box::new(leaf()), Box::new(node2(leaf(), leaf())));
        let node_case = Formula::forall(
            &[
                ("__fld_Node_0", btree_sort()),
                ("__fld_Node_1", btree_sort()),
                ("__ih0", btree_sort()),
                ("__ih1", btree_sort()),
            ],
            Formula::Implies(
                Box::new(Formula::And(vec![
                    Formula::Eq(
                        Box::new(bt_var("__ih0")),
                        Box::new(node2(bt_var("__fld_Node_0"), bt_var("__fld_Node_0"))),
                    ),
                    Formula::Eq(
                        Box::new(bt_var("__ih1")),
                        Box::new(node2(bt_var("__fld_Node_1"), bt_var("__fld_Node_1"))),
                    ),
                ])),
                Box::new(Formula::Eq(
                    Box::new(node2(bt_var("__ih0"), bt_var("__ih1"))),
                    Box::new(node2(
                        node2(bt_var("__fld_Node_0"), bt_var("__fld_Node_1")),
                        node2(bt_var("__fld_Node_0"), bt_var("__fld_Node_1")),
                    )),
                )),
            ),
        );
        let conclusion = Formula::forall(
            &[("t", btree_sort())],
            Formula::Eq(Box::new(bt_var("_0")), Box::new(node2(bt_var("t"), bt_var("t")))),
        );
        vec![
            bt_vc("recursive_datatype_functional_case::Leaf", leaf_case),
            bt_vc("recursive_datatype_functional_case::Node", node_case),
            bt_vc(
                "recursive_datatype_functional_conclusion[induction:btree::BTree;cases=2]",
                conclusion,
            ),
        ]
    }

    #[test]
    fn multi_ih_wrong_postcondition_rejected_by_kernel() {
        let bundle = rebuild_wrong_node_bundle();
        // Non-vacuity: the false bundle is well-formed enough to build every stage.
        let plan = parse_bundle(&bundle).expect("false multi-IH bundle must PARSE");
        let env = plan.build_env().expect("env builds");
        let goal = plan.goal().expect("goal builds");
        let proof = plan.proof().expect("candidate proof term builds");
        assert!(
            !kernel_checks_goal(&env, &proof, &goal),
            "the clean kernel must REJECT the generated proof of the false multi-IH postcondition"
        );
        assert!(
            certify_recursive_datatype_functional(&bundle).is_none(),
            "the false multi-IH postcondition must never mint a certificate"
        );
    }

    // ── GENERAL-N witness: a TERNARY constructor (3 fields, 3 IHs) — confirms
    //    `build_step_minor` is truly general-N (3 congrArgs + 2 Eq.trans), not
    //    hard-wired to N=2. ──────────────────────────────────────────────────

    fn ttree_sort() -> Sort {
        let tt = || Sort::Datatype { name: "ttree::TTree".to_string(), constructors: vec![] };
        Sort::Datatype {
            name: "ttree::TTree".to_string(),
            constructors: vec![
                ("Leaf".to_string(), vec![]),
                (
                    "Node3".to_string(),
                    vec![("0".to_string(), tt()), ("1".to_string(), tt()), ("2".to_string(), tt())],
                ),
            ],
        }
    }
    fn tt_var(name: &str) -> Formula {
        Formula::var_owned(name.to_string(), ttree_sort())
    }
    fn tt_ctor(name: &str, args: Vec<Formula>) -> Formula {
        Formula::Ctor { ctor: name.to_string(), args, sort: ttree_sort() }
    }
    fn tt_vc(property: &str, formula: Formula) -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::FunctionalCorrectness {
                property: property.to_string(),
                context: "rebuild3".to_string(),
            },
            function: "rebuild3".into(),
            location: SourceSpan::default(),
            formula,
            contract_metadata: None,
        }
    }

    /// Emitted bundle for `rebuild3 t = t` over a TERNARY `Node3` (3 IHs).
    fn rebuild3_identity_bundle() -> Vec<VerificationCondition> {
        let leaf_case =
            Formula::Eq(Box::new(tt_ctor("Leaf", vec![])), Box::new(tt_ctor("Leaf", vec![])));
        let node_case = Formula::forall(
            &[
                ("__fld_Node3_0", ttree_sort()),
                ("__fld_Node3_1", ttree_sort()),
                ("__fld_Node3_2", ttree_sort()),
                ("__ih0", ttree_sort()),
                ("__ih1", ttree_sort()),
                ("__ih2", ttree_sort()),
            ],
            Formula::Implies(
                Box::new(Formula::And(vec![
                    Formula::Eq(Box::new(tt_var("__ih0")), Box::new(tt_var("__fld_Node3_0"))),
                    Formula::Eq(Box::new(tt_var("__ih1")), Box::new(tt_var("__fld_Node3_1"))),
                    Formula::Eq(Box::new(tt_var("__ih2")), Box::new(tt_var("__fld_Node3_2"))),
                ])),
                Box::new(Formula::Eq(
                    Box::new(tt_ctor(
                        "Node3",
                        vec![tt_var("__ih0"), tt_var("__ih1"), tt_var("__ih2")],
                    )),
                    Box::new(tt_ctor(
                        "Node3",
                        vec![
                            tt_var("__fld_Node3_0"),
                            tt_var("__fld_Node3_1"),
                            tt_var("__fld_Node3_2"),
                        ],
                    )),
                )),
            ),
        );
        let conclusion = Formula::forall(
            &[("t", ttree_sort())],
            Formula::Eq(Box::new(tt_var("_0")), Box::new(tt_var("t"))),
        );
        vec![
            tt_vc("recursive_datatype_functional_case::Leaf", leaf_case),
            tt_vc("recursive_datatype_functional_case::Node3", node_case),
            tt_vc(
                "recursive_datatype_functional_conclusion[induction:ttree::TTree;cases=2]",
                conclusion,
            ),
        ]
    }

    /// GENERAL-N (N=3): the auto-generator emits a `TTree.rec` term whose ternary
    /// `Node3` minor consumes ALL THREE IHs (3 congrArgs folded by 2 Eq.trans) and
    /// the kernel accepts it — confirming `build_step_minor` generalizes beyond N=2.
    #[test]
    fn certify_rebuild3_identity_ternary_bundle() {
        let bundle = rebuild3_identity_bundle();
        certify_recursive_datatype_functional(&bundle).expect(
            "the ternary (N=3) rebuild-identity bundle must certify to a kernel-checked CleanCic",
        );
        assert!(
            induction_is_load_bearing(&bundle),
            "ternary multi-IH induction must be load-bearing"
        );
    }

    // ── PAYLOAD fields: `Tagged = Nil | Cons (tag : Bit) (rest : Tagged)` — a
    //    non-recursive Bit payload beside a recursive field (the `param(Name)` /
    //    `Cons(head, tail)` shape). The model passes the payload through. ────────

    fn bit_sort() -> Sort {
        Sort::Datatype {
            name: "bit::Bit".to_string(),
            constructors: vec![("B0".to_string(), vec![]), ("B1".to_string(), vec![])],
        }
    }
    fn tagged_sort() -> Sort {
        let tg = || Sort::Datatype { name: "tagged::Tagged".to_string(), constructors: vec![] };
        Sort::Datatype {
            name: "tagged::Tagged".to_string(),
            constructors: vec![
                ("Nil".to_string(), vec![]),
                ("Cons".to_string(), vec![("0".to_string(), bit_sort()), ("1".to_string(), tg())]),
            ],
        }
    }
    fn tg_v(name: &str, sort: Sort) -> Formula {
        Formula::var_owned(name.to_string(), sort)
    }
    fn tg_ctor(name: &str, args: Vec<Formula>) -> Formula {
        Formula::Ctor { ctor: name.to_string(), args, sort: tagged_sort() }
    }
    fn tg_vc(property: &str, formula: Formula) -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::FunctionalCorrectness {
                property: property.to_string(),
                context: "retag".to_string(),
            },
            function: "retag".into(),
            location: SourceSpan::default(),
            formula,
            contract_metadata: None,
        }
    }

    /// Emitted bundle for `retag t = t` where `Cons` carries a Bit PAYLOAD (passed
    /// through) and a recursive `rest` field (one IH).
    fn retag_identity_bundle() -> Vec<VerificationCondition> {
        let nil_case =
            Formula::Eq(Box::new(tg_ctor("Nil", vec![])), Box::new(tg_ctor("Nil", vec![])));
        let cons_case = Formula::forall(
            &[
                ("__fld_Cons_0", bit_sort()),
                ("__fld_Cons_1", tagged_sort()),
                ("__ih0", tagged_sort()),
            ],
            Formula::Implies(
                Box::new(Formula::Eq(
                    Box::new(tg_v("__ih0", tagged_sort())),
                    Box::new(tg_v("__fld_Cons_1", tagged_sort())),
                )),
                Box::new(Formula::Eq(
                    Box::new(tg_ctor(
                        "Cons",
                        vec![tg_v("__fld_Cons_0", bit_sort()), tg_v("__ih0", tagged_sort())],
                    )),
                    Box::new(tg_ctor(
                        "Cons",
                        vec![tg_v("__fld_Cons_0", bit_sort()), tg_v("__fld_Cons_1", tagged_sort())],
                    )),
                )),
            ),
        );
        let conclusion = Formula::forall(
            &[("t", tagged_sort())],
            Formula::Eq(Box::new(tg_v("_0", tagged_sort())), Box::new(tg_v("t", tagged_sort()))),
        );
        vec![
            tg_vc("recursive_datatype_functional_case::Nil", nil_case),
            tg_vc("recursive_datatype_functional_case::Cons", cons_case),
            tg_vc(
                "recursive_datatype_functional_conclusion[induction:tagged::Tagged;cases=2]",
                conclusion,
            ),
        ]
    }

    /// PAYLOAD MILESTONE: the auto-generator reconstructs the `Bit` payload
    /// datatype and a `Cons(tag : Bit, rest : Tagged)` constructor, builds the
    /// model that passes the tag through and rebuilds `rest`, and the kernel
    /// accepts the induction proof whose `Cons` minor consumes the single `rest`
    /// IH while holding the payload fixed.
    #[test]
    fn certify_retag_identity_payload_bundle() {
        let bundle = retag_identity_bundle();
        certify_recursive_datatype_functional(&bundle)
            .expect("the payload-carrying (Bit + recursive) rebuild-identity bundle must certify");
        assert!(induction_is_load_bearing(&bundle), "payload-field induction must be load-bearing");
    }

    // ── Expr-SHAPED datatype: `E = Lit (v : Bit) | App (f : E) (a : E)` — one
    //    PAYLOAD constructor AND one MULTI-recursive constructor in the same
    //    datatype (the kernel `Expr`'s Var/App shape). ─────────────────────────

    fn e_sort() -> Sort {
        let e = || Sort::Datatype { name: "expr::E".to_string(), constructors: vec![] };
        Sort::Datatype {
            name: "expr::E".to_string(),
            constructors: vec![
                ("Lit".to_string(), vec![("0".to_string(), bit_sort())]),
                ("App".to_string(), vec![("0".to_string(), e()), ("1".to_string(), e())]),
            ],
        }
    }
    fn e_v(name: &str, sort: Sort) -> Formula {
        Formula::var_owned(name.to_string(), sort)
    }
    fn e_ctor(name: &str, args: Vec<Formula>) -> Formula {
        Formula::Ctor { ctor: name.to_string(), args, sort: e_sort() }
    }
    fn e_vc(property: &str, formula: Formula) -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::FunctionalCorrectness {
                property: property.to_string(),
                context: "erebuild".to_string(),
            },
            function: "erebuild".into(),
            location: SourceSpan::default(),
            formula,
            contract_metadata: None,
        }
    }

    /// `erebuild e = e` over `E = Lit(v:Bit) | App(f:E)(a:E)`: a payload `Lit`
    /// constructor and a two-recursive-field `App` constructor in one datatype.
    fn erebuild_identity_bundle() -> Vec<VerificationCondition> {
        let lit_case = Formula::forall(
            &[("__fld_Lit_0", bit_sort())],
            // no IHs: Lit carries only a payload.
            Formula::Eq(
                Box::new(e_ctor("Lit", vec![e_v("__fld_Lit_0", bit_sort())])),
                Box::new(e_ctor("Lit", vec![e_v("__fld_Lit_0", bit_sort())])),
            ),
        );
        let app_case = Formula::forall(
            &[
                ("__fld_App_0", e_sort()),
                ("__fld_App_1", e_sort()),
                ("__ih0", e_sort()),
                ("__ih1", e_sort()),
            ],
            Formula::Implies(
                Box::new(Formula::And(vec![
                    Formula::Eq(
                        Box::new(e_v("__ih0", e_sort())),
                        Box::new(e_v("__fld_App_0", e_sort())),
                    ),
                    Formula::Eq(
                        Box::new(e_v("__ih1", e_sort())),
                        Box::new(e_v("__fld_App_1", e_sort())),
                    ),
                ])),
                Box::new(Formula::Eq(
                    Box::new(e_ctor("App", vec![e_v("__ih0", e_sort()), e_v("__ih1", e_sort())])),
                    Box::new(e_ctor(
                        "App",
                        vec![e_v("__fld_App_0", e_sort()), e_v("__fld_App_1", e_sort())],
                    )),
                )),
            ),
        );
        let conclusion = Formula::forall(
            &[("e", e_sort())],
            Formula::Eq(Box::new(e_v("_0", e_sort())), Box::new(e_v("e", e_sort()))),
        );
        vec![
            e_vc("recursive_datatype_functional_case::Lit", lit_case),
            e_vc("recursive_datatype_functional_case::App", app_case),
            e_vc("recursive_datatype_functional_conclusion[induction:expr::E;cases=2]", conclusion),
        ]
    }

    /// EXPR-SHAPE MILESTONE: a datatype mixing a payload constructor (`Lit`) and a
    /// multi-recursive constructor (`App`) — the kernel `Expr`'s Var/App shape —
    /// auto-generates an `E.rec` proof the clean kernel accepts (Lit minor by
    /// refl, App minor consuming both IHs), load-bearing.
    #[test]
    fn certify_erebuild_identity_expr_shaped_bundle() {
        let bundle = erebuild_identity_bundle();
        certify_recursive_datatype_functional(&bundle).expect(
            "the Expr-shaped (payload Lit + binary App) rebuild-identity bundle must certify",
        );
        assert!(induction_is_load_bearing(&bundle), "Expr-shaped induction must be load-bearing");
    }

    // ── NON-NULLARY PAYLOAD: `NatList = NNil | NCons (head : Nat) (tail : NatList)`
    //    with `Nat = Z | S (Nat)` — the payload is a SELF-RECURSIVE inductive
    //    (the shape real `Expr` payloads `Level`/`Name` carry), reconstructed and
    //    registered before the modeled datatype, held fixed by the model. ────────

    fn nat_sort() -> Sort {
        let nat_ref = || Sort::Datatype { name: "nat::Nat".to_string(), constructors: vec![] };
        Sort::Datatype {
            name: "nat::Nat".to_string(),
            constructors: vec![
                ("Z".to_string(), vec![]),
                ("S".to_string(), vec![("0".to_string(), nat_ref())]),
            ],
        }
    }
    fn natlist_sort() -> Sort {
        let nl = || Sort::Datatype { name: "natlist::NatList".to_string(), constructors: vec![] };
        Sort::Datatype {
            name: "natlist::NatList".to_string(),
            constructors: vec![
                ("NNil".to_string(), vec![]),
                ("NCons".to_string(), vec![("0".to_string(), nat_sort()), ("1".to_string(), nl())]),
            ],
        }
    }
    fn nl_v(name: &str, sort: Sort) -> Formula {
        Formula::var_owned(name.to_string(), sort)
    }
    fn nl_ctor(name: &str, args: Vec<Formula>) -> Formula {
        Formula::Ctor { ctor: name.to_string(), args, sort: natlist_sort() }
    }
    fn nl_vc(property: &str, formula: Formula) -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::FunctionalCorrectness {
                property: property.to_string(),
                context: "nrebuild".to_string(),
            },
            function: "nrebuild".into(),
            location: SourceSpan::default(),
            formula,
            contract_metadata: None,
        }
    }

    /// Emitted bundle for `nrebuild t = t` where `NCons` carries a self-recursive
    /// `Nat` PAYLOAD (passed through) beside the recursive `tail` (one IH).
    fn nrebuild_identity_bundle() -> Vec<VerificationCondition> {
        let nil_case =
            Formula::Eq(Box::new(nl_ctor("NNil", vec![])), Box::new(nl_ctor("NNil", vec![])));
        let cons_case = Formula::forall(
            &[
                ("__fld_NCons_0", nat_sort()),
                ("__fld_NCons_1", natlist_sort()),
                ("__ih0", natlist_sort()),
            ],
            Formula::Implies(
                Box::new(Formula::Eq(
                    Box::new(nl_v("__ih0", natlist_sort())),
                    Box::new(nl_v("__fld_NCons_1", natlist_sort())),
                )),
                Box::new(Formula::Eq(
                    Box::new(nl_ctor(
                        "NCons",
                        vec![nl_v("__fld_NCons_0", nat_sort()), nl_v("__ih0", natlist_sort())],
                    )),
                    Box::new(nl_ctor(
                        "NCons",
                        vec![
                            nl_v("__fld_NCons_0", nat_sort()),
                            nl_v("__fld_NCons_1", natlist_sort()),
                        ],
                    )),
                )),
            ),
        );
        let conclusion = Formula::forall(
            &[("t", natlist_sort())],
            Formula::Eq(Box::new(nl_v("_0", natlist_sort())), Box::new(nl_v("t", natlist_sort()))),
        );
        vec![
            nl_vc("recursive_datatype_functional_case::NNil", nil_case),
            nl_vc("recursive_datatype_functional_case::NCons", cons_case),
            nl_vc(
                "recursive_datatype_functional_conclusion[induction:natlist::NatList;cases=2]",
                conclusion,
            ),
        ]
    }

    /// NON-NULLARY-PAYLOAD MILESTONE: the auto-generator reconstructs the
    /// self-recursive `Nat = Z | S (Nat)` payload datatype (registered ahead of
    /// `NatList`), builds `NCons : Nat -> NatList -> NatList`, and the clean kernel
    /// accepts the induction proof whose `NCons` minor holds the `Nat` payload
    /// fixed while consuming the `tail` IH — the payload's own inductive structure
    /// is irrelevant to the proof, only that its type reconstructs faithfully.
    #[test]
    fn certify_nrebuild_identity_nonnullary_payload_bundle() {
        let bundle = nrebuild_identity_bundle();
        certify_recursive_datatype_functional(&bundle)
            .expect("the non-nullary (self-recursive Nat) payload bundle must certify");
        assert!(
            induction_is_load_bearing(&bundle),
            "non-nullary-payload induction must be load-bearing"
        );
    }

    // ── INTERLEAVED payload/recursive: `Tree = Tip (tag:Bit) | Fork (l:Tree)
    //    (mid:Bit) (r:Tree)` — a payload SANDWICHED between two recursive fields,
    //    the real kernel `Lam(BinderInfo, Expr, Expr)` / `Let(Name, ..)` shape
    //    where the payload is NOT at the edge. Exercises `arg_at`/`recursive_
    //    position` on non-adjacent recursive slots (ih0 for `l`, ih1 for `r`,
    //    the `mid` payload held fixed BETWEEN them). ─────────────────────────────

    fn tree_sort() -> Sort {
        let tr = || Sort::Datatype { name: "tree::Tree".to_string(), constructors: vec![] };
        Sort::Datatype {
            name: "tree::Tree".to_string(),
            constructors: vec![
                ("Tip".to_string(), vec![("0".to_string(), bit_sort())]),
                (
                    "Fork".to_string(),
                    vec![
                        ("0".to_string(), tr()),
                        ("1".to_string(), bit_sort()),
                        ("2".to_string(), tr()),
                    ],
                ),
            ],
        }
    }
    fn tr_v(name: &str, sort: Sort) -> Formula {
        Formula::var_owned(name.to_string(), sort)
    }
    fn tr_ctor(name: &str, args: Vec<Formula>) -> Formula {
        Formula::Ctor { ctor: name.to_string(), args, sort: tree_sort() }
    }
    fn tr_vc(property: &str, formula: Formula) -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::FunctionalCorrectness {
                property: property.to_string(),
                context: "trebuild".to_string(),
            },
            function: "trebuild".into(),
            location: SourceSpan::default(),
            formula,
            contract_metadata: None,
        }
    }

    /// `trebuild t = t` over `Fork(l:Tree, mid:Bit, r:Tree)` — the payload `mid`
    /// sits BETWEEN the two recursive fields; both IHs consumed, `mid` held fixed.
    fn trebuild_identity_bundle() -> Vec<VerificationCondition> {
        let tip_case = Formula::forall(
            &[("__fld_Tip_0", bit_sort())],
            Formula::Eq(
                Box::new(tr_ctor("Tip", vec![tr_v("__fld_Tip_0", bit_sort())])),
                Box::new(tr_ctor("Tip", vec![tr_v("__fld_Tip_0", bit_sort())])),
            ),
        );
        let fork_case = Formula::forall(
            &[
                ("__fld_Fork_0", tree_sort()),
                ("__fld_Fork_1", bit_sort()),
                ("__fld_Fork_2", tree_sort()),
                ("__ih0", tree_sort()),
                ("__ih1", tree_sort()),
            ],
            Formula::Implies(
                Box::new(Formula::And(vec![
                    Formula::Eq(
                        Box::new(tr_v("__ih0", tree_sort())),
                        Box::new(tr_v("__fld_Fork_0", tree_sort())),
                    ),
                    Formula::Eq(
                        Box::new(tr_v("__ih1", tree_sort())),
                        Box::new(tr_v("__fld_Fork_2", tree_sort())),
                    ),
                ])),
                Box::new(Formula::Eq(
                    Box::new(tr_ctor(
                        "Fork",
                        vec![
                            tr_v("__ih0", tree_sort()),
                            tr_v("__fld_Fork_1", bit_sort()),
                            tr_v("__ih1", tree_sort()),
                        ],
                    )),
                    Box::new(tr_ctor(
                        "Fork",
                        vec![
                            tr_v("__fld_Fork_0", tree_sort()),
                            tr_v("__fld_Fork_1", bit_sort()),
                            tr_v("__fld_Fork_2", tree_sort()),
                        ],
                    )),
                )),
            ),
        );
        let conclusion = Formula::forall(
            &[("t", tree_sort())],
            Formula::Eq(Box::new(tr_v("_0", tree_sort())), Box::new(tr_v("t", tree_sort()))),
        );
        vec![
            tr_vc("recursive_datatype_functional_case::Tip", tip_case),
            tr_vc("recursive_datatype_functional_case::Fork", fork_case),
            tr_vc(
                "recursive_datatype_functional_conclusion[induction:tree::Tree;cases=2]",
                conclusion,
            ),
        ]
    }

    /// INTERLEAVED-PAYLOAD MILESTONE: the payload `mid` sits between the two
    /// recursive fields of `Fork` (the real `Lam(BinderInfo, Expr, Expr)` shape).
    /// The auto-generator rewrites the two non-adjacent recursive slots via their
    /// IHs while holding the interior payload fixed, and the kernel accepts it.
    #[test]
    fn certify_trebuild_identity_interleaved_payload_bundle() {
        let bundle = trebuild_identity_bundle();
        certify_recursive_datatype_functional(&bundle)
            .expect("the interleaved payload/recursive (Fork) bundle must certify");
        assert!(
            induction_is_load_bearing(&bundle),
            "interleaved-payload induction must be load-bearing"
        );
    }

    // ── SCALAR payload: `KFrag = KVar (n : u32) | KProj (child : KFrag)` — a
    //    NON-datatype scalar field (`u32` lowers to `Sort::BitVec(32)`), the real
    //    `ExprKind::BVar(u32)` shape. The scalar is modeled by an opaque `Type`
    //    and held fixed by the identity proof. ─────────────────────────────────

    fn kfrag_sort() -> Sort {
        let kf = || Sort::Datatype { name: "kfrag::KFrag".to_string(), constructors: vec![] };
        Sort::Datatype {
            name: "kfrag::KFrag".to_string(),
            constructors: vec![
                ("KVar".to_string(), vec![("0".to_string(), Sort::BitVec(32))]),
                ("KProj".to_string(), vec![("0".to_string(), kf())]),
            ],
        }
    }
    fn kf_v(name: &str, sort: Sort) -> Formula {
        Formula::var_owned(name.to_string(), sort)
    }
    fn kf_ctor(name: &str, args: Vec<Formula>) -> Formula {
        Formula::Ctor { ctor: name.to_string(), args, sort: kfrag_sort() }
    }
    fn kf_vc(property: &str, formula: Formula) -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::FunctionalCorrectness {
                property: property.to_string(),
                context: "krebuild".to_string(),
            },
            function: "krebuild".into(),
            location: SourceSpan::default(),
            formula,
            contract_metadata: None,
        }
    }

    /// Emitted bundle for `krebuild k = k` where `KVar` carries a SCALAR `u32`
    /// (`Sort::BitVec(32)`) PAYLOAD (held fixed) and `KProj` is recursive (one IH).
    fn krebuild_identity_bundle() -> Vec<VerificationCondition> {
        let kvar_case = Formula::forall(
            &[("__fld_KVar_0", Sort::BitVec(32))],
            // no IH: KVar carries only a non-datatype scalar payload.
            Formula::Eq(
                Box::new(kf_ctor("KVar", vec![kf_v("__fld_KVar_0", Sort::BitVec(32))])),
                Box::new(kf_ctor("KVar", vec![kf_v("__fld_KVar_0", Sort::BitVec(32))])),
            ),
        );
        let kproj_case = Formula::forall(
            &[("__fld_KProj_0", kfrag_sort()), ("__ih0", kfrag_sort())],
            Formula::Implies(
                Box::new(Formula::Eq(
                    Box::new(kf_v("__ih0", kfrag_sort())),
                    Box::new(kf_v("__fld_KProj_0", kfrag_sort())),
                )),
                Box::new(Formula::Eq(
                    Box::new(kf_ctor("KProj", vec![kf_v("__ih0", kfrag_sort())])),
                    Box::new(kf_ctor("KProj", vec![kf_v("__fld_KProj_0", kfrag_sort())])),
                )),
            ),
        );
        let conclusion = Formula::forall(
            &[("k", kfrag_sort())],
            Formula::Eq(Box::new(kf_v("_0", kfrag_sort())), Box::new(kf_v("k", kfrag_sort()))),
        );
        vec![
            kf_vc("recursive_datatype_functional_case::KVar", kvar_case),
            kf_vc("recursive_datatype_functional_case::KProj", kproj_case),
            kf_vc(
                "recursive_datatype_functional_conclusion[induction:kfrag::KFrag;cases=2]",
                conclusion,
            ),
        ]
    }

    /// SCALAR-PAYLOAD MILESTONE: `KVar` carries a NON-datatype `u32`
    /// (`Sort::BitVec(32)`) — the exact `ExprKind::BVar(u32)` shape that previously
    /// FAILED CLOSED (certify's `.rec` lane rejected non-datatype fields). The
    /// scalar is now modeled by a fresh opaque `Type` and held fixed by the
    /// identity proof; the kernel accepts the `KFrag.rec` induction term (KVar
    /// minor by refl holding the scalar, KProj minor consuming its IH),
    /// load-bearing. This is the discharge capability that unblocks a for-all over
    /// the real `Expr` constructor shape.
    #[test]
    fn certify_krebuild_identity_scalar_payload_bundle() {
        let bundle = krebuild_identity_bundle();
        certify_recursive_datatype_functional(&bundle)
            .expect("the scalar-payload (u32/BitVec32 KVar) rebuild-identity bundle must certify");
        assert!(
            induction_is_load_bearing(&bundle),
            "scalar-payload induction must be load-bearing"
        );
    }

    // ── REAL-EXPR-SHAPED CAPSTONE: `EK = EKBVar(n : u32) | EKSort(l : Level)
    //    | EKApp(f : EK)(a : EK)` — the real kernel `Expr` constructor shape,
    //    combining a SCALAR payload (BVar's u32), a non-nullary DATATYPE payload
    //    (Sort's Level = LZero | LSucc(Level)), and a MULTI-recursive constructor
    //    (App, two IHs) in ONE datatype. ─────────────────────────────────────────

    fn level_dt_sort() -> Sort {
        let lref = || Sort::Datatype { name: "lvl::Level".to_string(), constructors: vec![] };
        Sort::Datatype {
            name: "lvl::Level".to_string(),
            constructors: vec![
                ("LZero".to_string(), vec![]),
                ("LSucc".to_string(), vec![("0".to_string(), lref())]),
            ],
        }
    }
    fn ek_sort() -> Sort {
        let ek = || Sort::Datatype { name: "ek::EK".to_string(), constructors: vec![] };
        Sort::Datatype {
            name: "ek::EK".to_string(),
            constructors: vec![
                ("EKBVar".to_string(), vec![("0".to_string(), Sort::BitVec(32))]),
                ("EKSort".to_string(), vec![("0".to_string(), level_dt_sort())]),
                ("EKApp".to_string(), vec![("0".to_string(), ek()), ("1".to_string(), ek())]),
            ],
        }
    }
    fn ek_v(name: &str, sort: Sort) -> Formula {
        Formula::var_owned(name.to_string(), sort)
    }
    fn ek_ctor(name: &str, args: Vec<Formula>) -> Formula {
        Formula::Ctor { ctor: name.to_string(), args, sort: ek_sort() }
    }
    fn ek_vc(property: &str, formula: Formula) -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::FunctionalCorrectness {
                property: property.to_string(),
                context: "ekrebuild".to_string(),
            },
            function: "ekrebuild".into(),
            location: SourceSpan::default(),
            formula,
            contract_metadata: None,
        }
    }

    /// Emitted bundle for `ekrebuild ek = ek` over the real-`Expr`-shaped
    /// `EK = EKBVar(u32) | EKSort(Level) | EKApp(EK, EK)`.
    fn ekrebuild_identity_bundle() -> Vec<VerificationCondition> {
        // EKBVar: scalar u32 payload, held fixed, no IH.
        let bvar_case = Formula::forall(
            &[("__fld_EKBVar_0", Sort::BitVec(32))],
            Formula::Eq(
                Box::new(ek_ctor("EKBVar", vec![ek_v("__fld_EKBVar_0", Sort::BitVec(32))])),
                Box::new(ek_ctor("EKBVar", vec![ek_v("__fld_EKBVar_0", Sort::BitVec(32))])),
            ),
        );
        // EKSort: Level DATATYPE payload, held fixed, no IH.
        let sort_case = Formula::forall(
            &[("__fld_EKSort_0", level_dt_sort())],
            Formula::Eq(
                Box::new(ek_ctor("EKSort", vec![ek_v("__fld_EKSort_0", level_dt_sort())])),
                Box::new(ek_ctor("EKSort", vec![ek_v("__fld_EKSort_0", level_dt_sort())])),
            ),
        );
        // EKApp: two recursive fields, two IHs.
        let app_case = Formula::forall(
            &[
                ("__fld_EKApp_0", ek_sort()),
                ("__fld_EKApp_1", ek_sort()),
                ("__ih0", ek_sort()),
                ("__ih1", ek_sort()),
            ],
            Formula::Implies(
                Box::new(Formula::And(vec![
                    Formula::Eq(
                        Box::new(ek_v("__ih0", ek_sort())),
                        Box::new(ek_v("__fld_EKApp_0", ek_sort())),
                    ),
                    Formula::Eq(
                        Box::new(ek_v("__ih1", ek_sort())),
                        Box::new(ek_v("__fld_EKApp_1", ek_sort())),
                    ),
                ])),
                Box::new(Formula::Eq(
                    Box::new(ek_ctor(
                        "EKApp",
                        vec![ek_v("__ih0", ek_sort()), ek_v("__ih1", ek_sort())],
                    )),
                    Box::new(ek_ctor(
                        "EKApp",
                        vec![ek_v("__fld_EKApp_0", ek_sort()), ek_v("__fld_EKApp_1", ek_sort())],
                    )),
                )),
            ),
        );
        let conclusion = Formula::forall(
            &[("ek", ek_sort())],
            Formula::Eq(Box::new(ek_v("_0", ek_sort())), Box::new(ek_v("ek", ek_sort()))),
        );
        vec![
            ek_vc("recursive_datatype_functional_case::EKBVar", bvar_case),
            ek_vc("recursive_datatype_functional_case::EKSort", sort_case),
            ek_vc("recursive_datatype_functional_case::EKApp", app_case),
            ek_vc("recursive_datatype_functional_conclusion[induction:ek::EK;cases=3]", conclusion),
        ]
    }

    /// REAL-EXPR-SHAPED CAPSTONE: one datatype with the real kernel `Expr`
    /// constructor shape — a SCALAR payload (`EKBVar(u32)`), a non-nullary DATATYPE
    /// payload (`EKSort(Level)`), and a MULTI-recursive constructor (`EKApp`, two
    /// IHs) — discharges the for-all `∀ ek, ekrebuild ek = ek` to a kernel-checked
    /// `EK.rec` induction term (scalar + Level payloads held fixed, App consuming
    /// both IHs), load-bearing. This exercises every payload/recursion kind the real
    /// `Expr` carries, together, now that scalar payloads discharge.
    #[test]
    fn certify_ekrebuild_identity_real_expr_shaped_bundle() {
        let bundle = ekrebuild_identity_bundle();
        certify_recursive_datatype_functional(&bundle).expect(
            "the real-Expr-shaped (scalar u32 + Level datatype payload + binary App) \
             bundle must certify",
        );
        assert!(
            induction_is_load_bearing(&bundle),
            "real-Expr-shaped induction must be load-bearing"
        );
    }

    // ── NESTED scalar payload: a PAYLOAD DATATYPE with a scalar field —
    //    `NL = NLLeaf(n : NameLike) | NLNode(child : NL)` where
    //    `NameLike = Anon | Num(u32)` (Num carries a NESTED scalar). ─────────────

    fn namelike_sort() -> Sort {
        Sort::Datatype {
            name: "nm::NameLike".to_string(),
            constructors: vec![
                ("Anon".to_string(), vec![]),
                ("Num".to_string(), vec![("0".to_string(), Sort::BitVec(32))]), // NESTED scalar
            ],
        }
    }
    fn nsl_sort() -> Sort {
        let nl = || Sort::Datatype { name: "nl::NL".to_string(), constructors: vec![] };
        Sort::Datatype {
            name: "nl::NL".to_string(),
            constructors: vec![
                ("NLLeaf".to_string(), vec![("0".to_string(), namelike_sort())]),
                ("NLNode".to_string(), vec![("0".to_string(), nl())]),
            ],
        }
    }
    fn nsl_v(name: &str, sort: Sort) -> Formula {
        Formula::var_owned(name.to_string(), sort)
    }
    fn nsl_ctor(name: &str, args: Vec<Formula>) -> Formula {
        Formula::Ctor { ctor: name.to_string(), args, sort: nsl_sort() }
    }
    fn nsl_vc(property: &str, formula: Formula) -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::FunctionalCorrectness {
                property: property.to_string(),
                context: "nlrebuild".to_string(),
            },
            function: "nlrebuild".into(),
            location: SourceSpan::default(),
            formula,
            contract_metadata: None,
        }
    }

    /// `nlrebuild nl = nl` where `NLLeaf` carries a `NameLike` PAYLOAD DATATYPE
    /// whose `Num` constructor holds a NESTED `u32` scalar (held fixed), and
    /// `NLNode` is recursive.
    fn nlrebuild_identity_bundle() -> Vec<VerificationCondition> {
        let leaf_case = Formula::forall(
            &[("__fld_NLLeaf_0", namelike_sort())],
            Formula::Eq(
                Box::new(nsl_ctor("NLLeaf", vec![nsl_v("__fld_NLLeaf_0", namelike_sort())])),
                Box::new(nsl_ctor("NLLeaf", vec![nsl_v("__fld_NLLeaf_0", namelike_sort())])),
            ),
        );
        let node_case = Formula::forall(
            &[("__fld_NLNode_0", nsl_sort()), ("__ih0", nsl_sort())],
            Formula::Implies(
                Box::new(Formula::Eq(
                    Box::new(nsl_v("__ih0", nsl_sort())),
                    Box::new(nsl_v("__fld_NLNode_0", nsl_sort())),
                )),
                Box::new(Formula::Eq(
                    Box::new(nsl_ctor("NLNode", vec![nsl_v("__ih0", nsl_sort())])),
                    Box::new(nsl_ctor("NLNode", vec![nsl_v("__fld_NLNode_0", nsl_sort())])),
                )),
            ),
        );
        let conclusion = Formula::forall(
            &[("nl", nsl_sort())],
            Formula::Eq(Box::new(nsl_v("_0", nsl_sort())), Box::new(nsl_v("nl", nsl_sort()))),
        );
        vec![
            nsl_vc("recursive_datatype_functional_case::NLLeaf", leaf_case),
            nsl_vc("recursive_datatype_functional_case::NLNode", node_case),
            nsl_vc(
                "recursive_datatype_functional_conclusion[induction:nl::NL;cases=2]",
                conclusion,
            ),
        ]
    }

    /// NESTED-SCALAR-PAYLOAD MILESTONE: the payload datatype `NameLike = Anon |
    /// Num(u32)` — reconstructed and registered ahead of `NL` — carries a NESTED
    /// scalar `u32` in `Num`. Both the opaque `u32` type AND the `NameLike` payload
    /// are built (scalar registered before the payload that references it), the
    /// `Num : <u32> -> NameLike` constructor type-checks, and the kernel accepts the
    /// `NL.rec` identity proof (the whole `NameLike` payload held fixed),
    /// load-bearing.
    #[test]
    fn certify_nlrebuild_identity_nested_scalar_payload_bundle() {
        let bundle = nlrebuild_identity_bundle();
        certify_recursive_datatype_functional(&bundle)
            .expect("the nested-scalar (NameLike = Anon | Num(u32)) payload bundle must certify");
        assert!(
            induction_is_load_bearing(&bundle),
            "nested-scalar-payload induction must be load-bearing"
        );
    }

    // ── THE MILESTONE: the generated .rec induction term kernel-checks ────────

    #[test]
    fn certify_mirror_identity_bundle() {
        let bundle = mirror_identity_bundle();
        let evidence = certify_recursive_datatype_functional(&bundle)
            .expect("the mirror identity bundle must certify to a kernel-checked CleanCic term");
        let ProofEvidence::CleanCic { term, context, lineage, .. } = evidence else {
            panic!("expected CleanCic evidence");
        };
        assert!(!term.is_empty() && !context.is_empty(), "nonempty CleanCic payload");
        assert_ne!(lineage, trust_ir::ProofDigest::zero(), "lineage must be bound");
        assert!(
            recheck_recursive_datatype_functional(&bundle, &term, &context, &lineage),
            "serialized recursive-functional CleanCic payload must re-check"
        );
    }

    /// The IH is load-bearing: the refl-only pseudo-proof is REJECTED while the
    /// generated induction proof is ACCEPTED (no masquerade).
    #[test]
    fn mirror_identity_requires_induction() {
        assert!(
            induction_is_load_bearing(&mirror_identity_bundle()),
            "the generated .rec proof must check AND the refl-only pseudo-proof must be rejected"
        );
    }

    // ── NEGATIVE control: the WRONG postcondition is kernel-rejected ──────────

    /// The false spec's bundle PARSES and BUILDS (it is not a malformation) —
    /// and the clean KERNEL rejects the generated proof: no certificate.
    #[test]
    fn wrong_postcondition_bundle_rejected_by_kernel() {
        let bundle = mirror_wrong_succ_bundle();
        // Non-vacuity: the wrong bundle is well-formed enough to build a plan,
        // env, goal, and candidate proof term.
        let plan = parse_bundle(&bundle).expect("wrong bundle must PARSE (not a malformation)");
        let env = plan.build_env().expect("env builds");
        let goal = plan.goal().expect("goal builds");
        let proof = plan.proof().expect("candidate proof term builds");
        // The kernel is the gate that rejects it.
        assert!(
            !kernel_checks_goal(&env, &proof, &goal),
            "the clean kernel must REJECT the generated proof of the false postcondition"
        );
        assert!(
            certify_recursive_datatype_functional(&bundle).is_none(),
            "the false postcondition must never mint a certificate"
        );
    }

    // ── fail-closed shape gates ────────────────────────────────────────────────

    #[test]
    fn missing_conclusion_fails_closed() {
        let mut bundle = mirror_identity_bundle();
        bundle.pop();
        assert!(certify_recursive_datatype_functional(&bundle).is_none());
    }

    /// Dropping a case VC breaks the `cases=<n>` coverage marker: a partial
    /// bundle would reconstruct a DIFFERENT (smaller) datatype, over which the
    /// induction could be vacuously easy — it must certify NOTHING.
    #[test]
    fn missing_case_fails_closed() {
        let bundle = mirror_identity_bundle();
        let partial = vec![bundle[0].clone(), bundle[2].clone()];
        assert!(
            certify_recursive_datatype_functional(&partial).is_none(),
            "a bundle whose cases do not match the conclusion's coverage marker must fail closed"
        );
    }

    #[test]
    fn tampered_term_rejected() {
        let bundle = mirror_identity_bundle();
        let evidence = certify_recursive_datatype_functional(&bundle).expect("certify");
        let ProofEvidence::CleanCic { term, context, lineage, .. } = evidence else {
            panic!("expected CleanCic evidence");
        };
        let mut tampered = term.clone();
        tampered[0] ^= 0xff;
        assert!(
            !recheck_recursive_datatype_functional(&bundle, &tampered, &context, &lineage),
            "tampered term must fail the offline kernel re-check"
        );
    }

    /// A public lineage hash cannot authorize an arbitrary proof term.  In the
    /// old ambient environment, polymorphic `@sorry goal` is genuinely well
    /// typed; even with a freshly recomputed lineage it must not pass the
    /// canonical-term rechecker.
    #[test]
    fn relineaged_sorry_term_rejected() {
        let bundle = mirror_identity_bundle();
        let plan = parse_bundle(&bundle).expect("identity bundle parses");
        let env = plan
            .build_env_with_ambient_trust_markers()
            .expect("formerly vulnerable ambient env builds");
        let goal = plan.goal().expect("goal builds");
        let sorry =
            Expr::app(Expr::const_(Name::from_string("sorry"), vec![Level::zero()]), goal.clone());
        assert!(
            kernel_checks_goal(&env, &sorry, &goal),
            "non-vacuity: the ambient kernel accepts polymorphic @sorry goal"
        );
        let forged_term = serialize_term(&sorry).expect("serialize forged sorry term");
        let context = canonical_empty_context_bytes().expect("canonical empty context");
        let lineage =
            recursive_functional_lineage_digest(&bundle, &forged_term, &context, &plan.label)
                .expect("lineage");
        assert!(
            !recheck_recursive_datatype_functional(&bundle, &forged_term, &context, &lineage),
            "well-typed @sorry with recomputed lineage must fail closed"
        );
    }

    /// The minimal recheck environment contains no trust markers, but the
    /// canonical-term gate is independently load-bearing too: a beta-redex
    /// around the generated proof is a different, kernel-valid proof of the
    /// same goal and must not be accepted as this lane's canonical evidence,
    /// even with a recomputed public lineage digest.
    #[test]
    fn relineaged_valid_noncanonical_term_rejected() {
        let bundle = mirror_identity_bundle();
        let plan = parse_bundle(&bundle).expect("identity bundle parses");
        let env = plan.build_env().expect("minimal env builds");
        let goal = plan.goal().expect("goal builds");
        let canonical_proof = plan.proof().expect("canonical proof builds");
        let alternate_proof = Expr::app(
            Expr::lam(BinderInfo::Default, goal.clone(), Expr::bvar(0)),
            canonical_proof.clone(),
        );
        assert!(
            kernel_checks_goal(&env, &alternate_proof, &goal),
            "non-vacuity: the minimal kernel accepts the beta-wrapped proof"
        );
        let canonical_term = serialize_term(&canonical_proof).expect("serialize canonical proof");
        let alternate_term = serialize_term(&alternate_proof).expect("serialize alternate proof");
        assert_ne!(
            alternate_term, canonical_term,
            "the alternate proof must have a distinct serialized representation"
        );
        let context = canonical_empty_context_bytes().expect("canonical empty context");
        let lineage =
            recursive_functional_lineage_digest(&bundle, &alternate_term, &context, &plan.label)
                .expect("lineage");
        assert!(
            !recheck_recursive_datatype_functional(&bundle, &alternate_term, &context, &lineage),
            "a valid but non-canonical proof with recomputed lineage must fail closed"
        );
    }

    #[test]
    fn relineaged_noncanonical_context_rejected() {
        let bundle = mirror_identity_bundle();
        let evidence = certify_recursive_datatype_functional(&bundle).expect("certify");
        let ProofEvidence::CleanCic { term, mut context, .. } = evidence else {
            panic!("expected CleanCic evidence");
        };
        context.push(0);
        let plan = parse_bundle(&bundle).expect("identity bundle parses");
        let lineage = recursive_functional_lineage_digest(&bundle, &term, &context, &plan.label)
            .expect("lineage");
        assert!(
            !recheck_recursive_datatype_functional(&bundle, &term, &context, &lineage),
            "re-lineaged non-canonical context must fail closed"
        );
    }

    #[test]
    fn lineage_binds_entire_vc_bundle_not_only_property_tags() {
        let bundle = mirror_identity_bundle();
        let evidence = certify_recursive_datatype_functional(&bundle).expect("certify");
        let ProofEvidence::CleanCic { term, context, lineage, .. } = evidence else {
            panic!("expected CleanCic evidence");
        };
        let mut different_obligation = bundle.clone();
        different_obligation[0].location.file = "different_source.rs".to_string();
        let original_plan = parse_bundle(&bundle).expect("original bundle parses");
        let different_plan = parse_bundle(&different_obligation)
            .expect("changing an otherwise-ignored source span must preserve bundle shape");
        assert_eq!(
            serialize_term(&original_plan.proof().expect("original proof")).expect("serialize"),
            serialize_term(&different_plan.proof().expect("different proof")).expect("serialize"),
            "the proof term must be unchanged so this control specifically exercises VC binding"
        );
        assert!(
            !recheck_recursive_datatype_functional(
                &different_obligation,
                &term,
                &context,
                &lineage,
            ),
            "certificate lineage must bind every serialized VC field"
        );
    }

    #[test]
    fn swapped_lineage_rejected() {
        let bundle = mirror_identity_bundle();
        let evidence = certify_recursive_datatype_functional(&bundle).expect("certify");
        let ProofEvidence::CleanCic { term, context, .. } = evidence else {
            panic!("expected CleanCic evidence");
        };
        assert!(
            !recheck_recursive_datatype_functional(
                &bundle,
                &term,
                &context,
                &trust_ir::ProofDigest::zero()
            ),
            "a zeroed lineage must fail closed"
        );
    }
}
