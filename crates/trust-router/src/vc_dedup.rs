// Structural deduplication of verification conditions before sequential
// dispatch.
//
// Many safety VCs emitted for a single function (or across functions) are
// structurally identical up to bound-variable renaming — e.g. dozens of
// `index out of bounds` obligations whose formula is the same alpha-equivalent
// shape. The parallel cache path already coalesces duplicate cache *misses* by
// formula hash (`solver_cache::pending_miss_by_key`); the sequential path
// (`Router::verify_all_with_deadline`) did not, so it re-solved each duplicate
// 1:1.
//
// This module provides the alpha-equivalence machinery (ported here so
// `trust-router` need not depend on the downstream `trust-vcgen` crate, which
// already depends on `trust-router`) plus `dedup_groups`, which collapses a VC
// batch into representative groups for one-solve-per-group dispatch and
// shared-verdict fan-out.
//
// SOUNDNESS — this is a performance/caching change that MUST NOT alter any
// verdict:
//
//   * Two VCs are merged ONLY IF they are equivalent obligations up to
//     renaming of *bound* variables. Free variables (program values) must
//     match by name; `normalize_alpha` deliberately leaves them unchanged.
//   * A fingerprint match is treated as a hash *filter* only. Before merging we
//     run an exact equivalence check (`vcs_equivalent`) on the alpha-normalized
//     VCs, so a hash collision can never merge two non-equivalent obligations.
//   * VCs are never merged across different routing requirements: the caller
//     supplies a per-VC *plan signature* (the ordered backend selection +
//     `can_handle` flags) and VCs with differing signatures are kept in
//     separate groups even when their formulas coincide.
//   * The fan-out assigns each group's single verdict to exactly the originals
//     in that group, and every input VC appears in exactly one group, so the
//     per-VC output contract (one result per input, original order) is
//     preserved by the caller.
//
// When in doubt we keep VCs separate (cache miss / no dedup): correctness over
// hit-rate.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::hash::{Hash, Hasher};

use trust_types::fx::FxHashMap;
use trust_types::{Formula, Sort, VcKind, VerificationCondition};

/// One group of structurally-equivalent VCs that share a single solve.
///
/// `representative` is the index (into the original batch) of the VC that is
/// actually dispatched. `members` lists every original index in the group
/// (including the representative), in ascending order, so the shared verdict
/// can be fanned out to each.
#[derive(Debug, Clone)]
pub(crate) struct DedupGroup {
    pub representative: usize,
    pub members: Vec<usize>,
}

/// Collapse a VC batch into representative groups for one-solve-per-group
/// dispatch.
///
/// `plan_signature(i)` returns an opaque, `Eq + Hash` value describing the
/// routing requirements of `vcs[i]` (e.g. the ordered backend plan + per-entry
/// `can_handle` flags). VCs with differing signatures are never merged.
///
/// Guarantees:
///   * Every input index appears in exactly one group's `members`.
///   * `members` within a group are in ascending order; the representative is
///     the first (lowest) index of the group.
///   * Two indices share a group only if their VCs are equivalent up to
///     bound-variable renaming AND their plan signatures are equal.
pub(crate) fn dedup_groups<K, F>(
    vcs: &[VerificationCondition],
    plan_signature: F,
) -> Vec<DedupGroup>
where
    K: Eq + Hash,
    F: Fn(usize) -> K,
{
    // Bucket candidate matches by a cheap composite hash so the exact
    // equivalence check only runs against plausible peers. The bucket key folds
    // the plan-signature hash, the VC-kind description, and the alpha-normalized
    // formula fingerprint together.
    let mut buckets: FxHashMap<u64, Vec<usize>> = FxHashMap::default();
    let mut groups: Vec<DedupGroup> = Vec::new();
    // group_of[i] = index into `groups` for the group VC i was assigned to.
    let mut group_of: Vec<Option<usize>> = vec![None; vcs.len()];

    for i in 0..vcs.len() {
        let sig = plan_signature(i);
        let sig_hash = {
            let mut h = std::hash::DefaultHasher::new();
            sig.hash(&mut h);
            h.finish()
        };
        let bucket_key = bucket_hash(sig_hash, &vcs[i]);

        // Look for an existing representative in this bucket that is exactly
        // equivalent to vcs[i] AND shares the same plan signature.
        let mut merged_into: Option<usize> = None;
        if let Some(bucket) = buckets.get(&bucket_key) {
            for &candidate in bucket.iter() {
                let group_idx = group_of[candidate].expect("bucket member must have a group");
                let rep = groups[group_idx].representative;
                // Same routing requirements?
                if plan_signature(rep) != sig {
                    continue;
                }
                // Same obligation up to bound-variable renaming?
                if vcs_equivalent(&vcs[rep], &vcs[i]) {
                    merged_into = Some(group_idx);
                    break;
                }
            }
        }

        match merged_into {
            Some(group_idx) => {
                groups[group_idx].members.push(i);
                group_of[i] = Some(group_idx);
            }
            None => {
                let group_idx = groups.len();
                groups.push(DedupGroup { representative: i, members: vec![i] });
                group_of[i] = Some(group_idx);
            }
        }
        // Record `i` as a probe target for future matches regardless of
        // whether it started a new group: keeping the bucket populated keeps
        // future lookups cheap. The representative is what equivalence is
        // actually checked against.
        buckets.entry(bucket_key).or_default().push(i);
    }

    groups
}

/// Composite bucket hash: plan-signature hash + VC-kind description + the
/// alpha-normalized formula fingerprint. Two VCs that can possibly be merged
/// always land in the same bucket; the reverse need not hold (collisions are
/// resolved by `vcs_equivalent`).
fn bucket_hash(sig_hash: u64, vc: &VerificationCondition) -> u64 {
    let mut h = std::hash::DefaultHasher::new();
    sig_hash.hash(&mut h);
    vc.kind.description().hash(&mut h);
    let normalized = normalize_alpha(&vc.formula);
    hash_formula(&normalized, &mut h);
    h.finish()
}

/// A VC-kind whose proof obligation is checked against a *state machine /
/// automaton* model that is NOT fully captured by `kind.description()` nor by
/// the VC `formula`. These are the kinds the temporal backend (`ty`) routes:
///
///   * `Temporal { property, machine }` — `description()` is only
///     `"temporal: {property}"` (it DROPS the `machine`), and the machine is
///     not in `formula`. Two `Temporal` VCs with equal property + formula but
///     DIFFERENT machines would otherwise be deemed equivalent, and a machine
///     that VIOLATES the property would inherit a `Proved` verdict from a safe
///     representative — a false proof.
///   * `Deadlock` / `DeadState` / `Liveness` / `Fairness` — same hazard: the
///     property/state/constraint they describe is checked against an automaton
///     model that does not round-trip through the description + formula.
///
/// For these we conservatively REFUSE to dedup (always treat as
/// non-equivalent). Soundness over hit-rate: a redundant solve is always
/// acceptable; sharing a verdict between non-equivalent automata is not.
fn carries_unmodeled_machine(kind: &VcKind) -> bool {
    matches!(
        kind,
        VcKind::Temporal { .. }
            | VcKind::Deadlock
            | VcKind::DeadState { .. }
            | VcKind::Liveness { .. }
            | VcKind::Fairness { .. }
    )
}

/// Exact equivalence of two VCs up to renaming of bound variables.
///
/// Conservative: requires the VC-kind descriptions to match, the contract
/// metadata to be equal, and the alpha-normalized formulas to be structurally
/// equal. Free variables must match by name (they are preserved by
/// `normalize_alpha`), so distinct program values are never conflated. The
/// source `location` is intentionally NOT compared: it does not affect the
/// solver verdict, and merging same-obligation VCs from different spans is the
/// whole point of dedup (the caller fans the verdict back to each original VC,
/// which retains its own span).
///
/// SOUNDNESS — machine-bearing kinds are never deduped. `kind.description()` is
/// a lossy projection: for `VcKind::Temporal { property, machine }` it is only
/// `"temporal: {property}"`, which DROPS the `machine`, and the machine is not
/// in `formula` either. Comparing descriptions + formulas would then let two
/// Temporal VCs with the same property but DIFFERENT state machines be merged,
/// so a machine that violates the property could inherit `Proved` from a safe
/// representative. We bail (return `false`) for every automaton-carrying kind
/// routed to the temporal backend (`Temporal`, `Deadlock`, `DeadState`,
/// `Liveness`, `Fairness`).
fn vcs_equivalent(a: &VerificationCondition, b: &VerificationCondition) -> bool {
    // Never share a verdict between automaton-bearing obligations: their model
    // is not faithfully captured by `description()` + `formula`.
    if carries_unmodeled_machine(&a.kind) || carries_unmodeled_machine(&b.kind) {
        return false;
    }
    if a.kind.description() != b.kind.description() {
        return false;
    }
    if a.contract_metadata != b.contract_metadata {
        return false;
    }
    normalize_alpha(&a.formula) == normalize_alpha(&b.formula)
}

// ---------------------------------------------------------------------------
// Alpha-equivalence normalization
//
// Ported from trust-vcgen::dedup (kept local to avoid a dependency cycle:
// trust-vcgen depends on trust-router). Bound (quantifier) variables are
// renamed to canonical `__alpha_N` names in binding order; free variables are
// left untouched.
// ---------------------------------------------------------------------------

/// Normalize bound variables to canonical names for alpha-equivalence.
fn normalize_alpha(f: &Formula) -> Formula {
    let mut counter = 0usize;
    let mut env: FxHashMap<String, String> = FxHashMap::default();
    // Generated canonical names must never capture a free program variable.
    // Installing free names as identity mappings both preserves them and lets
    // `normalize_quantifier` skip every occupied canonical candidate.
    for name in f.free_variables() {
        env.insert(name.clone(), name);
    }
    normalize_inner(f, &mut env, &mut counter)
}

fn normalize_inner(
    f: &Formula,
    env: &mut FxHashMap<String, String>,
    counter: &mut usize,
) -> Formula {
    match f {
        Formula::Var(name, sort) => {
            let resolved = env.get(name).cloned().unwrap_or_else(|| name.clone());
            Formula::Var(resolved, sort.clone())
        }
        Formula::SymVar(name, sort) => {
            let name = name.as_str();
            let resolved = env.get(name).cloned().unwrap_or_else(|| name.to_string());
            Formula::Var(resolved, sort.clone())
        }
        Formula::Forall(bindings, body) => normalize_quantifier(bindings, body, true, env, counter),
        Formula::Exists(bindings, body) => {
            normalize_quantifier(bindings, body, false, env, counter)
        }
        _ => normalize_structural(f, env, counter),
    }
}

fn normalize_quantifier(
    bindings: &[(trust_types::Symbol, Sort)],
    body: &Formula,
    is_forall: bool,
    env: &mut FxHashMap<String, String>,
    counter: &mut usize,
) -> Formula {
    let mut saved: Vec<(String, Option<String>)> = Vec::new();
    let mut new_bindings = Vec::new();

    for (name, sort) in bindings {
        let canonical = loop {
            let candidate = format!("__alpha_{counter}");
            *counter =
                counter.checked_add(1).expect("VC dedup alpha-normalization counter exhausted");
            if !env.contains_key(&candidate) {
                break candidate;
            }
        };
        let name_str = name.to_string();
        saved.push((name_str.clone(), env.get(&name_str).cloned()));
        env.insert(name_str, canonical.clone());
        new_bindings.push((trust_types::Symbol::intern(&canonical), sort.clone()));
    }

    let new_body = normalize_inner(body, env, counter);

    for (name, old_val) in saved.into_iter().rev() {
        match old_val {
            Some(v) => {
                env.insert(name, v);
            }
            None => {
                env.remove(&name);
            }
        }
    }

    if is_forall {
        Formula::Forall(new_bindings, Box::new(new_body))
    } else {
        Formula::Exists(new_bindings, Box::new(new_body))
    }
}

fn normalize_structural(
    f: &Formula,
    env: &mut FxHashMap<String, String>,
    counter: &mut usize,
) -> Formula {
    match f {
        Formula::Bool(_)
        | Formula::Int(_)
        | Formula::UInt(_)
        | Formula::BitVec { .. }
        | Formula::Var(..)
        | Formula::SymVar(..) => f.clone(),

        Formula::Not(a) => Formula::Not(Box::new(normalize_inner(a, env, counter))),
        Formula::Neg(a) => Formula::Neg(Box::new(normalize_inner(a, env, counter))),

        Formula::And(terms) => {
            Formula::And(terms.iter().map(|t| normalize_inner(t, env, counter)).collect())
        }
        Formula::Or(terms) => {
            Formula::Or(terms.iter().map(|t| normalize_inner(t, env, counter)).collect())
        }

        Formula::Implies(a, b) => Formula::Implies(
            Box::new(normalize_inner(a, env, counter)),
            Box::new(normalize_inner(b, env, counter)),
        ),
        Formula::Eq(a, b) => Formula::Eq(
            Box::new(normalize_inner(a, env, counter)),
            Box::new(normalize_inner(b, env, counter)),
        ),
        Formula::Lt(a, b) => Formula::Lt(
            Box::new(normalize_inner(a, env, counter)),
            Box::new(normalize_inner(b, env, counter)),
        ),
        Formula::Le(a, b) => Formula::Le(
            Box::new(normalize_inner(a, env, counter)),
            Box::new(normalize_inner(b, env, counter)),
        ),
        Formula::Gt(a, b) => Formula::Gt(
            Box::new(normalize_inner(a, env, counter)),
            Box::new(normalize_inner(b, env, counter)),
        ),
        Formula::Ge(a, b) => Formula::Ge(
            Box::new(normalize_inner(a, env, counter)),
            Box::new(normalize_inner(b, env, counter)),
        ),
        Formula::Add(a, b) => Formula::Add(
            Box::new(normalize_inner(a, env, counter)),
            Box::new(normalize_inner(b, env, counter)),
        ),
        Formula::Sub(a, b) => Formula::Sub(
            Box::new(normalize_inner(a, env, counter)),
            Box::new(normalize_inner(b, env, counter)),
        ),
        Formula::Mul(a, b) => Formula::Mul(
            Box::new(normalize_inner(a, env, counter)),
            Box::new(normalize_inner(b, env, counter)),
        ),
        Formula::Div(a, b) => Formula::Div(
            Box::new(normalize_inner(a, env, counter)),
            Box::new(normalize_inner(b, env, counter)),
        ),
        Formula::Rem(a, b) => Formula::Rem(
            Box::new(normalize_inner(a, env, counter)),
            Box::new(normalize_inner(b, env, counter)),
        ),

        Formula::BvAdd(a, b, w) => Formula::BvAdd(
            Box::new(normalize_inner(a, env, counter)),
            Box::new(normalize_inner(b, env, counter)),
            *w,
        ),
        Formula::BvSub(a, b, w) => Formula::BvSub(
            Box::new(normalize_inner(a, env, counter)),
            Box::new(normalize_inner(b, env, counter)),
            *w,
        ),
        Formula::BvMul(a, b, w) => Formula::BvMul(
            Box::new(normalize_inner(a, env, counter)),
            Box::new(normalize_inner(b, env, counter)),
            *w,
        ),
        Formula::BvUDiv(a, b, w) => Formula::BvUDiv(
            Box::new(normalize_inner(a, env, counter)),
            Box::new(normalize_inner(b, env, counter)),
            *w,
        ),
        Formula::BvSDiv(a, b, w) => Formula::BvSDiv(
            Box::new(normalize_inner(a, env, counter)),
            Box::new(normalize_inner(b, env, counter)),
            *w,
        ),
        Formula::BvURem(a, b, w) => Formula::BvURem(
            Box::new(normalize_inner(a, env, counter)),
            Box::new(normalize_inner(b, env, counter)),
            *w,
        ),
        Formula::BvSRem(a, b, w) => Formula::BvSRem(
            Box::new(normalize_inner(a, env, counter)),
            Box::new(normalize_inner(b, env, counter)),
            *w,
        ),
        Formula::BvAnd(a, b, w) => Formula::BvAnd(
            Box::new(normalize_inner(a, env, counter)),
            Box::new(normalize_inner(b, env, counter)),
            *w,
        ),
        Formula::BvOr(a, b, w) => Formula::BvOr(
            Box::new(normalize_inner(a, env, counter)),
            Box::new(normalize_inner(b, env, counter)),
            *w,
        ),
        Formula::BvXor(a, b, w) => Formula::BvXor(
            Box::new(normalize_inner(a, env, counter)),
            Box::new(normalize_inner(b, env, counter)),
            *w,
        ),
        Formula::BvShl(a, b, w) => Formula::BvShl(
            Box::new(normalize_inner(a, env, counter)),
            Box::new(normalize_inner(b, env, counter)),
            *w,
        ),
        Formula::BvLShr(a, b, w) => Formula::BvLShr(
            Box::new(normalize_inner(a, env, counter)),
            Box::new(normalize_inner(b, env, counter)),
            *w,
        ),
        Formula::BvAShr(a, b, w) => Formula::BvAShr(
            Box::new(normalize_inner(a, env, counter)),
            Box::new(normalize_inner(b, env, counter)),
            *w,
        ),

        Formula::BvULt(a, b, w) => Formula::BvULt(
            Box::new(normalize_inner(a, env, counter)),
            Box::new(normalize_inner(b, env, counter)),
            *w,
        ),
        Formula::BvULe(a, b, w) => Formula::BvULe(
            Box::new(normalize_inner(a, env, counter)),
            Box::new(normalize_inner(b, env, counter)),
            *w,
        ),
        Formula::BvSLt(a, b, w) => Formula::BvSLt(
            Box::new(normalize_inner(a, env, counter)),
            Box::new(normalize_inner(b, env, counter)),
            *w,
        ),
        Formula::BvSLe(a, b, w) => Formula::BvSLe(
            Box::new(normalize_inner(a, env, counter)),
            Box::new(normalize_inner(b, env, counter)),
            *w,
        ),

        Formula::BvNot(a, w) => Formula::BvNot(Box::new(normalize_inner(a, env, counter)), *w),
        Formula::BvToInt(a, w, s) => {
            Formula::BvToInt(Box::new(normalize_inner(a, env, counter)), *w, *s)
        }
        Formula::IntToBv(a, w) => Formula::IntToBv(Box::new(normalize_inner(a, env, counter)), *w),
        Formula::BvExtract { inner, high, low } => Formula::BvExtract {
            inner: Box::new(normalize_inner(inner, env, counter)),
            high: *high,
            low: *low,
        },
        Formula::BvConcat(a, b) => Formula::BvConcat(
            Box::new(normalize_inner(a, env, counter)),
            Box::new(normalize_inner(b, env, counter)),
        ),
        Formula::BvZeroExt(a, bits) => {
            Formula::BvZeroExt(Box::new(normalize_inner(a, env, counter)), *bits)
        }
        Formula::BvSignExt(a, bits) => {
            Formula::BvSignExt(Box::new(normalize_inner(a, env, counter)), *bits)
        }

        Formula::Ite(cond, then_f, else_f) => Formula::Ite(
            Box::new(normalize_inner(cond, env, counter)),
            Box::new(normalize_inner(then_f, env, counter)),
            Box::new(normalize_inner(else_f, env, counter)),
        ),
        Formula::Store(arr, idx, val) => Formula::Store(
            Box::new(normalize_inner(arr, env, counter)),
            Box::new(normalize_inner(idx, env, counter)),
            Box::new(normalize_inner(val, env, counter)),
        ),

        Formula::Select(arr, idx) => Formula::Select(
            Box::new(normalize_inner(arr, env, counter)),
            Box::new(normalize_inner(idx, env, counter)),
        ),

        // Quantifiers are handled in normalize_inner; unreachable here but safe.
        Formula::Forall(..) | Formula::Exists(..) => f.clone(),

        // Formula owns the exhaustive child traversal. Preserve new variant
        // payloads and recurse through their children so bound variables inside
        // predicates, floating-point terms, ADTs, and function applications are
        // normalized without another hand-maintained match table.
        _ => f.clone().map_children(&mut |child| normalize_inner(&child, env, counter)),
    }
}

// ---------------------------------------------------------------------------
// Structural hashing for Formula (used only for bucketing).
// ---------------------------------------------------------------------------

// Discriminant tags so different constructors hash differently even when their
// children hash the same.
const TAG_BOOL: u8 = 0;
const TAG_INT: u8 = 1;
const TAG_UINT: u8 = 2;
const TAG_BITVEC: u8 = 3;
const TAG_VAR: u8 = 4;
const TAG_NOT: u8 = 5;
const TAG_AND: u8 = 6;
const TAG_OR: u8 = 7;
const TAG_IMPLIES: u8 = 8;
const TAG_EQ: u8 = 9;
const TAG_LT: u8 = 10;
const TAG_LE: u8 = 11;
const TAG_GT: u8 = 12;
const TAG_GE: u8 = 13;
const TAG_ADD: u8 = 14;
const TAG_SUB: u8 = 15;
const TAG_MUL: u8 = 16;
const TAG_DIV: u8 = 17;
const TAG_REM: u8 = 18;
const TAG_NEG: u8 = 19;
const TAG_BV_ADD: u8 = 20;
const TAG_BV_SUB: u8 = 21;
const TAG_BV_MUL: u8 = 22;
const TAG_BV_UDIV: u8 = 23;
const TAG_BV_SDIV: u8 = 24;
const TAG_BV_UREM: u8 = 25;
const TAG_BV_SREM: u8 = 26;
const TAG_BV_AND: u8 = 27;
const TAG_BV_OR: u8 = 28;
const TAG_BV_XOR: u8 = 29;
const TAG_BV_NOT: u8 = 30;
const TAG_BV_SHL: u8 = 31;
const TAG_BV_LSHR: u8 = 32;
const TAG_BV_ASHR: u8 = 33;
const TAG_BV_ULT: u8 = 34;
const TAG_BV_ULE: u8 = 35;
const TAG_BV_SLT: u8 = 36;
const TAG_BV_SLE: u8 = 37;
const TAG_BV_TO_INT: u8 = 38;
const TAG_INT_TO_BV: u8 = 39;
const TAG_BV_EXTRACT: u8 = 40;
const TAG_BV_CONCAT: u8 = 41;
const TAG_BV_ZERO_EXT: u8 = 42;
const TAG_BV_SIGN_EXT: u8 = 43;
const TAG_ITE: u8 = 44;
const TAG_FORALL: u8 = 45;
const TAG_EXISTS: u8 = 46;
const TAG_SELECT: u8 = 47;
const TAG_STORE: u8 = 48;

fn hash_formula(f: &Formula, h: &mut impl Hasher) {
    match f {
        Formula::Bool(b) => {
            TAG_BOOL.hash(h);
            b.hash(h);
        }
        Formula::Int(n) => {
            TAG_INT.hash(h);
            n.hash(h);
        }
        Formula::UInt(n) => {
            TAG_UINT.hash(h);
            n.hash(h);
        }
        Formula::BitVec { value, width } => {
            TAG_BITVEC.hash(h);
            value.hash(h);
            width.hash(h);
        }
        Formula::Var(name, sort) => {
            TAG_VAR.hash(h);
            name.hash(h);
            sort.hash(h);
        }
        Formula::Not(a) => {
            TAG_NOT.hash(h);
            hash_formula(a, h);
        }
        Formula::And(terms) => {
            TAG_AND.hash(h);
            terms.len().hash(h);
            for t in terms {
                hash_formula(t, h);
            }
        }
        Formula::Or(terms) => {
            TAG_OR.hash(h);
            terms.len().hash(h);
            for t in terms {
                hash_formula(t, h);
            }
        }
        Formula::Implies(a, b) => {
            TAG_IMPLIES.hash(h);
            hash_formula(a, h);
            hash_formula(b, h);
        }
        Formula::Eq(a, b) => {
            TAG_EQ.hash(h);
            hash_formula(a, h);
            hash_formula(b, h);
        }
        Formula::Lt(a, b) => {
            TAG_LT.hash(h);
            hash_formula(a, h);
            hash_formula(b, h);
        }
        Formula::Le(a, b) => {
            TAG_LE.hash(h);
            hash_formula(a, h);
            hash_formula(b, h);
        }
        Formula::Gt(a, b) => {
            TAG_GT.hash(h);
            hash_formula(a, h);
            hash_formula(b, h);
        }
        Formula::Ge(a, b) => {
            TAG_GE.hash(h);
            hash_formula(a, h);
            hash_formula(b, h);
        }
        Formula::Add(a, b) => {
            TAG_ADD.hash(h);
            hash_formula(a, h);
            hash_formula(b, h);
        }
        Formula::Sub(a, b) => {
            TAG_SUB.hash(h);
            hash_formula(a, h);
            hash_formula(b, h);
        }
        Formula::Mul(a, b) => {
            TAG_MUL.hash(h);
            hash_formula(a, h);
            hash_formula(b, h);
        }
        Formula::Div(a, b) => {
            TAG_DIV.hash(h);
            hash_formula(a, h);
            hash_formula(b, h);
        }
        Formula::Rem(a, b) => {
            TAG_REM.hash(h);
            hash_formula(a, h);
            hash_formula(b, h);
        }
        Formula::Neg(a) => {
            TAG_NEG.hash(h);
            hash_formula(a, h);
        }
        Formula::BvAdd(a, b, w) => {
            TAG_BV_ADD.hash(h);
            hash_bv_binary(a, b, *w, h);
        }
        Formula::BvSub(a, b, w) => {
            TAG_BV_SUB.hash(h);
            hash_bv_binary(a, b, *w, h);
        }
        Formula::BvMul(a, b, w) => {
            TAG_BV_MUL.hash(h);
            hash_bv_binary(a, b, *w, h);
        }
        Formula::BvUDiv(a, b, w) => {
            TAG_BV_UDIV.hash(h);
            hash_bv_binary(a, b, *w, h);
        }
        Formula::BvSDiv(a, b, w) => {
            TAG_BV_SDIV.hash(h);
            hash_bv_binary(a, b, *w, h);
        }
        Formula::BvURem(a, b, w) => {
            TAG_BV_UREM.hash(h);
            hash_bv_binary(a, b, *w, h);
        }
        Formula::BvSRem(a, b, w) => {
            TAG_BV_SREM.hash(h);
            hash_bv_binary(a, b, *w, h);
        }
        Formula::BvAnd(a, b, w) => {
            TAG_BV_AND.hash(h);
            hash_bv_binary(a, b, *w, h);
        }
        Formula::BvOr(a, b, w) => {
            TAG_BV_OR.hash(h);
            hash_bv_binary(a, b, *w, h);
        }
        Formula::BvXor(a, b, w) => {
            TAG_BV_XOR.hash(h);
            hash_bv_binary(a, b, *w, h);
        }
        Formula::BvShl(a, b, w) => {
            TAG_BV_SHL.hash(h);
            hash_bv_binary(a, b, *w, h);
        }
        Formula::BvLShr(a, b, w) => {
            TAG_BV_LSHR.hash(h);
            hash_bv_binary(a, b, *w, h);
        }
        Formula::BvAShr(a, b, w) => {
            TAG_BV_ASHR.hash(h);
            hash_bv_binary(a, b, *w, h);
        }
        Formula::BvULt(a, b, w) => {
            TAG_BV_ULT.hash(h);
            hash_bv_binary(a, b, *w, h);
        }
        Formula::BvULe(a, b, w) => {
            TAG_BV_ULE.hash(h);
            hash_bv_binary(a, b, *w, h);
        }
        Formula::BvSLt(a, b, w) => {
            TAG_BV_SLT.hash(h);
            hash_bv_binary(a, b, *w, h);
        }
        Formula::BvSLe(a, b, w) => {
            TAG_BV_SLE.hash(h);
            hash_bv_binary(a, b, *w, h);
        }
        Formula::BvNot(a, w) => {
            TAG_BV_NOT.hash(h);
            w.hash(h);
            hash_formula(a, h);
        }
        Formula::BvToInt(a, w, signed) => {
            TAG_BV_TO_INT.hash(h);
            w.hash(h);
            signed.hash(h);
            hash_formula(a, h);
        }
        Formula::IntToBv(a, w) => {
            TAG_INT_TO_BV.hash(h);
            w.hash(h);
            hash_formula(a, h);
        }
        Formula::BvExtract { inner, high, low } => {
            TAG_BV_EXTRACT.hash(h);
            high.hash(h);
            low.hash(h);
            hash_formula(inner, h);
        }
        Formula::BvConcat(a, b) => {
            TAG_BV_CONCAT.hash(h);
            hash_formula(a, h);
            hash_formula(b, h);
        }
        Formula::BvZeroExt(a, bits) => {
            TAG_BV_ZERO_EXT.hash(h);
            bits.hash(h);
            hash_formula(a, h);
        }
        Formula::BvSignExt(a, bits) => {
            TAG_BV_SIGN_EXT.hash(h);
            bits.hash(h);
            hash_formula(a, h);
        }
        Formula::Ite(cond, then_f, else_f) => {
            TAG_ITE.hash(h);
            hash_formula(cond, h);
            hash_formula(then_f, h);
            hash_formula(else_f, h);
        }
        Formula::Store(arr, idx, val) => {
            TAG_STORE.hash(h);
            hash_formula(arr, h);
            hash_formula(idx, h);
            hash_formula(val, h);
        }
        Formula::Select(arr, idx) => {
            TAG_SELECT.hash(h);
            hash_formula(arr, h);
            hash_formula(idx, h);
        }
        Formula::Forall(bindings, body) => {
            TAG_FORALL.hash(h);
            hash_bindings(bindings, h);
            hash_formula(body, h);
        }
        Formula::Exists(bindings, body) => {
            TAG_EXISTS.hash(h);
            hash_bindings(bindings, h);
            hash_formula(body, h);
        }
        // Unknown variants (#[non_exhaustive]) hash by Debug as a fallback;
        // this only affects bucketing, and `vcs_equivalent` still gates merges.
        other => {
            255u8.hash(h);
            format!("{other:?}").hash(h);
        }
    }
}

fn hash_bv_binary(a: &Formula, b: &Formula, w: u32, h: &mut impl Hasher) {
    w.hash(h);
    hash_formula(a, h);
    hash_formula(b, h);
}

fn hash_bindings(bindings: &[(trust_types::Symbol, Sort)], h: &mut impl Hasher) {
    bindings.len().hash(h);
    for (name, sort) in bindings {
        name.hash(h);
        sort.hash(h);
    }
}

#[cfg(test)]
mod tests {
    use trust_types::fx::FxHashMap;
    use trust_types::{Formula, SourceSpan, StateMachineMetadata, VcKind};

    use super::*;

    fn var(name: &str) -> Formula {
        Formula::Var(name.into(), Sort::Int)
    }

    fn make_vc(kind: VcKind, formula: Formula) -> VerificationCondition {
        VerificationCondition {
            kind,
            function: "test_fn".into(),
            location: SourceSpan::default(),
            formula,
            contract_metadata: None,
        }
    }

    /// Trivial uniform plan signature: every VC routes identically.
    fn uniform(_i: usize) -> u8 {
        0
    }

    #[test]
    fn identical_vcs_collapse_to_one_group() {
        let vcs = vec![
            make_vc(
                VcKind::DivisionByZero,
                Formula::Eq(Box::new(var("y")), Box::new(Formula::Int(0))),
            ),
            make_vc(
                VcKind::DivisionByZero,
                Formula::Eq(Box::new(var("y")), Box::new(Formula::Int(0))),
            ),
            make_vc(
                VcKind::DivisionByZero,
                Formula::Eq(Box::new(var("y")), Box::new(Formula::Int(0))),
            ),
        ];
        let groups = dedup_groups(&vcs, uniform);
        assert_eq!(groups.len(), 1, "three identical VCs must collapse to one group");
        assert_eq!(groups[0].representative, 0);
        assert_eq!(groups[0].members, vec![0, 1, 2]);
    }

    #[test]
    fn alpha_equivalent_quantified_vcs_collapse() {
        // forall x. x > 0  vs  forall y. y > 0 -- same obligation, different
        // bound-variable name.
        let f1 = Formula::Forall(
            vec![("x".into(), Sort::Int)],
            Box::new(Formula::Gt(Box::new(var("x")), Box::new(Formula::Int(0)))),
        );
        let f2 = Formula::Forall(
            vec![("y".into(), Sort::Int)],
            Box::new(Formula::Gt(Box::new(var("y")), Box::new(Formula::Int(0)))),
        );
        let vcs = vec![make_vc(VcKind::Postcondition, f1), make_vc(VcKind::Postcondition, f2)];
        let groups = dedup_groups(&vcs, uniform);
        assert_eq!(groups.len(), 1, "alpha-equivalent VCs must merge");
        assert_eq!(groups[0].members, vec![0, 1]);
    }

    #[test]
    fn canonical_binder_name_cannot_capture_a_free_variable() {
        let has_free_canonical_name = Formula::Exists(
            vec![("a".into(), Sort::Int)],
            Box::new(Formula::Eq(Box::new(var("a")), Box::new(var("__alpha_0")))),
        );
        let genuinely_reflexive = Formula::Exists(
            vec![("b".into(), Sort::Int)],
            Box::new(Formula::Eq(Box::new(var("b")), Box::new(var("b")))),
        );
        assert_ne!(
            normalize_alpha(&has_free_canonical_name),
            normalize_alpha(&genuinely_reflexive),
            "alpha-normalization must preserve the free-vs-bound distinction"
        );

        let vcs = vec![
            make_vc(VcKind::Postcondition, has_free_canonical_name),
            make_vc(VcKind::Postcondition, genuinely_reflexive),
        ];
        assert_eq!(
            dedup_groups(&vcs, uniform).len(),
            2,
            "non-equivalent obligations must never share a solver verdict"
        );
    }

    #[test]
    fn alpha_normalization_recurses_through_new_term_families() {
        let quantified_predicate = |binder: &str| {
            Formula::Exists(
                vec![(binder.into(), Sort::Int)],
                Box::new(Formula::Pred(
                    "is_valid".into(),
                    vec![Formula::SymVar(binder.into(), Sort::Int)],
                )),
            )
        };
        let vcs = vec![
            make_vc(VcKind::Postcondition, quantified_predicate("a")),
            make_vc(VcKind::Postcondition, quantified_predicate("b")),
        ];
        assert_eq!(dedup_groups(&vcs, uniform).len(), 1);
    }

    #[test]
    fn different_free_vars_do_not_merge() {
        // Free variables are distinct program values: never merged.
        let vcs = vec![
            make_vc(
                VcKind::DivisionByZero,
                Formula::Eq(Box::new(var("b")), Box::new(Formula::Int(0))),
            ),
            make_vc(
                VcKind::DivisionByZero,
                Formula::Eq(Box::new(var("c")), Box::new(Formula::Int(0))),
            ),
        ];
        let groups = dedup_groups(&vcs, uniform);
        assert_eq!(groups.len(), 2, "distinct free vars must NOT merge");
    }

    #[test]
    fn different_kinds_do_not_merge() {
        let formula = Formula::Eq(Box::new(var("y")), Box::new(Formula::Int(0)));
        let vcs = vec![
            make_vc(VcKind::DivisionByZero, formula.clone()),
            make_vc(VcKind::RemainderByZero, formula),
        ];
        let groups = dedup_groups(&vcs, uniform);
        assert_eq!(groups.len(), 2, "different VcKind must NOT merge");
    }

    #[test]
    fn different_plan_signatures_do_not_merge() {
        // Identical obligations, but the caller reports differing routing
        // requirements -> kept separate.
        let vcs = vec![
            make_vc(
                VcKind::DivisionByZero,
                Formula::Eq(Box::new(var("y")), Box::new(Formula::Int(0))),
            ),
            make_vc(
                VcKind::DivisionByZero,
                Formula::Eq(Box::new(var("y")), Box::new(Formula::Int(0))),
            ),
        ];
        // VC 0 -> sig 0, VC 1 -> sig 1.
        let groups = dedup_groups(&vcs, |i| i as u8);
        assert_eq!(groups.len(), 2, "different plan signatures must NOT merge");
    }

    #[test]
    fn order_and_count_preserved_with_mixed_batch() {
        // Batch: [A, B, A, C, B] where A,B,C are distinct obligations.
        let a = || {
            make_vc(
                VcKind::DivisionByZero,
                Formula::Eq(Box::new(var("a")), Box::new(Formula::Int(0))),
            )
        };
        let b = || {
            make_vc(
                VcKind::DivisionByZero,
                Formula::Eq(Box::new(var("b")), Box::new(Formula::Int(0))),
            )
        };
        let c = || {
            make_vc(
                VcKind::DivisionByZero,
                Formula::Eq(Box::new(var("c")), Box::new(Formula::Int(0))),
            )
        };
        let vcs = vec![a(), b(), a(), c(), b()];
        let groups = dedup_groups(&vcs, uniform);
        assert_eq!(groups.len(), 3, "three distinct obligations -> three groups");

        // Every original index appears in exactly one group's members.
        let mut all: Vec<usize> = groups.iter().flat_map(|g| g.members.iter().copied()).collect();
        all.sort_unstable();
        assert_eq!(all, vec![0, 1, 2, 3, 4], "every input index must appear exactly once");

        // Representative is the lowest member of its group.
        for g in &groups {
            assert_eq!(g.representative, *g.members.iter().min().unwrap());
        }

        // A's group is {0,2}, B's is {1,4}, C's is {3}.
        let group_with = |idx: usize| groups.iter().find(|g| g.members.contains(&idx)).unwrap();
        assert_eq!(group_with(0).members, vec![0, 2]);
        assert_eq!(group_with(1).members, vec![1, 4]);
        assert_eq!(group_with(3).members, vec![3]);
    }

    /// Build a two-state machine `A --ev--> B` whose transition label and state
    /// names are taken from `tag`, so callers can produce *distinct* automata.
    fn machine(tag: &str) -> StateMachineMetadata {
        let states = vec![format!("{tag}_A"), format!("{tag}_B")];
        let mut labels: FxHashMap<usize, Vec<String>> = FxHashMap::default();
        labels.insert(0, vec![format!("{tag}_A")]);
        labels.insert(1, vec![format!("{tag}_B")]);
        StateMachineMetadata {
            states,
            init_states: vec![0],
            transitions: vec![(0, format!("{tag}_ev"), 1)],
            labels,
        }
    }

    /// REGRESSION (ay-sequential-dedup soundness): two `Temporal` VCs with an
    /// IDENTICAL `property` and IDENTICAL `formula` but DIFFERENT state machines
    /// must NOT be deduped. `kind.description()` is `"temporal: {property}"`,
    /// which DROPS the `machine`, and the machine is not in `formula` either —
    /// so the lossy-description path would merge them and let a machine that
    /// VIOLATES the property inherit `Proved` from a safe representative
    /// (a false proof). They must land in separate groups, so the caller's
    /// per-group verdict fan-out can never share a verdict across the two.
    #[test]
    fn temporal_vcs_with_different_machines_do_not_merge() {
        let property = "AG safe".to_string();
        let formula = Formula::Eq(Box::new(var("s")), Box::new(Formula::Int(0)));

        let vcs = vec![
            // Representative: a SAFE machine that would prove the property.
            make_vc(
                VcKind::Temporal { property: property.clone(), machine: Some(machine("safe")) },
                formula.clone(),
            ),
            // A DIFFERENT machine that may VIOLATE the property — identical
            // property + formula, but it must not inherit the representative's
            // verdict.
            make_vc(
                VcKind::Temporal { property: property.clone(), machine: Some(machine("unsafe")) },
                formula.clone(),
            ),
        ];

        // Sanity: the two kinds are description-equal (the lossy projection the
        // old code keyed on) and the formulas are identical, so the ONLY thing
        // distinguishing them is the machine.
        assert_eq!(vcs[0].kind.description(), vcs[1].kind.description());
        assert_eq!(normalize_alpha(&vcs[0].formula), normalize_alpha(&vcs[1].formula));
        // The pairwise equivalence check must refuse to merge them.
        assert!(
            !vcs_equivalent(&vcs[0], &vcs[1]),
            "Temporal VCs with different machines must never be equivalent"
        );

        let groups = dedup_groups(&vcs, uniform);
        assert_eq!(
            groups.len(),
            2,
            "Temporal VCs with different machines must NOT share a dedup group"
        );
        // Each VC is its own representative -> each is solved independently, so a
        // verdict for one can never reach the other.
        let mut reps: Vec<usize> = groups.iter().map(|g| g.representative).collect();
        reps.sort_unstable();
        assert_eq!(reps, vec![0, 1]);
        for g in &groups {
            assert_eq!(g.members.len(), 1, "no machine-bearing VC may absorb another");
        }
    }

    /// Even two Temporal VCs with the SAME machine are conservatively kept
    /// separate: machine-bearing kinds are never deduped (soundness over
    /// hit-rate). A redundant solve is always acceptable.
    #[test]
    fn temporal_vcs_are_never_deduped_even_when_identical() {
        let property = "AG safe".to_string();
        let formula = Formula::Bool(true);
        let m = machine("same");
        let vcs = vec![
            make_vc(
                VcKind::Temporal { property: property.clone(), machine: Some(m.clone()) },
                formula.clone(),
            ),
            make_vc(VcKind::Temporal { property, machine: Some(m) }, formula),
        ];
        let groups = dedup_groups(&vcs, uniform);
        assert_eq!(groups.len(), 2, "machine-bearing kinds are conservatively never merged");
    }

    /// The other temporal-backend kinds that check an automaton model
    /// (`Deadlock`, `DeadState`, `Liveness`, `Fairness`) are likewise never
    /// deduped, even when their description + formula coincide.
    #[test]
    fn automaton_bearing_kinds_are_never_deduped() {
        let formula = Formula::Bool(true);
        let pairs = [
            (VcKind::Deadlock, VcKind::Deadlock),
            (VcKind::DeadState { state: "S".into() }, VcKind::DeadState { state: "S".into() }),
        ];
        for (k1, k2) in pairs {
            let vcs = vec![make_vc(k1, formula.clone()), make_vc(k2, formula.clone())];
            let groups = dedup_groups(&vcs, uniform);
            assert_eq!(
                groups.len(),
                2,
                "automaton-bearing kinds must never be deduped: {:?}",
                vcs[0].kind.description()
            );
        }
    }

    #[test]
    fn empty_batch_yields_no_groups() {
        let vcs: Vec<VerificationCondition> = Vec::new();
        let groups = dedup_groups(&vcs, uniform);
        assert!(groups.is_empty());
    }

    #[test]
    fn singleton_batch_yields_one_group() {
        let vcs = vec![make_vc(VcKind::IndexOutOfBounds, Formula::Bool(true))];
        let groups = dedup_groups(&vcs, uniform);
        assert_eq!(groups.len(), 1);
        assert_eq!(groups[0].members, vec![0]);
    }
}
