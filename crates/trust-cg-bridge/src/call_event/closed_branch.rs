//! The closed-branch kernel retry (DECISION_QUEUE AGG-SSA-2).
//!
//! The machine executor runs both arms of every conditional branch, so a branch whose condition
//! is ground (no register, memory or symbol in it) leaves `Ite(c, a, e)` in the machine value with
//! the untaken arm still present. That arm can read memory no path writes (s23: the `E::B`
//! payload read on the `E::A` path), which puts the item outside the kernel's bit-vector
//! fragment, so the kernel declines a conjunction ay already proved.
//!
//! [`retry`] replaces each ground-condition `Ite` whose arms have one sort, on either side of any
//! item, by the arm its condition selects, bottom-up, and records the condition the choice rests
//! on (`c`, or `not c` for the else arm) as a premise `ite(condition, 1, 0) == 1`. The kernel then
//! proves the folded conjunction, and each premise on its own (by bit-blast certificate only),
//! for every input. Where every premise holds, each replaced node equals the node it replaced (bottom-up, by induction: a premise is
//! recorded over the already-folded condition, and the folded condition equals the original
//! one), so the original items hold. A wrong choice makes its premise false and the kernel
//! declines: the grade stays [VALIDATED], never Refuted. The chooser is not trusted; what is
//! trusted is this module's substitution, that the node it puts in place is the arm the recorded
//! premise selects, and that the two arms have the same sort.
//!
//! [`canonicalize`] then rewrites `x - 0` to `x` and `ite(p, 1, 0) != 0` to `p` in the folded
//! items, each instance a kernel-proved premise `ite(rewritten == original, 1, 0) == 1`, so that
//! the machine's and the spec's renderings of one test become one term and the bit-blast stays
//! under the re-checkable refutation limit (s23's value goal, the unit shape
//! `s23_shape_is_kernel_proved` and the gate's `rung` at O0 alike, under `TRUST_GATE_TRACE=1`:
//! 46928 refutation steps unrewritten, 130 rewritten).
//!
//! The folded items are proved as one conjunction by `try_kernel_recheckable_conjunction` (the
//! bit-blast certificate or an O(1) route); when that gives no kernel evidence, by the branch split
//! (DECISION_QUEUE BRANCH-SPLIT-1), one kernel-checked term against the branching reflection of the
//! folded items, compiled only with `kernel-recheck` (s23 at O2, whose `tbz` test against the
//! spec's `x & 1 == 0` leaves the folded value over the refutation limit). Either way the premises
//! are still proved one by one, by bit-blast certificate only.
//!
//! The evidence is `KernelRecheckableWithSideConditions`, built by
//! `ProvenEvidence::with_side_conditions`, which refuses a part the kernel did not check (a wide
//! multiply's citation): the value evidence is about the
//! folded conjunction, and the side conditions are the premises' certificates, so the fold is
//! visible in the verdict (object replay refuses it as a side-conditioned row; a branch-split value
//! is label-only, as BRANCH-SPLIT-1 says).
//!
//! The retry runs only where the unfolded conjunction cannot be lowered to the kernel's
//! fragment and the folded one can (a 128-bit register pair lowered half by half, as the kernel
//! conjunction splits it), and only after ay's steps (4) and (4b), so no Refuted or
//! Unknown verdict depends on it.

use trust_types::check_formula_sort;

use super::*;
use crate::verify_output::{formula_to_bvexpr, split_register_pair_128};

/// The folded items and the premises, kept apart so a premise is never folded again.
#[derive(Debug, PartialEq)]
pub(super) struct Folded {
    pub(super) items: Vec<(Formula, Formula)>,
    pub(super) premises: Vec<(Formula, Formula)>,
}

/// The kernel retry: `Some` only when the unfolded conjunction has an item outside the kernel's
/// fragment, the folded items and every premise are inside it, and the kernel accepts them all.
pub(super) fn retry(conj: &[(Formula, Formula)]) -> Option<ProvenEvidence> {
    if conj.iter().all(lowers_item) {
        return None;
    }
    let folded = canonicalize(fold(conj)?);
    if !folded.items.iter().chain(&folded.premises).all(lowers_item) {
        return None;
    }
    check(&folded)
}

/// Two exact identities applied to the folded items, so that the machine's and the spec's
/// renderings of one test become one term: `x - 0` is `x`, and `ite(p, 1, 0) != 0` is `p`. Each
/// instance is a premise `ite(rewritten == original, 1, 0) == 1` the kernel proves on its own,
/// so neither identity is trusted; what is trusted is, as for the fold, that the node put in
/// place is the one the premise names (bottom-up, so a premise reads already rewritten
/// children).
pub(super) fn canonicalize(mut folded: Folded) -> Folded {
    let mut eqs: Vec<(Formula, Formula)> = Vec::new();
    let mut one = |f: &Formula| {
        f.clone().map(&mut |node| {
            let (rewritten, original) = match node {
                Formula::BvSub(x, z, w)
                    if matches!(*z, Formula::BitVec { value: 0, width } if width == w) =>
                {
                    let original = Formula::BvSub(x.clone(), z, w);
                    ((*x).clone(), original)
                }
                Formula::Not(inner) => match *inner {
                    Formula::Eq(l, r) => match as_indicator(&l, &r).cloned() {
                        Some(p) => (p, Formula::Not(Box::new(Formula::Eq(l, r)))),
                        None => return Formula::Not(Box::new(Formula::Eq(l, r))),
                    },
                    other => return Formula::Not(Box::new(other)),
                },
                other => return other,
            };
            let (r, o) = if check_formula_sort(&rewritten).ok() == Some(Sort::Bool) {
                (pred_to_int(rewritten.clone(), 1), pred_to_int(original, 1))
            } else {
                (rewritten.clone(), original)
            };
            let premise = (
                pred_to_int(Formula::Eq(Box::new(r), Box::new(o)), 1),
                Formula::BitVec { value: 1, width: 1 },
            );
            if !eqs.contains(&premise) {
                eqs.push(premise);
            }
            rewritten
        })
    };
    folded.items = folded.items.iter().map(|(l, r)| (one(l), one(r))).collect();
    folded.premises.extend(eqs);
    folded
}

/// `p` when `l == r` reads `ite(p, 1, 0) == 0` at one width.
fn as_indicator<'a>(l: &'a Formula, r: &Formula) -> Option<&'a Formula> {
    let Formula::Ite(p, one, zero) = l else {
        return None;
    };
    match (&**one, &**zero, r) {
        (
            Formula::BitVec { value: 1, width: w1 },
            Formula::BitVec { value: 0, width: w0 },
            Formula::BitVec { value: 0, width: wr },
        ) if w1 == w0 && w0 == wr => Some(p),
        _ => None,
    }
}

/// The kernel's verdict on a fold: the items as one conjunction, each premise on its own. Every
/// part must be kernel evidence ([`ProvenEvidence::with_side_conditions`] refuses a wide
/// multiply's `StructuralCitation`, which the kernel did not check). The items take
/// `try_kernel_recheckable_conjunction`'s kernel evidence, else the branch split's
/// ([`branch_split`]); a branch-split success does not excuse a premise. A premise is a formula ay
/// never discharged, so it takes only a bit-blast certificate: an O(1) instantiation's reading of
/// its wrapper is matcher-trusted, backed by ay's prior proof of the same formula.
fn check(folded: &Folded) -> Option<ProvenEvidence> {
    let value = match try_kernel_recheckable_conjunction(&folded.items) {
        Some(e) if e.is_kernel() => e,
        _ => branch_split(&folded.items)?,
    };
    let side_conditions = folded
        .premises
        .iter()
        .map(|p| bit_blast_only(try_kernel_recheckable_conjunction(std::slice::from_ref(p))?))
        .collect::<Option<Vec<_>>>()?;
    ProvenEvidence::with_side_conditions(value, side_conditions)
}

/// The branch split (DECISION_QUEUE BRANCH-SPLIT-1) on the folded items: `Some` only when the
/// kernel accepted one term against the goal built from those items alone. It is the recording
/// wrapper step (5) calls too, so the `test-hooks` recorder shows this call.
#[cfg(feature = "kernel-recheck")]
fn branch_split(items: &[(Formula, Formula)]) -> Option<ProvenEvidence> {
    crate::verify_output_instantiate::try_branch_split_conjunction(items)
}

/// Without `kernel-recheck` the route is not compiled: `None`, as at step (5).
#[cfg(not(feature = "kernel-recheck"))]
fn branch_split(_items: &[(Formula, Formula)]) -> Option<ProvenEvidence> {
    None
}

fn bit_blast_only(e: ProvenEvidence) -> Option<ProvenEvidence> {
    matches!(e, ProvenEvidence::KernelRecheckable(_) | ProvenEvidence::KernelRecheckablePair { .. })
        .then_some(e)
}

/// Whether an item lowers to the kernel's fragment as the kernel conjunction reads it: a 128-bit
/// register pair is split at bit 64 first, and each half must lower.
fn lowers_item((l, r): &(Formula, Formula)) -> bool {
    match (split_register_pair_128(l), split_register_pair_128(r)) {
        (Some((lh, ll)), Some((rh, rl))) => [lh, ll, rh, rl].iter().all(lowers),
        _ => lowers(l) && lowers(r),
    }
}

fn lowers(f: &Formula) -> bool {
    formula_to_bvexpr(f).is_ok()
}

/// `Some` when at least one `Ite` had a ground condition; `None` otherwise (the retry would be
/// the declined goal again).
pub(super) fn fold(conj: &[(Formula, Formula)]) -> Option<Folded> {
    fold_with(conj, &ground_bool)
}

/// [`fold`] with the arm chooser as a parameter, so a test can hand it a wrong one.
pub(super) fn fold_with(
    conj: &[(Formula, Formula)],
    choose: &dyn Fn(&Formula) -> Option<bool>,
) -> Option<Folded> {
    let mut chosen: Vec<(Formula, bool)> = Vec::new();
    let mut fold_one = |f: &Formula| {
        f.clone().map(&mut |node| {
            let Formula::Ite(c, a, e) = node else {
                return node;
            };
            let same_sort = matches!(
                (check_formula_sort(&a), check_formula_sort(&e)),
                (Ok(sa), Ok(se)) if sa == se
            );
            match choose(&c).filter(|_| same_sort) {
                Some(v) => {
                    if !chosen.iter().any(|(p, pv)| *p == *c && *pv == v) {
                        chosen.push(((*c).clone(), v));
                    }
                    if v { *a } else { *e }
                }
                None => Formula::Ite(c, a, e),
            }
        })
    };
    let items: Vec<(Formula, Formula)> =
        conj.iter().map(|(l, r)| (fold_one(l), fold_one(r))).collect();
    if chosen.is_empty() {
        return None;
    }
    let premises = chosen
        .into_iter()
        .map(|(c, v)| {
            let held = if v { c } else { Formula::Not(Box::new(c)) };
            (pred_to_int(held, 1), Formula::BitVec { value: 1, width: 1 })
        })
        .collect();
    Some(Folded { items, premises })
}

/// The value of a ground condition: one with no variable, memory, quantifier or uninterpreted
/// symbol in it (the evaluator would read those as its zero state). An evaluation error is not
/// ground. The value is only a choice; the kernel checks the premise it becomes.
fn ground_bool(c: &Formula) -> Option<bool> {
    let mut ground = true;
    c.visit(&mut |node| {
        ground &= !matches!(
            node,
            Formula::Var(..)
                | Formula::SymVar(..)
                | Formula::Select(..)
                | Formula::Store(..)
                | Formula::ConstArray { .. }
                | Formula::Forall(..)
                | Formula::Exists(..)
                | Formula::Pred(..)
                | Formula::Ctor { .. }
                | Formula::Sel { .. }
                | Formula::IsCtor { .. }
                | Formula::FnApp { .. }
        );
    });
    ground.then(|| trust_machine_sem::ConcreteState::new().eval_bool(c).ok()).flatten()
}

#[cfg(test)]
#[path = "closed_branch/tests.rs"]
mod tests;
