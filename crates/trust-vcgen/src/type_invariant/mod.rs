//! TINV — the inferred type-invariant lane
//! (`docs/design/2026-10-04-type-invariant-tinv.md`).
//!
//! Built in the design's §6 order. So far:
//! * step 3, [`unwind`]: the strategy-independent classifier of the unwind (U) points at
//!   which an invariant is owed;
//! * step 7 (increment 7.4), [`obligations`]: the PURE enumeration of the situated
//!   E/C/R/U/M/Drop points of one body, and here the conjunct vocabulary
//!   ([`FieldTerm`], [`CandidateConjunct`], [`TinvType`]) with its instantiation
//!   ([`Sigma`], [`instantiate`]);
//! * step 8 (increments 8a/8b), [`candidate`]: the UNTRUSTED candidate seed — the P3
//!   templates over those placeholders, the construction sites they are seeded from, and
//!   the exact evaluator step 9's non-vacuity gate checks a model with. It proposes;
//!   Houdini and `certify_vc` decide.
//!
//! * step 7 (increment 7.5), [`obligations::type_invariant_check_vcs`]: the SITUATED
//!   `VcKind::TypeInvariant` rows of those points, built inside the ordinary safety walk
//!   by the crate-private shim `generate::tinv_rows`.
//!
//! * step 7 (increment 7.6), [`houdini`]: the Houdini fixpoint over those rows (an
//!   oracle filter with a vacuity probe) and the certify mint loop; the only constructor
//!   of a published row.
//!
//! * step 7 (increment 7.7): the kernel kind gate ADMITS `VcKind::TypeInvariant`, so a
//!   recorded, situated row (`VerificationCondition::type_invariant_situatedness_refusal`)
//!   can mint `CleanCic` evidence through `trust_certify::certify_vc`.
//!
//! * step 10 (increment 10.2), [`use_set`]: what a use site may assume from one run
//!   ([`TinvUseSet`], built only from a [`houdini::TinvOutcome`]), and the crate-private
//!   `generate::type_invariant_facts`, the TAGGED entry and post-call facts a body may
//!   assume. Nothing conjoins them into a row until step 10.3.
//!
//! * TINV-21, [`arm_lemma`]: kernel-certified `Some`-arm lemmas of inventory getters,
//!   minted by [`houdini::houdini`] before its fixpoint and consumed by the rows of a
//!   caller as sealed arm facts (design §6 item 2, "peek composition").
//!
//! Nothing here publishes authority outside tests: nothing calls [`houdini::houdini`]
//! outside tests until step 9 wires it with `certify_vc`, and nothing consumes a
//! certificate until step 10's use-site facts.

pub mod arm_lemma;
pub mod candidate;
pub mod houdini;
pub mod obligations;
pub mod unwind;
pub mod use_set;

use std::collections::{BTreeSet, HashSet};

use trust_types::{BlockId, Formula, Sort, Ty};
pub use use_set::{
    TinvAssumedRow, TinvGenerationRecord, TinvUseSet, TinvUseSetRefusal,
    with_tinv_assumed_rows_scope,
};
pub(crate) use use_set::{note_scope_use_set, record_assumed_row, record_scope_admits};

/// Facts read from the rustc MIR body the TINV pre-pass inventories, handed to vcgen
/// beside the extracted model (design §6 step 3).
///
/// A CROSS-CHECK ONLY: no U point and no U state depends on these. [`unwind::u_point`] and
/// [`unwind::body_regions`] read the model, and the verdict is identical with and without
/// facts and under `panic=unwind` and `panic=abort`. A disagreement between the facts and
/// the model withholds the certificate ([`unwind::cross_check`]). The edge rustc's
/// `UnwindAction` carries is deliberately NOT here: it is rewritten by panic strategy
/// (`AbortUnwindingCalls`, `-Zpanic-in-drop`), and carrying it would invite a consumer to
/// read it as a nounwind exemption.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct TinvBodyFacts {
    /// Blocks rustc marks `is_cleanup`.
    pub cleanup_blocks: HashSet<BlockId>,
    /// Blocks whose terminator is `Drop { replace: true, .. }`. The flag survives
    /// `ElaborateDrops` only for a drop behind a pointer (`LookupResult::Parent`), so it is
    /// a cross-check of the structural recogniser, never the recogniser.
    pub replace_drops: HashSet<BlockId>,
    /// The number of basic blocks in the rustc body.
    pub block_count: usize,
    /// Decision TINV-32: the candidate types (by name) SOME constant operand of the rustc
    /// body may hold — the census walk over every constant's rustc type — or `None` when
    /// there is no such evidence (no census, or a constant whose type keeps a parameter or
    /// an alias, or holds a `dyn`). See [`TinvBodyFacts::constants_clear`].
    pub constants_may_hold: Option<BTreeSet<String>>,
    /// Decision TINV-33: the candidate types (by name) no `dyn` of the crate can hide
    /// (crate-wide census evidence, the same in every body). Empty: no evidence.
    pub dyn_unreachable: BTreeSet<String>,
    /// Decision TINV-33: the candidate types (by name) no type parameter of a polymorphic
    /// body of the crate can be instantiated to reach (a subset of `dyn_unreachable`).
    pub param_unreachable: BTreeSet<String>,
}

impl TinvBodyFacts {
    /// Decision TINV-32: whether the census proved that no constant operand of this body
    /// can hold a value of `name` (so an opaque constant need not refuse it).
    #[must_use]
    pub fn constants_clear(&self, name: &str) -> bool {
        self.constants_may_hold.as_ref().is_some_and(|held| !held.contains(name))
    }

    /// Decision TINV-33: the evidence the mint's reach walk may use for `name`.
    #[must_use]
    pub fn opaque_reach(&self, name: &str) -> crate::place_write::OpaqueReach {
        let dyn_cannot_reach = self.dyn_unreachable.contains(name);
        crate::place_write::OpaqueReach {
            dyn_cannot_reach,
            param_cannot_reach: dyn_cannot_reach && self.param_unreachable.contains(name),
        }
    }
}

/// A conjunct placeholder: the value of field `i`, or its length.
///
/// `Len` exists because the templates (design P3) read `len(f)`, and the generator names
/// a length differently per field type: a `Vec` field (`Ty::Seq`) is its own Int-sorted
/// name (`guards::coll_len_var_place`), a `&[T]`/`&str` field is `{name}__slice_len`
/// (`generate::SLICE_LEN_SUFFIX`). [`Sigma`] carries the rendered term per field.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum FieldTerm {
    Value(usize),
    Len(usize),
}

const VALUE_PREFIX: &str = "$tinv_v";
const LEN_PREFIX: &str = "$tinv_l";

/// The placeholder variable for `t`: `$tinv_v{i}` or `$tinv_l{i}`, Int-sorted (G16: the
/// templates are over unbounded `Int`). The `$` cannot begin a name the generator mints
/// for a MIR place, so a placeholder never collides with a program variable.
#[must_use]
pub fn field_var(t: FieldTerm) -> Formula {
    match t {
        FieldTerm::Value(i) => Formula::var_owned(format!("{VALUE_PREFIX}{i}"), Sort::Int),
        FieldTerm::Len(i) => Formula::var_owned(format!("{LEN_PREFIX}{i}"), Sort::Int),
    }
}

/// The [`FieldTerm`] a variable is the placeholder of: exactly the formula [`field_var`]
/// builds, so a sort other than `Int`, a leading zero or any other spelling is not one.
fn as_field_var(f: &Formula) -> Option<FieldTerm> {
    let Formula::Var(name, Sort::Int) = f else { return None };
    let parse_canonical_usize = |digits: &str| -> Option<usize> {
        if digits.is_empty()
            || !digits.bytes().all(|b| b.is_ascii_digit())
            || (digits.len() > 1 && digits.starts_with('0'))
        {
            return None;
        }
        digits.parse().ok()
    };
    if let Some(i) = name.strip_prefix(VALUE_PREFIX) {
        Some(FieldTerm::Value(parse_canonical_usize(i)?))
    } else {
        Some(FieldTerm::Len(parse_canonical_usize(name.strip_prefix(LEN_PREFIX)?)?))
    }
}

/// One candidate conjunct of a type's invariant: an Int-sorted predicate whose only free
/// variables are [`field_var`]s (G16). `id` is stable across Houdini rounds and is what a
/// use site cites (`assumes type_invariant(S)#id`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CandidateConjunct {
    pub id: u32,
    pub formula: Formula,
}

/// A candidate type and its candidate conjuncts.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TinvType {
    /// Crate-qualified; equals the extractor's `Ty::Adt` name and `AggregateKind::Adt`
    /// name for the type (the step-0(a) fixture shows `a::S` for both).
    pub def_path: String,
    /// The fields in declaration order (MIR field index order).
    pub fields: Vec<(String, Ty)>,
    pub conjuncts: Vec<CandidateConjunct>,
}

/// The rendered term of every field at one point, indexed by field. `None` means the
/// generator has no term for it, and [`instantiate`] refuses any conjunct that reads it.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Sigma {
    pub value: Vec<Option<Formula>>,
    pub len: Vec<Option<Formula>>,
}

/// Whether a rendered term is Int-sorted by its own shape. Deliberately narrow: an
/// Int-sorted variable or an integer literal. Anything else (a `UInt` literal, a
/// compound term, a bit-vector) is not admitted, so no sort is ever guessed.
fn is_int_term(f: &Formula) -> bool {
    matches!(f, Formula::Var(_, Sort::Int) | Formula::SymVar(_, Sort::Int) | Formula::Int(_))
}

/// Whether a node is in the language the instantiation admits.
///
/// The admitted language is the G16 template language: Boolean connectives, integer
/// comparisons and `+ - *` with negation, `ite`, and literals. Binders (`Forall`,
/// `Exists`), division, bit-vector, float, array and predicate nodes are refused rather
/// than walked, so "a free variable that is not a placeholder" can never hide under a
/// binder or behind an unexamined node.
fn is_admitted_node(f: &Formula) -> bool {
    matches!(
        f,
        Formula::Bool(_)
            | Formula::Int(_)
            | Formula::Var(..)
            | Formula::Not(_)
            | Formula::Neg(_)
            | Formula::And(_)
            | Formula::Or(_)
            | Formula::Implies(..)
            | Formula::Eq(..)
            | Formula::Lt(..)
            | Formula::Le(..)
            | Formula::Gt(..)
            | Formula::Ge(..)
            | Formula::Add(..)
            | Formula::Sub(..)
            | Formula::Mul(..)
            | Formula::Ite(..)
    )
}

/// Rebuild an admitted node by popping its `kid_count` instantiated children off `done`
/// (pushed left to right, so the rightmost child is on top of `done`).
fn rebuild_from_stack(f: &Formula, done: &mut Vec<Formula>, kid_count: usize) -> Option<Formula> {
    match f {
        Formula::And(_) => {
            let at = done.len().checked_sub(kid_count)?;
            return Some(Formula::And(done.split_off(at)));
        }
        Formula::Or(_) => {
            let at = done.len().checked_sub(kid_count)?;
            return Some(Formula::Or(done.split_off(at)));
        }
        _ => {}
    }
    if done.len() < kid_count {
        return None;
    }
    Some(match f {
        Formula::Not(_) if kid_count == 1 => Formula::Not(Box::new(done.pop()?)),
        Formula::Neg(_) if kid_count == 1 => Formula::Neg(Box::new(done.pop()?)),
        Formula::Implies(..) if kid_count == 2 => {
            let b = Box::new(done.pop()?);
            let a = Box::new(done.pop()?);
            Formula::Implies(a, b)
        }
        Formula::Eq(..) if kid_count == 2 => {
            let b = Box::new(done.pop()?);
            let a = Box::new(done.pop()?);
            Formula::Eq(a, b)
        }
        Formula::Lt(..) if kid_count == 2 => {
            let b = Box::new(done.pop()?);
            let a = Box::new(done.pop()?);
            Formula::Lt(a, b)
        }
        Formula::Le(..) if kid_count == 2 => {
            let b = Box::new(done.pop()?);
            let a = Box::new(done.pop()?);
            Formula::Le(a, b)
        }
        Formula::Gt(..) if kid_count == 2 => {
            let b = Box::new(done.pop()?);
            let a = Box::new(done.pop()?);
            Formula::Gt(a, b)
        }
        Formula::Ge(..) if kid_count == 2 => {
            let b = Box::new(done.pop()?);
            let a = Box::new(done.pop()?);
            Formula::Ge(a, b)
        }
        Formula::Add(..) if kid_count == 2 => {
            let b = Box::new(done.pop()?);
            let a = Box::new(done.pop()?);
            Formula::Add(a, b)
        }
        Formula::Sub(..) if kid_count == 2 => {
            let b = Box::new(done.pop()?);
            let a = Box::new(done.pop()?);
            Formula::Sub(a, b)
        }
        Formula::Mul(..) if kid_count == 2 => {
            let b = Box::new(done.pop()?);
            let a = Box::new(done.pop()?);
            Formula::Mul(a, b)
        }
        Formula::Ite(..) if kid_count == 3 => {
            let e = Box::new(done.pop()?);
            let t = Box::new(done.pop()?);
            let c = Box::new(done.pop()?);
            Formula::Ite(c, t, e)
        }
        _ => return None,
    })
}

fn push_admitted_children<'a>(
    f: &'a Formula,
    work: &mut Vec<(&'a Formula, Option<usize>)>,
) -> Option<usize> {
    Some(match f {
        Formula::Bool(_) | Formula::Int(_) | Formula::Var(..) => 0,
        Formula::Not(a) | Formula::Neg(a) => {
            work.push((f, Some(1)));
            work.push((a.as_ref(), None));
            1
        }
        Formula::And(xs) | Formula::Or(xs) => {
            if !xs.is_empty() {
                work.push((f, Some(xs.len())));
                work.extend(xs.iter().rev().map(|k| (k, None)));
            }
            xs.len()
        }
        Formula::Implies(a, b)
        | Formula::Eq(a, b)
        | Formula::Lt(a, b)
        | Formula::Le(a, b)
        | Formula::Gt(a, b)
        | Formula::Ge(a, b)
        | Formula::Add(a, b)
        | Formula::Sub(a, b)
        | Formula::Mul(a, b) => {
            work.push((f, Some(2)));
            work.push((b.as_ref(), None));
            work.push((a.as_ref(), None));
            2
        }
        Formula::Ite(c, t, e) => {
            work.push((f, Some(3)));
            work.push((e.as_ref(), None));
            work.push((t.as_ref(), None));
            work.push((c.as_ref(), None));
            3
        }
        _ => return None,
    })
}

#[cfg(test)]
fn admitted_children(f: &Formula) -> Option<Vec<&Formula>> {
    let mut work = Vec::new();
    let count = push_admitted_children(f, &mut work)?;
    if count == 0 {
        return Some(Vec::new());
    }
    Some(work.into_iter().skip(1).rev().map(|(kid, _)| kid).collect())
}

/// `c.formula` with every placeholder replaced by its [`Sigma`] term.
///
/// Refuses (`None`) on:
/// * any free variable that is not a [`field_var`] (including a `SymVar`, which is never
///   a placeholder spelling, and a placeholder spelled with a sort other than `Int`);
/// * a placeholder whose term is missing (`None`, or a field index past `sigma`);
/// * a sort mismatch: the term is not Int-sorted by its own shape ([`is_int_term`]);
/// * any node outside the admitted template language ([`is_admitted_node`]).
///
/// The walk is iterative (an explicit stack), so a deep conjunct cannot overflow the
/// stack.
#[must_use]
pub fn instantiate(c: &CandidateConjunct, sigma: &Sigma) -> Option<Formula> {
    // (node, child count once children have been pushed)
    let mut work: Vec<(&Formula, Option<usize>)> = vec![(&c.formula, None)];
    let mut done: Vec<Formula> = Vec::new();
    while let Some((f, expanded_count)) = work.pop() {
        if let Some(kid_count) = expanded_count {
            let rebuilt = rebuild_from_stack(f, &mut done, kid_count)?;
            done.push(rebuilt);
            continue;
        }
        if let Formula::Var(..) = f {
            let term = match as_field_var(f)? {
                FieldTerm::Value(i) => sigma.value.get(i)?.as_ref()?,
                FieldTerm::Len(i) => sigma.len.get(i)?.as_ref()?,
            };
            if !is_int_term(term) {
                return None;
            }
            done.push(term.clone());
            continue;
        }
        if push_admitted_children(f, &mut work)? == 0 {
            done.push(f.clone());
        }
    }
    let out = done.pop()?;
    done.is_empty().then_some(out)
}
