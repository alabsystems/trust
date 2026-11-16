//! TINV step 7, increment 7.6: the Houdini fixpoint and the certify mint loop
//! (`docs/design/2026-10-04-type-invariant-tinv.md` §2 "Houdini fixpoint", P5, P7;
//! TINV-2, TINV-8(e)).
//!
//! [`houdini`] takes every candidate type with its UNTRUSTED conjuncts and every body of
//! the run, and returns, per type, either a [`TypeInvariantCertificate`] (every row of
//! every surviving conjunct was certified), or nothing: the type's conjuncts are all in
//! [`TinvOutcome::dropped`], or the type is in [`TinvOutcome::refused`].
//!
//! THE LOOP.
//! 0. TINV-21: the `Some`-arm lemmas of the inventory getters are minted once
//!    ([`super::arm_lemma`]), each admitted by [`judge`] and `certify` on its own probe
//!    row; every round's rows may assume them at a caller, sealed and region-gated.
//! 1. The inputs are checked: the inventory (the callees whose post-call facts and U
//!    discharges the rows may use) is DERIVED from the bodies' identities, so no callee
//!    can be assumed whose own obligations are not checked here. A body with no
//!    identity (`TinvBody::identity` is `None`) is checked but is not in the inventory.
//!    A duplicate `Some` body identity, body `def_path`, type `def_path` or conjunct id
//!    refuses EVERY type (the `inferred_return` precedent).
//! 2. Each round walks every body once ([`type_invariant_check_vcs`]) for every
//!    (type, alive conjunct). A conjunct is dropped by any of its rows that is
//!    unsituated ([`VerificationCondition::type_invariant_situatedness_refusal`]),
//!    refuted or unknown to the oracle, vacuous (below) or uninstantiable. A type whose
//!    enumeration or walk refuses in any body is refused. The round is completed, the
//!    drops are applied together, and the next round starts: the alive set only shrinks,
//!    so the loop ends.
//! 3. At a round with no drop, a type with no Establish row is refused (no construction
//!    of it was checked), and every row of every surviving conjunct is passed to
//!    `certify`. A `None` drops the conjunct as [`DropCause::NotCertified`] and the loop
//!    returns to step 2, because the other rows assumed it.
//! 4. Only when a whole mint pass certifies every row are the certificates built, from
//!    that pass's rows: each row was generated under exactly the final alive set, which
//!    is the whole-crate induction the entry and post-call assumptions rely on.
//!
//! EDGE PARTS (TINV-9(a)). An R point at a join arrives as one row per predecessor edge
//! (`TinvRowKey::edge`). The parts are aggregated with AND by construction: each part is
//! an ordinary row, so any part that is unsituated, refuted, unknown, vacuous or not
//! certified drops the conjunct, and a point is discharged only when every part is. A
//! point whose part set is not exactly its block's predecessor set (re-derived here from
//! the body, independently of the split), or that mixes a whole row with parts, refuses
//! the type ([`incomplete_join_parts`]).
//!
//! THE VACUITY PROBE (fail-closed). The situatedness gate is structural and cannot tell
//! a true hypothesis from an unsatisfiable one, and a TINV certificate becomes an
//! assumption crate-wide, so a vacuous row is worse here than anywhere else. For every
//! row the oracle proves, the oracle is asked about the row's HYPOTHESES ALONE: the
//! record's body with its negated core replaced by `true`, replayed through the record's
//! own wrappers ([`hypotheses_only`]), and must answer with a satisfying MODEL
//! ([`TinvOracle::model`]). The row is kept only if that model is CHECKED here: the
//! total ground evaluator [`ground_eval`] evaluates the probe formula under it to `true`.
//! No model, a model that misses a variable or binds it at the wrong sort, a node outside
//! the evaluator's fragment, or an evaluation to `false` drops the conjunct as
//! [`DropCause::Vacuous`]; a bare "satisfiable" from the untrusted oracle never keeps a
//! row (2026-10-05, review of step 7.7: before this a wrong SAT answer let a vacuous row
//! reach the kernel mint). Step 9 MUST keep this contract: vacuity requires a checked
//! model (`docs/DECISION_QUEUE.md`, TINV). This also drops a conjunct at a point the path
//! condition makes dead, and one whose hypotheses leave the fragment: precision only.
//!
//! AUTHORITY. The oracle is a FILTER: it never makes a row publishable. Only `certify`
//! does, and the caller's `certify` must apply the kernel gate
//! ([`VerificationCondition::kernel_authority_refusal`]) and return `None` for a refused
//! row. Step 9 passes `trust_certify::certify_vc` restricted to Clean-CIC evidence; since
//! step 7.7 admitted the kind, that mints for a situated row the kernel can refute
//! (`certify_tests.rs` runs it end to end).
//!
//! PUBLICATION (TINV-8(e)). A dropped conjunct is a [`DroppedConjunct`] and a
//! [`TinvNote`], never a row: [`PublishedTinvRow`] has no public constructor, and only
//! the final pass's rows of surviving conjuncts become one.
//!
//! DETERMINISM. Types are walked sorted by `def_path`, conjuncts by id, bodies by
//! `def_path`, rows by [`TinvRowKey`] in body order; the budget counts walks and steps,
//! never time. A walk budget exhausted refuses every type that is not already refused:
//! no partial certificate is ever returned.

use std::collections::{BTreeMap, BTreeSet, HashSet};

use trust_types::{
    BlockId, CalleeIdentity, Formula, ObligationRecord, Ty, TypeInvariantPoint, TypeInvariantSite,
    VerifiableFunction, VerificationCondition,
};

#[cfg(test)]
use super::arm_lemma::mint_arm_lemmas;
use super::arm_lemma::{
    ArmLemma, ArmLemmas, LEMMA_CONJUNCT_BASE, LemmaEnv, formula_contains, is_instance_of,
    mint_arm_lemmas_with_prepared, strip_versions,
};
use super::obligations::{
    BodyTinvPlan, PreparedBody, TinvObligationRefusal, TinvRowKey,
    type_invariant_check_vcs_with_lemmas_prepared,
};
use super::unwind::ExactCallModels;
use super::{CandidateConjunct, TinvBodyFacts, TinvType};
use crate::generate::tinv_rows::RowArmUse;

/// The decision procedure Houdini filters with. A FILTER ONLY: no answer of it grants
/// authority (that is `certify`'s).
pub trait TinvOracle {
    /// Whether the violation formula of `vc` is unsatisfiable: `Some(true)` = the
    /// property holds, `Some(false)` = a counterexample exists, `None` = unknown.
    ///
    /// Asked of rows only. The vacuity probe ([`hypotheses_only`]: a VC of the same
    /// kind whose formula is the row's hypotheses alone and which carries NO obligation
    /// record, so it is never a row) is asked for a [`Self::model`] instead.
    fn proves(&self, vc: &VerificationCondition) -> Option<bool>;

    /// A satisfying assignment of the violation formula of `vc`, if the oracle has one:
    /// asked of the vacuity probe ([`hypotheses_only`]) only. UNTRUSTED like every other
    /// answer: [`judge`] keeps a row only when [`ground_eval`] confirms the probe formula
    /// evaluates to `true` under it, so a wrong model drops the conjunct and can never keep
    /// it. Return `None` when there is no model (unsat, unknown, or a value outside
    /// [`TinvModelValue`]).
    fn model(&self, vc: &VerificationCondition) -> Option<TinvModel>;
}

/// One value of a [`TinvModel`]: the sorts the ground evaluator reads.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TinvModelValue {
    /// The value of an `Int`-sorted variable.
    Int(i128),
    /// The value of a `Bool`-sorted variable.
    Bool(bool),
}

/// A model of a vacuity probe: variable name (the formula's own spelling) to value.
pub type TinvModel = BTreeMap<String, TinvModelValue>;

/// Recursion bound for [`ground_eval`]; a deeper formula is not confirmed.
const GROUND_EVAL_DEPTH: usize = 512;

/// The TOTAL ground evaluation of `f` under `model`: `Some(b)` only when every node of
/// `f` is in the fragment and evaluates. The fragment is what TINV probe formulas use:
/// `Bool`/`Int` constants; `Var`/`SymVar` of sort `Int` or `Bool` bound in `model` at
/// that sort; `Not`, `And`, `Or`, `Implies`, `Ite`; `Eq` on two ints or two bools;
/// `Lt`/`Le`/`Gt`/`Ge`; `Add`/`Sub`/`Mul`/`Neg` over unbounded `Int`, computed with
/// checked `i128`. Anything else — an unbound or ill-sorted variable, an `i128`
/// overflow, `Div`/`Rem`, bit-vectors, arrays, quantifiers, any other node, or depth past
/// [`GROUND_EVAL_DEPTH`] — is `None`. Connectives evaluate EVERY child (no short
/// circuit), so `Some` means the whole formula was understood.
#[must_use]
pub fn ground_eval(f: &Formula, model: &TinvModel) -> Option<bool> {
    match ground_eval_at(f, model, 0)? {
        Ground::B(b) => Some(b),
        Ground::I(_) => None,
    }
}

#[derive(Clone, Copy)]
enum Ground {
    I(i128),
    B(bool),
}

fn ground_eval_at(f: &Formula, m: &TinvModel, depth: usize) -> Option<Ground> {
    use trust_types::Sort;
    if depth > GROUND_EVAL_DEPTH {
        return None;
    }
    let d = depth + 1;
    let int = |x: &Formula| match ground_eval_at(x, m, d)? {
        Ground::I(i) => Some(i),
        Ground::B(_) => None,
    };
    let boolean = |x: &Formula| match ground_eval_at(x, m, d)? {
        Ground::B(b) => Some(b),
        Ground::I(_) => None,
    };
    let var = |name: &str, sort: &Sort| match (sort, m.get(name)?) {
        (Sort::Int, TinvModelValue::Int(i)) => Some(Ground::I(*i)),
        (Sort::Bool, TinvModelValue::Bool(b)) => Some(Ground::B(*b)),
        _ => None,
    };
    Some(match f {
        Formula::Bool(b) => Ground::B(*b),
        Formula::Int(i) => Ground::I(*i),
        Formula::Var(name, sort) => var(name, sort)?,
        Formula::SymVar(sym, sort) => var(sym.as_str(), sort)?,
        Formula::Not(a) => Ground::B(!boolean(a)?),
        Formula::And(kids) | Formula::Or(kids) => {
            let mut all_true = true;
            let mut any_true = false;
            for k in kids {
                let b = boolean(k)?;
                all_true &= b;
                any_true |= b;
            }
            Ground::B(if matches!(f, Formula::And(_)) { all_true } else { any_true })
        }
        Formula::Implies(a, b) => {
            let (a, b) = (boolean(a)?, boolean(b)?);
            Ground::B(!a || b)
        }
        Formula::Eq(a, b) => match (ground_eval_at(a, m, d)?, ground_eval_at(b, m, d)?) {
            (Ground::I(x), Ground::I(y)) => Ground::B(x == y),
            (Ground::B(x), Ground::B(y)) => Ground::B(x == y),
            _ => return None,
        },
        Formula::Lt(a, b) => Ground::B(int(a)? < int(b)?),
        Formula::Le(a, b) => Ground::B(int(a)? <= int(b)?),
        Formula::Gt(a, b) => Ground::B(int(a)? > int(b)?),
        Formula::Ge(a, b) => Ground::B(int(a)? >= int(b)?),
        Formula::Add(a, b) => Ground::I(int(a)?.checked_add(int(b)?)?),
        Formula::Sub(a, b) => Ground::I(int(a)?.checked_sub(int(b)?)?),
        Formula::Mul(a, b) => Ground::I(int(a)?.checked_mul(int(b)?)?),
        Formula::Neg(a) => Ground::I(int(a)?.checked_neg()?),
        Formula::Ite(c, t, e) => {
            // Both arms must evaluate (totality), at one sort.
            let (c, t, e) = (boolean(c)?, ground_eval_at(t, m, d)?, ground_eval_at(e, m, d)?);
            match (t, e) {
                (Ground::I(_), Ground::I(_)) | (Ground::B(_), Ground::B(_)) => {
                    if c {
                        t
                    } else {
                        e
                    }
                }
                _ => return None,
            }
        }
        _ => return None,
    })
}

/// One body of the run.
#[derive(Clone, Copy)]
pub struct TinvBody<'a> {
    /// The body's `CalleeIdentity`, as a `Terminator::Call` naming it carries it.
    ///
    /// `None`: no `Terminator::Call` can name this body with an identity the extractor
    /// stamps (a promoted, const, static, closure, coroutine, generic, Clean-origin or
    /// interposable body). Its rows are generated and checked like any other body's,
    /// but it is not in the inventory: a call to it never kills a window, gives a
    /// post-call fact or discharges a U row. Such a call havocs, which is fail-closed.
    pub identity: Option<CalleeIdentity>,
    pub func: &'a VerifiableFunction,
    pub facts: Option<&'a TinvBodyFacts>,
}

/// Why a conjunct was dropped.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum DropCause {
    /// The oracle found a counterexample to a row.
    Refuted,
    /// The oracle could not decide a row.
    Unknown,
    /// `certify` returned no evidence for a row.
    NotCertified,
    /// A row's hypotheses alone are not shown satisfiable by a model the ground evaluator
    /// checked: unsatisfiable, unknown, no model, or a model that fails the check.
    Vacuous,
    /// A row failed the structural situatedness gate.
    Situatedness,
    /// The conjunct reads a field term the generator has none for at a point.
    Uninstantiable,
}

/// A conjunct Houdini dropped, with the first row (in the deterministic order) that
/// dropped it. A NOTE, never a row.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DroppedConjunct {
    pub ty: String,
    pub conjunct: u32,
    /// The `def_path` of the body holding the row.
    pub function: String,
    pub point: TypeInvariantPoint,
    pub site: TypeInvariantSite,
    /// The edge part (TINV-9(a)) whose row dropped it, if the point was split.
    pub edge: Option<usize>,
    pub cause: DropCause,
    /// The round (from 1) whose rows dropped it; a mint pass counts as its round.
    pub round: u32,
}

/// A v7/D3 note (design P7) about a type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TinvNote {
    pub ty: String,
    pub text: String,
}

/// A certified row of a certificate. Only [`houdini`] constructs one, from the final
/// pass's rows of surviving conjuncts (TINV-8(e)).
#[derive(Debug, Clone)]
pub struct PublishedTinvRow<E> {
    key: TinvRowKey,
    function: String,
    vc: VerificationCondition,
    evidence: E,
    /// TINV-21: the arm facts this row ASSUMED (the lemma each instantiates and the
    /// sealed hypothesis the row's VC carries for it).
    lemma_uses: Vec<RowArmUse>,
}

impl<E> PublishedTinvRow<E> {
    #[must_use]
    pub fn key(&self) -> &TinvRowKey {
        &self.key
    }

    /// The `def_path` of the body the row is owed in.
    #[must_use]
    pub fn function(&self) -> &str {
        &self.function
    }

    #[must_use]
    pub fn vc(&self) -> &VerificationCondition {
        &self.vc
    }

    /// The row's evidence. It proves the row UNDER every hypothesis its VC carries,
    /// including the arm facts of [`Self::lemma_uses`]; it does not re-check those lemmas.
    #[must_use]
    pub fn evidence(&self) -> &E {
        &self.evidence
    }

    /// TINV-21: the arm facts the row assumed.
    #[must_use]
    pub fn lemma_uses(&self) -> &[RowArmUse] {
        &self.lemma_uses
    }
}

/// TINV-21: a kernel-certified `Some`-arm lemma a certificate's rows depend on, with the
/// `A`-part VC it was admitted on and the evidence `certify` returned for it
/// (`arm_lemma` module doc, EVIDENCE). Only [`houdini`] constructs one.
#[derive(Debug, Clone)]
pub struct PublishedArmLemma<E> {
    lemma: ArmLemma,
    vc: VerificationCondition,
    evidence: E,
}

impl<E> PublishedArmLemma<E> {
    /// The lemma (callee identity, getter, type, parameter, `φ`).
    #[must_use]
    pub fn lemma(&self) -> &ArmLemma {
        &self.lemma
    }

    /// The probe's `A` edge part the lemma was admitted on.
    #[must_use]
    pub fn vc(&self) -> &VerificationCondition {
        &self.vc
    }

    #[must_use]
    pub fn evidence(&self) -> &E {
        &self.evidence
    }

    /// The lemma's own shape, checked without the kernel: its VC is the `A` edge part of a
    /// lemma probe row of `lemma.ty` at `Return` (`VcKind::TypeInvariant`, conjunct id at
    /// or above `LEMMA_CONJUNCT_BASE`, `edge: Some(_)`) of the getter `lemma.function`, and
    /// its formula refutes `¬core` where `core` is `φ` instantiated at the callee's root.
    #[must_use]
    pub fn well_formed(&self) -> bool {
        let trust_types::VcKind::TypeInvariant { ty, point, conjunct, edge, .. } = &self.vc.kind
        else {
            return false;
        };
        let Some(core) = self.lemma.core() else { return false };
        let function = self.vc.function.as_str();
        ty == self.lemma.ty()
            && *point == TypeInvariantPoint::Return
            && *conjunct >= LEMMA_CONJUNCT_BASE
            && edge.is_some()
            && !function.is_empty()
            && (self.lemma.function() == function
                || self
                    .lemma
                    .function()
                    .strip_suffix(function)
                    .is_some_and(|prefix| prefix.ends_with("::")))
            && is_instance_of(self.lemma.phi(), core)
            && formula_contains(
                &strip_versions(&self.vc.formula),
                &Formula::Not(Box::new(core.clone())),
            )
    }
}

/// The surviving conjuncts of one type and the certified rows that establish them.
/// Read-only outside this module: a consumer cannot add a conjunct no row proved.
#[derive(Debug, Clone)]
pub struct TypeInvariantCertificate<E> {
    def_path: String,
    /// The type's fields in declaration order, captured from the [`TinvType`] the rows
    /// were generated for (step 10.0): a use site instantiates the conjuncts over exactly
    /// these field indices, never over a field list it re-derives.
    fields: Vec<(String, Ty)>,
    conjuncts: Vec<CandidateConjunct>,
    rows: Vec<PublishedTinvRow<E>>,
    /// TINV-21: every arm lemma a row here ASSUMED (`PublishedTinvRow::lemma_uses`),
    /// each with its own evidence. A row's evidence
    /// proves it UNDER these lemmas; [`Self::replay`] re-checks both.
    lemmas: Vec<PublishedArmLemma<E>>,
}

impl<E> TypeInvariantCertificate<E> {
    #[must_use]
    pub fn def_path(&self) -> &str {
        &self.def_path
    }

    /// The type's fields in declaration order (MIR field index order), as the rows were
    /// generated for them.
    #[must_use]
    pub fn fields(&self) -> &[(String, Ty)] {
        &self.fields
    }

    /// The number of fields, `fields().len()`.
    #[must_use]
    pub fn field_count(&self) -> usize {
        self.fields.len()
    }

    /// The surviving conjuncts, sorted by id (the id a use site cites).
    #[must_use]
    pub fn conjuncts(&self) -> &[CandidateConjunct] {
        &self.conjuncts
    }

    /// Every row of every surviving conjunct, each with its evidence.
    ///
    /// A row's evidence is valid only UNDER [`Self::lemmas`]: a row that assumed an arm
    /// fact ([`PublishedTinvRow::lemma_uses`]) is proved given that lemma, and the lemma
    /// is re-checked only by its own evidence. Re-check a certificate with
    /// [`Self::replay`], never by replaying these rows alone.
    #[must_use]
    pub fn rows(&self) -> &[PublishedTinvRow<E>] {
        &self.rows
    }

    /// TINV-21: the arm lemmas the rows depend on, each with its evidence.
    #[must_use]
    pub fn lemmas(&self) -> &[PublishedArmLemma<E>] {
        &self.lemmas
    }

    /// Re-check the certificate with `replay` (the compiler passes
    /// `trust_certify::replay_vc_evidence`): true exactly when EVERY row AND every lemma
    /// a row depends on replays. A replay of the rows alone does not re-check the lemmas
    /// their hypotheses carry.
    ///
    /// Beyond the kernel replays it TIES each carried lemma to what the rows assumed: every
    /// carried lemma is [`PublishedArmLemma::well_formed`]; and for every arm fact a row
    /// assumed, (a) a carried lemma is EXACTLY the one it names (callee identity, type,
    /// parameter, `φ`), and (b) the use's fact is `φ` instantiated (same shape, field
    /// placeholders replaced consistently), the row's sealed hypothesis is that fact up
    /// to version tokens, and the row's VC formula carries that hypothesis.
    pub fn replay(&self, replay: &dyn Fn(&VerificationCondition, &E) -> bool) -> bool {
        let lemmas_ok = self.lemmas.iter().all(|l| {
            l.lemma.ty() == self.def_path && l.well_formed() && replay(&l.vc, &l.evidence)
        });
        lemmas_ok
            && self.rows.iter().all(|r| {
                replay(&r.vc, &r.evidence)
                    && r.lemma_uses.iter().all(|u| {
                        u.lemma.dep.ty == self.def_path
                            && is_instance_of(&u.lemma.phi, &u.lemma.fact)
                            && strip_versions(&u.sealed) == u.lemma.fact
                            && formula_contains(&r.vc.formula, &u.sealed)
                            && self.lemmas.iter().any(|l| u.lemma.names(&l.lemma))
                    })
            })
    }

    /// One line for the `certified` note: how many arm lemmas the certificate carries and
    /// which getters and parameters they are about.
    #[must_use]
    pub fn lemma_summary(&self) -> String {
        if self.lemmas.is_empty() {
            return "0 arm lemma(s)".into();
        }
        let mut deps: Vec<String> = Vec::new();
        for l in &self.lemmas {
            let d = format!("`{}` param _{}", l.lemma.function(), l.lemma.param());
            if !deps.contains(&d) {
                deps.push(d);
            }
        }
        format!("{} arm lemma(s) carried, of {}", self.lemmas.len(), deps.join(", "))
    }
}

/// A certificate with no rows, for the use-set and use-site tests only: production
/// certificates come from [`houdini`] alone.
#[cfg(test)]
impl<E> TypeInvariantCertificate<E> {
    pub(crate) fn for_test(ty: &TinvType) -> Self {
        Self {
            def_path: ty.def_path.clone(),
            fields: ty.fields.clone(),
            conjuncts: ty.conjuncts.clone(),
            rows: Vec::new(),
            lemmas: Vec::new(),
        }
    }
}

/// What a run established. `dropped`, `refused` and `notes` are notes only; nothing in
/// them is a VC.
#[derive(Debug, Clone)]
pub struct TinvOutcome<E> {
    pub certificates: BTreeMap<String, TypeInvariantCertificate<E>>,
    pub dropped: Vec<DroppedConjunct>,
    /// Sorted by type `def_path`, one entry per refused type.
    pub refused: Vec<(String, TinvObligationRefusal)>,
    pub notes: Vec<TinvNote>,
    /// The rounds run, mint passes included.
    pub rounds: u32,
    /// The callee identities the run's rows assumed (step 10.0): exactly the `Some`
    /// identities of the input bodies, the set every walk's kill, post-call fact and U
    /// discharge read. Empty when the inputs were refused before it was derived (a
    /// duplicate). A use site may assume `I` after a call only into this set.
    pub inventory: HashSet<CalleeIdentity>,
    /// The `def_path` of every body walked in the round whose rows the certificates were
    /// built from (step 10.0). The entry assumption is justified only inside the
    /// whole-crate induction those bodies form, so a use site gives no fact in a body
    /// outside this set. Empty when no certificate is returned.
    pub checked_bodies: BTreeSet<String>,
    /// TINV-21: the `Some`-arm lemmas minted before the fixpoint (each kernel-certified
    /// on its own probe row) that every round's rows could assume at a caller. Reported
    /// for audit; a use site never reads them (design §6 item 2).
    pub arm_lemmas: ArmLemmas,
}

impl<E> Default for TinvOutcome<E> {
    fn default() -> Self {
        Self {
            certificates: BTreeMap::new(),
            dropped: Vec::new(),
            refused: Vec::new(),
            notes: Vec::new(),
            rounds: 0,
            inventory: HashSet::new(),
            checked_bodies: BTreeSet::new(),
            arm_lemmas: ArmLemmas::default(),
        }
    }
}

/// Step budgets only, so the result is deterministic.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TinvBudget {
    /// Each walk's `VerifyBudgetGuard` step budget; a trip refuses the walk's types.
    pub steps_per_walk: u64,
    /// The walks (one per body per round) the whole run may take; past it, every type
    /// not already refused is refused as `Budget`.
    pub total_walks: u32,
}

/// The vacuity probe of a row: `vc` with its record body's negated core replaced by
/// `true`, replayed through the record's own wrappers, and with NO record (the probe is
/// never a row). `None` when the row has no record, its body is not `Not(core)` or
/// `And([h.., Not(core)])`, or the replay exceeds the record bounds.
#[must_use]
pub fn hypotheses_only(vc: &VerificationCondition) -> Option<VerificationCondition> {
    let record: &ObligationRecord = vc.obligation.as_ref()?;
    let body = match &record.body {
        Formula::Not(_) => Formula::Bool(true),
        Formula::And(parts) => match parts.split_last() {
            Some((Formula::Not(_), hyps)) => {
                let mut v = Vec::with_capacity(hyps.len() + 1);
                v.extend_from_slice(hyps);
                v.push(Formula::Bool(true));
                Formula::And(v)
            }
            _ => return None,
        },
        _ => return None,
    };
    let formula = ObligationRecord::reconstruct_parts(&body, &record.wrappers)?;
    Some(VerificationCondition {
        kind: vc.kind.clone(),
        function: vc.function,
        location: vc.location.clone(),
        formula,
        contract_metadata: None,
        obligation: None,
    })
}

/// One row of one round.
struct Row {
    function: String,
    key: TinvRowKey,
    vc: VerificationCondition,
    uses: Vec<RowArmUse>,
}

fn key_order(k: &TinvRowKey) -> (&str, u32, u8, usize, usize, u32, Option<usize>) {
    (
        k.ty.as_str(),
        k.conjunct,
        k.point.canonical_byte(),
        k.site.block,
        k.site.statement_index,
        k.ordinal,
        k.edge,
    )
}

/// The first duplicate among the inputs, as the refusal every type gets.
fn duplicate(types: &[&TinvType], bodies: &[TinvBody<'_>]) -> Option<TinvObligationRefusal> {
    let mut ids: trust_types::fx::FxHashSet<CalleeIdentity> =
        trust_types::fx::FxHashSet::with_capacity_and_hasher(bodies.len(), Default::default());
    let mut paths: trust_types::fx::FxHashSet<&str> =
        trust_types::fx::FxHashSet::with_capacity_and_hasher(bodies.len(), Default::default());
    for b in bodies {
        // Only a `Some` identity can name a body at a call, so only those must be unique.
        if let Some(id) = b.identity
            && !ids.insert(id)
        {
            return Some(TinvObligationRefusal::DuplicateIdentity(id));
        }
        if !paths.insert(b.func.def_path.as_str()) {
            return Some(TinvObligationRefusal::DuplicateDefPath(b.func.def_path.clone()));
        }
    }
    let mut tys: trust_types::fx::FxHashSet<&str> =
        trust_types::fx::FxHashSet::with_capacity_and_hasher(types.len(), Default::default());
    for t in types {
        if !tys.insert(t.def_path.as_str()) {
            return Some(TinvObligationRefusal::DuplicateDefPath(t.def_path.clone()));
        }
        let mut cids: trust_types::fx::FxHashSet<u32> =
            trust_types::fx::FxHashSet::with_capacity_and_hasher(
                t.conjuncts.len(),
                Default::default(),
            );
        for c in &t.conjuncts {
            if !cids.insert(c.id) {
                return Some(TinvObligationRefusal::DuplicateDefPath(format!(
                    "{}#{}",
                    t.def_path, c.id
                )));
            }
        }
    }
    None
}

/// The run's mutable state.
struct State<'t> {
    /// Every input type, sorted by `def_path`.
    types: Vec<&'t TinvType>,
    /// Alive conjunct ids per type.
    alive: BTreeMap<String, BTreeSet<u32>>,
    refused: BTreeMap<String, TinvObligationRefusal>,
    dropped: Vec<DroppedConjunct>,
    notes: Vec<TinvNote>,
    /// TINV-21: minted once, before the first round.
    arm_lemmas: ArmLemmas,
}

impl State<'_> {
    /// The types the next round checks: not refused, with at least one alive conjunct,
    /// conjuncts sorted by id.
    fn plan_types(&self) -> Vec<TinvType> {
        self.types
            .iter()
            .filter(|t| !self.refused.contains_key(&t.def_path))
            .filter_map(|t| {
                let alive = self.alive.get(&t.def_path)?;
                let mut conjuncts: Vec<CandidateConjunct> =
                    t.conjuncts.iter().filter(|c| alive.contains(&c.id)).cloned().collect();
                conjuncts.sort_by_key(|c| c.id);
                (!conjuncts.is_empty()).then(|| TinvType {
                    def_path: t.def_path.clone(),
                    fields: t.fields.clone(),
                    conjuncts,
                })
            })
            .collect()
    }

    fn refuse(&mut self, ty: &str, why: TinvObligationRefusal) {
        if self.refused.contains_key(ty) {
            return;
        }
        self.notes.push(TinvNote {
            ty: ty.to_owned(),
            text: format!("type invariant withheld: {why:?}"),
        });
        self.refused.insert(ty.to_owned(), why);
    }

    fn drop_conjunct(&mut self, d: DroppedConjunct) {
        let Some(alive) = self.alive.get_mut(&d.ty) else { return };
        if !alive.remove(&d.conjunct) {
            return;
        }
        self.notes.push(TinvNote {
            ty: d.ty.clone(),
            text: format!(
                "conjunct #{} dropped ({:?}) at {} {}{} in {} (round {})",
                d.conjunct,
                d.cause,
                d.point,
                d.site,
                d.edge.map(|p| format!(" via edge bb{p}")).unwrap_or_default(),
                d.function,
                d.round
            ),
        });
        if alive.is_empty() {
            self.notes.push(TinvNote {
                ty: d.ty.clone(),
                text: "no candidate conjunct survives: no type invariant".into(),
            });
        }
        self.dropped.push(d);
    }

    /// The outcome. `checked_bodies` must be empty unless `certificates` is not: a body
    /// set justifies nothing without a certificate, and a certificate without its body
    /// set could not be used.
    fn finish<E>(
        self,
        certificates: BTreeMap<String, TypeInvariantCertificate<E>>,
        rounds: u32,
        inventory: HashSet<CalleeIdentity>,
        checked_bodies: BTreeSet<String>,
    ) -> TinvOutcome<E> {
        let checked_bodies = if certificates.is_empty() { BTreeSet::new() } else { checked_bodies };
        TinvOutcome {
            certificates,
            dropped: self.dropped,
            refused: self.refused.into_iter().collect(),
            notes: self.notes,
            rounds,
            inventory,
            checked_bodies,
            arm_lemmas: self.arm_lemmas,
        }
    }
}

/// The pending drops of one round, first cause per conjunct in deterministic order.
#[derive(Default)]
struct RoundDrops {
    drops: BTreeMap<String, BTreeMap<u32, DroppedConjunct>>,
    refusals: BTreeMap<String, TinvObligationRefusal>,
}

impl RoundDrops {
    fn is_empty(&self) -> bool {
        self.drops.is_empty() && self.refusals.is_empty()
    }

    fn decided(&self, key: &TinvRowKey) -> bool {
        self.refusals.contains_key(&key.ty)
            || self.drops.get(&key.ty).is_some_and(|m| m.contains_key(&key.conjunct))
    }

    fn drop_row(&mut self, function: &str, key: &TinvRowKey, cause: DropCause, round: u32) {
        let make = || DroppedConjunct {
            ty: key.ty.clone(),
            conjunct: key.conjunct,
            function: function.to_owned(),
            point: key.point,
            site: key.site,
            edge: key.edge,
            cause,
            round,
        };
        if let Some(by_conjunct) = self.drops.get_mut(&key.ty) {
            by_conjunct.entry(key.conjunct).or_insert_with(make);
        } else {
            self.drops.entry(key.ty.clone()).or_default().insert(key.conjunct, make());
        }
    }

    fn refuse(&mut self, ty: &str, why: TinvObligationRefusal) {
        if !self.refusals.contains_key(ty) {
            self.refusals.insert(ty.to_owned(), why);
        }
    }

    fn apply(self, st: &mut State<'_>) {
        for (ty, why) in self.refusals {
            st.refuse(&ty, why);
        }
        for (_, by_conjunct) in self.drops {
            for (_, d) in by_conjunct {
                if !st.refused.contains_key(&d.ty) {
                    st.drop_conjunct(d);
                }
            }
        }
    }
}

/// Every type whose rows in one body do not cover each split point exactly (TINV-9(a)),
/// with the first reason found for it, in type order: per `(ty, conjunct, point, site,
/// ordinal)`, either ONE whole row (`edge: None`) or parts whose edges are exactly the
/// site block's predecessors (at least two), each once. The predecessors are re-derived
/// from `func`, independently of the split, so a split that left an entering edge out
/// cannot discharge the point. Empty when every point is covered. EVERY offending type
/// is reported, not only the first.
pub(crate) fn incomplete_join_parts<'k>(
    func: &VerifiableFunction,
    keys: impl IntoIterator<Item = &'k TinvRowKey>,
) -> Vec<(String, String)> {
    // PERF-COMPILER-VCGEN-708: fast-path empty or single whole-row (`edge: None`)
    // bodies without allocating the `BTreeMap` or per-point edge vectors.
    let mut keys = keys.into_iter().peekable();
    let Some(first) = keys.next() else {
        return Vec::new();
    };
    if keys.peek().is_none() && first.edge.is_none() {
        return Vec::new();
    }
    type Point<'a> = (&'a str, u32, u8, usize, usize, u32);
    let mut points: BTreeMap<Point<'k>, Vec<Option<usize>>> = BTreeMap::new();
    for k in std::iter::once(first).chain(keys) {
        points
            .entry((
                k.ty.as_str(),
                k.conjunct,
                k.point.canonical_byte(),
                k.site.block,
                k.site.statement_index,
                k.ordinal,
            ))
            .or_default()
            .push(k.edge);
    }
    let mut offending: BTreeMap<&'k str, String> = BTreeMap::new();
    let mut preds_cache: trust_types::fx::FxHashMap<usize, Vec<usize>> =
        trust_types::fx::FxHashMap::default();
    for ((ty, conjunct, _, block, stmt, ordinal), mut edges) in points {
        if offending.contains_key(ty) || edges.as_slice() == [None] {
            continue;
        }
        edges.sort_unstable();
        let what = if edges.iter().all(Option::is_none) {
            (edges.len() != 1).then_some("a point has more than one whole row")
        } else if edges.iter().any(Option::is_none) {
            Some("a point mixes a whole row with edge parts")
        } else {
            let preds = preds_cache
                .entry(block)
                .or_insert_with(|| crate::generate::tinv_rows::block_predecessors(func, BlockId(block)));
            (preds.len() < 2
                || edges.len() != preds.len()
                || !edges.iter().copied().eq(preds.iter().copied().map(Some)))
            .then_some("a split point's edge parts are not exactly its predecessors")
        };
        if let Some(what) = what {
            offending.insert(
                ty,
                format!(
                    "{what} at bb{block}[{stmt}] (conjunct {conjunct}, ordinal {ordinal}): {edges:?}"
                ),
            );
        }
    }
    offending.into_iter().map(|(ty, why)| (ty.to_owned(), why)).collect()
}

/// The oracle's verdict on one row: `None` keeps the conjunct. Shared with the TINV-21
/// lemma mint (`arm_lemma`), which admits a lemma only on the same verdict.
pub(crate) fn judge(vc: &VerificationCondition, oracle: &dyn TinvOracle) -> Option<DropCause> {
    if vc.type_invariant_situatedness_refusal().is_some() {
        return Some(DropCause::Situatedness);
    }
    match oracle.proves(vc) {
        Some(false) => return Some(DropCause::Refuted),
        None => return Some(DropCause::Unknown),
        Some(true) => {}
    }
    // Proved: the hypotheses alone must be SATISFIABLE, shown by a model the ground
    // evaluator CHECKS (module doc, "THE VACUITY PROBE"). No model, or a model that does
    // not evaluate the probe to `true`, drops the conjunct: the oracle's word is never
    // enough. Step 9 must keep this contract.
    let Some(probe) = hypotheses_only(vc) else { return Some(DropCause::Vacuous) };
    match oracle.model(&probe) {
        Some(model) if ground_eval(&probe.formula, &model) == Some(true) => None,
        _ => Some(DropCause::Vacuous),
    }
}

/// The Houdini fixpoint and the certify mint loop over `types` and `bodies` (module
/// doc). Generic over the evidence `certify` returns, so this crate takes no
/// dependency on its type.
///
/// `certify` MUST return `None` for a row the kernel gate refuses
/// ([`VerificationCondition::kernel_authority_refusal`]); this function applies the
/// structural situatedness half itself, every round.
pub fn houdini<E>(
    types: &[TinvType],
    bodies: &[TinvBody<'_>],
    models: &dyn ExactCallModels,
    may_run_user_drop: &dyn Fn(&Ty) -> bool,
    oracle: &dyn TinvOracle,
    certify: &dyn Fn(&VerificationCondition) -> Option<E>,
    budget: TinvBudget,
) -> TinvOutcome<E> {
    let mut sorted_types: Vec<&TinvType> = types.iter().collect();
    sorted_types.sort_by(|a, b| a.def_path.cmp(&b.def_path));
    let mut st = State {
        alive: sorted_types
            .iter()
            .map(|t| (t.def_path.clone(), t.conjuncts.iter().map(|c| c.id).collect()))
            .collect(),
        types: sorted_types,
        refused: BTreeMap::new(),
        dropped: Vec::new(),
        notes: Vec::new(),
        arm_lemmas: ArmLemmas::default(),
    };

    // Step 10.0 (circularity): the mint never runs where its own use-site facts are
    // visible. `tinv_use_facts` also gives nothing under an active row request; this is
    // the run-level backstop, checked at RUNTIME on the thread-local context.
    if crate::current_type_invariants().is_some() {
        let all: Vec<String> = st.types.iter().map(|t| t.def_path.clone()).collect();
        for ty in all {
            st.refuse(&ty, TinvObligationRefusal::UseSetVisible);
        }
        return st.finish(BTreeMap::new(), 0, HashSet::new(), BTreeSet::new());
    }
    if let Some(why) = duplicate(&st.types, bodies) {
        let all: Vec<String> = st.types.iter().map(|t| t.def_path.clone()).collect();
        for ty in all {
            st.refuse(&ty, why.clone());
        }
        return st.finish(BTreeMap::new(), 0, HashSet::new(), BTreeSet::new());
    }

    let mut bodies: Vec<TinvBody<'_>> = bodies.to_vec();
    bodies.sort_by(|a, b| a.func.def_path.cmp(&b.func.def_path));
    let inventory: HashSet<CalleeIdentity> = bodies.iter().filter_map(|b| b.identity).collect();

    let mut prepared_bodies: Vec<Option<PreparedBody<'_>>> =
        (0..bodies.len()).map(|_| None).collect();

    // TINV-21: the `Some`-arm lemmas, ONCE, before the fixpoint (`arm_lemma`). Each is an
    // unconditional fact about one body, certified by the same `certify` as the rows: it
    // assumes no conjunct, so it does not depend on the alive set, and a lemma that fails
    // to mint is not a conjunct drop. At most one walk per body, each under the walk step
    // budget; not charged to `total_walks`, which sizes the rounds.
    let env = LemmaEnv { inventory: &inventory, models, may_run_user_drop };
    let (lemmas, lemma_evidence, lemma_notes) =
        mint_arm_lemmas_with_prepared(
            &st.types,
            &bodies,
            &mut prepared_bodies,
            &env,
            oracle,
            certify,
            budget.steps_per_walk,
        );
    st.notes.extend(lemma_notes);
    st.arm_lemmas = lemmas;
    // Index-aligned with `st.arm_lemmas`; taken (moved) into the one certificate whose
    // type the lemma is about.
    let mut lemma_evidence: Vec<Option<E>> = lemma_evidence.into_iter().map(Some).collect();
    if lemma_evidence.len() != st.arm_lemmas.len() {
        let all: Vec<String> = st.types.iter().map(|t| t.def_path.clone()).collect();
        for ty in all {
            st.refuse(&ty, TinvObligationRefusal::Shim("arm lemma evidence misaligned".into()));
        }
        return st.finish(BTreeMap::new(), 0, inventory, BTreeSet::new());
    }

    let mut walks: u32 = 0;
    let mut round: u32 = 0;
    loop {
        let plan_types = st.plan_types();
        if plan_types.is_empty() {
            return st.finish(BTreeMap::new(), round, inventory, BTreeSet::new());
        }
        round += 1;

        // One walk per body, every (type, alive conjunct) at once.
        let mut pending = RoundDrops::default();
        let mut rows: Vec<Row> = Vec::new();
        let mut walked: BTreeSet<String> = BTreeSet::new();
        for (bi, body) in bodies.iter().enumerate() {
            if walks >= budget.total_walks {
                let all: Vec<String> = st.types.iter().map(|t| t.def_path.clone()).collect();
                for ty in all {
                    st.refuse(&ty, TinvObligationRefusal::Budget);
                }
                return st.finish(BTreeMap::new(), round, inventory, BTreeSet::new());
            }
            walks += 1;
            walked.insert(body.func.def_path.clone());
            let plan = BodyTinvPlan {
                types: &plan_types,
                facts: body.facts,
                inventory: &inventory,
                models,
                may_run_user_drop,
                step_budget: budget.steps_per_walk,
            };
            let function = body.func.def_path.as_str();
            let prep = prepared_bodies[bi]
                .get_or_insert_with(|| PreparedBody::new(body.func, body.facts, models));
            match type_invariant_check_vcs_with_lemmas_prepared(
                body.func,
                prep,
                &plan,
                &st.arm_lemmas,
            ) {
                // A walk-level refusal cannot be attributed to one type: it refuses
                // every type the walk carried.
                Err(why) => {
                    for t in &plan_types {
                        pending.refuse(&t.def_path, why.clone());
                    }
                }
                Ok(got) => {
                    let mut row_uses: trust_types::fx::FxHashMap<TinvRowKey, Vec<RowArmUse>> =
                        trust_types::fx::FxHashMap::with_capacity_and_hasher(
                            got.row_arm_uses.len(),
                            Default::default(),
                        );
                    for (k, u) in got.row_arm_uses {
                        row_uses.entry(k).or_insert(u);
                    }
                    for (ty, why) in got.refused {
                        pending.refuse(&ty, why);
                    }
                    let mut un = got.uninstantiable;
                    un.sort_by(|a, b| key_order(a).cmp(&key_order(b)));
                    for key in &un {
                        pending.drop_row(function, key, DropCause::Uninstantiable, round);
                    }
                    let planned = |k: &TinvRowKey| {
                        plan_types
                            .binary_search_by(|t| t.def_path.as_str().cmp(k.ty.as_str()))
                            .is_ok_and(|idx| {
                                plan_types[idx]
                                    .conjuncts
                                    .binary_search_by_key(&k.conjunct, |c| c.id)
                                    .is_ok()
                            })
                    };
                    if let Some((stray, _)) = got.rows.iter().find(|(k, _)| !planned(k)) {
                        let why = TinvObligationRefusal::Shim(format!(
                            "the walk returned a row the plan did not request: {stray:?}"
                        ));
                        for t in &plan_types {
                            pending.refuse(&t.def_path, why.clone());
                        }
                        continue;
                    }
                    for (ty, why) in
                        incomplete_join_parts(body.func, got.rows.iter().map(|(k, _)| k))
                    {
                        pending.refuse(&ty, TinvObligationRefusal::Shim(why));
                    }
                    let mut got_rows = got.rows;
                    got_rows.sort_by(|a, b| key_order(&a.0).cmp(&key_order(&b.0)));
                    rows.extend(got_rows.into_iter().map(|(key, vc)| {
                        let uses = row_uses.remove(&key).unwrap_or_default();
                        Row { function: function.to_owned(), key, vc, uses }
                    }));
                }
            }
        }

        // The oracle filter, rows in deterministic order; a conjunct already dropped
        // this round is not asked about again.
        //
        // TINV-21 (2026-10-06): a `Vacuous` verdict is DEFERRED while the round drops or
        // refuses anything else. A row's hypotheses are the alive conjuncts (entry and
        // post-call) plus, since TINV-21, arm-lemma facts; a FALSE alive conjunct can
        // make them inconsistent with a TRUE lemma (MEASURED on P1: the post-call
        // `i <= 0` and `len(b) == i * i` against `peek`'s `i < len(b)`), which would drop
        // a true conjunct together with the false ones that the same round refutes.
        // Deferring keeps it alive for the next round, whose rows are regenerated without
        // the dropped conjuncts and judged again. Sound: nothing is published until a
        // round in which EVERY row is kept (vacuity included), and a round whose only
        // drops are `Vacuous` applies them, so the alive set still shrinks every round
        // and the loop ends.
        let mut vacuous = RoundDrops::default();
        for row in &rows {
            // As before: a conjunct is judged up to its first failing row. One whose
            // first failing row is vacuous is re-judged in the next round if this round
            // drops anything else.
            if pending.decided(&row.key) || vacuous.decided(&row.key) {
                continue;
            }
            match judge(&row.vc, oracle) {
                Some(DropCause::Vacuous) => {
                    vacuous.drop_row(&row.function, &row.key, DropCause::Vacuous, round);
                }
                Some(cause) => pending.drop_row(&row.function, &row.key, cause, round),
                None => {}
            }
        }
        if !pending.is_empty() {
            pending.apply(&mut st);
            continue;
        }
        if !vacuous.is_empty() {
            vacuous.apply(&mut st);
            continue;
        }

        // A fixpoint of the filter. A type none of whose constructions was checked has
        // no E row: nothing established the invariant it would assume.
        let established_tys: trust_types::fx::FxHashSet<&str> = rows
            .iter()
            .filter(|r| r.key.point == TypeInvariantPoint::Establish)
            .map(|r| r.key.ty.as_str())
            .collect();
        for t in &plan_types {
            if !established_tys.contains(t.def_path.as_str()) {
                pending.refuse(&t.def_path, TinvObligationRefusal::NoEstablishPoint);
            }
        }
        if !pending.is_empty() {
            pending.apply(&mut st);
            continue;
        }

        // The mint pass: every row of every surviving conjunct must certify.
        round += 1;
        let mut evidence: Vec<Option<E>> = Vec::with_capacity(rows.len());
        for row in &rows {
            if pending.decided(&row.key) {
                evidence.push(None);
                continue;
            }
            let e = certify(&row.vc);
            if e.is_none() {
                pending.drop_row(&row.function, &row.key, DropCause::NotCertified, round);
            }
            evidence.push(e);
        }
        if !pending.is_empty() {
            pending.apply(&mut st);
            continue;
        }

        let mut certificates: BTreeMap<String, TypeInvariantCertificate<E>> = plan_types
            .iter()
            .map(|t| {
                (
                    t.def_path.clone(),
                    TypeInvariantCertificate {
                        def_path: t.def_path.clone(),
                        fields: t.fields.clone(),
                        conjuncts: t.conjuncts.clone(),
                        rows: Vec::new(),
                        lemmas: Vec::new(),
                    },
                )
            })
            .collect();
        for (row, e) in rows.into_iter().zip(evidence) {
            // Every evidence is Some here (the pass dropped nothing), and every row's
            // type is a planned type (checked at collection). Anything else withholds
            // the whole run rather than publish a certificate short of a row.
            let (Some(e), Some(cert)) = (e, certificates.get_mut(&row.key.ty)) else {
                let all: Vec<String> = st.types.iter().map(|t| t.def_path.clone()).collect();
                for ty in all {
                    st.refuse(
                        &ty,
                        TinvObligationRefusal::Shim("houdini lost a row's evidence".into()),
                    );
                }
                return st.finish(BTreeMap::new(), round, inventory, BTreeSet::new());
            };
            cert.rows.push(PublishedTinvRow {
                key: row.key,
                function: row.function,
                vc: row.vc,
                evidence: e,
                lemma_uses: row.uses,
            });
        }
        // TINV-21 (EVIDENCE): every lemma a published row ASSUMED travels with its type's
        // certificate, and the certificate must tie them together (`replay`'s structural
        // checks, run here without the kernel). Fail-closed: a use that names no minted
        // lemma, a lemma whose VC or evidence is missing, or a certificate whose rows and
        // lemmas do not tie, withholds the whole run rather than publish a certificate
        // whose rows assume a fact it cannot re-check.
        let mut lost: Option<String> = None;
        for cert in certificates.values_mut() {
            for r in &cert.rows {
                for u in &r.lemma_uses {
                    let Some((i, lemma)) =
                        st.arm_lemmas.iter().enumerate().find(|(_, l)| u.lemma.names(l))
                    else {
                        lost = Some(format!("{:?} names no minted lemma", u.lemma));
                        continue;
                    };
                    if cert.lemmas.iter().any(|l| u.lemma.names(&l.lemma)) {
                        continue;
                    }
                    match (lemma.vc(), lemma_evidence.get_mut(i).and_then(Option::take)) {
                        (Some(vc), Some(evidence)) => cert.lemmas.push(PublishedArmLemma {
                            lemma: lemma.clone(),
                            vc: vc.clone(),
                            evidence,
                        }),
                        _ => lost = Some(format!("{:?} has no VC or evidence", u.lemma)),
                    }
                }
            }
            if lost.is_none() && !cert.replay(&|_, _| true) {
                lost = Some(format!("`{}`: its rows and lemmas do not tie", cert.def_path));
            }
        }
        if let Some(what) = lost {
            let all: Vec<String> = st.types.iter().map(|t| t.def_path.clone()).collect();
            for ty in all {
                st.refuse(
                    &ty,
                    TinvObligationRefusal::Shim(format!(
                        "a row consumed an arm lemma the certificate cannot carry: {what}"
                    )),
                );
            }
            return st.finish(BTreeMap::new(), round, inventory, BTreeSet::new());
        }
        return st.finish(certificates, round, inventory, walked);
    }
}

#[cfg(test)]
#[path = "houdini_tests.rs"]
mod tests;
