//! The `Versioned<Formula>` type-gate (staleness-class S2c, item 2).
//!
//! The staleness class exists because a fact and a VC could be conjoined with raw
//! `Formula::And` while one referred to a stale place value. This module makes the
//! version boundary a TYPE: a `Fact` and a `Vc` are formulas tagged with the
//! program point at which their place variables were versioned, and they can only
//! be combined through [`conjoin`], which is the single place the version-aware
//! meet happens.
//!
//! Scope (honest): this makes the boundary EXPLICIT and gives the staleness path a
//! single typed chokepoint. FULL crate-wide bypass-prevention — making
//! `VerificationCondition.formula` private so a raw `Formula` can never reach a VC
//! except through `conjoin` — is a separate large change (477+ construction sites)
//! and is the documented follow-up; it is not required for the flip's soundness,
//! which rests on the version rename + the freshness theorem.

use trust_types::{BlockId, Formula};

/// A hypothesis (precondition / guard / block-def) whose place variables have been
/// versioned at its ESTABLISH point. Two facts established at the same versioned
/// point share variable names; a write between establish points renames them apart.
#[derive(Debug, Clone)]
pub(crate) struct Fact {
    formula: Formula,
    /// `None`: an ENTRY fact, its place names bare. `Some((block, point))`: a fact
    /// VERSIONED AND SEALED at that point ([`Fact::sealed_at`]).
    sealed: Option<(BlockId, usize)>,
}

/// A verification-condition body whose place variables have been versioned at its
/// program point (the point the obligation is evaluated).
#[derive(Debug, Clone)]
pub(crate) struct Vc {
    formula: Formula,
    /// The block the VC is evaluated at (diagnostic / future per-fact threading).
    #[allow(dead_code)]
    point: BlockId,
}

impl Fact {
    /// A fact carrying ENTRY/parameter values: its place names are unversioned
    /// (bare), so it unifies with a VC variable that has not been reassigned.
    pub(crate) fn entry(formula: Formula) -> Self {
        Fact { formula, sealed: None }
    }

    /// TINV step 10.2: a fact whose place names were versioned at `(block, point)` and
    /// SEALED there (`generate::seal_bare_reads`: a name left bare is spelled `#e` or
    /// `#pre_s{b}_{k}`), so it carries version tokens and is NOT an entry fact: the
    /// `Fact::entry` contract (bare = entry value) does not hold for it. A post-call
    /// type-invariant fact is one, sealed at its call's single-predecessor target `(T, 0)`
    /// by `generate::tinv_rows::tinv_sealed_post_call_hyps`; it may be conjoined only where
    /// that helper kept it (`(T, 0)` dominates the row, and the row's rename leaves it
    /// unchanged).
    pub(crate) fn sealed_at(formula: Formula, block: BlockId, point: usize) -> Self {
        Fact { formula, sealed: Some((block, point)) }
    }

    /// The fact's formula.
    pub(crate) fn formula(&self) -> &Formula {
        &self.formula
    }

    /// The point a sealed fact was versioned and sealed at; `None` for an entry fact.
    pub(crate) fn sealed_point(&self) -> Option<(BlockId, usize)> {
        self.sealed
    }
}

impl Vc {
    /// Wrap a VC body already renamed to its versioned form at `point`.
    pub(crate) fn versioned(formula: Formula, point: BlockId) -> Self {
        Vc { formula, point }
    }

    pub(crate) fn into_formula(self) -> Formula {
        self.formula
    }
}

/// The single version-aware meet: conjoin entry `facts` onto a versioned `vc`.
/// Because the VC body's reassigned variables carry a `#token` and the entry
/// facts carry bare names, a fact about a reassigned place names a different
/// variable than the body and contributes only a free (unconstraining) conjunct —
/// the kill's drop, achieved structurally. Verdict-equivalence is proven by
/// `crate::generate::flip_matches_kill_stmt`.
pub(crate) fn conjoin(facts: &[Fact], vc: Vc) -> Formula {
    if facts.is_empty() {
        return vc.into_formula();
    }
    let mut conj = Vec::with_capacity(facts.len() + 1);
    conj.extend(facts.iter().map(|f| f.formula.clone()));
    conj.push(vc.into_formula());
    Formula::And(conj)
}

pub(crate) fn conjoin_owned(facts: Vec<Fact>, vc: Vc) -> Formula {
    if facts.is_empty() {
        return vc.into_formula();
    }
    let mut conj = Vec::with_capacity(facts.len() + 1);
    conj.extend(facts.into_iter().map(|f| f.formula));
    conj.push(vc.into_formula());
    Formula::And(conj)
}
