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
        Fact { formula }
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
    let mut conj: Vec<Formula> = facts.iter().map(|f| f.formula.clone()).collect();
    conj.push(vc.into_formula());
    Formula::And(conj)
}
