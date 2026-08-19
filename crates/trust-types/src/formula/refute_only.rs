// trust-types/formula/refute_only: the REFUTE-ONLY verification-condition class.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

//! Trust: a **one-directional** verification-condition class.
//!
//! # Why this type exists
//!
//! Every ordinary [`VerificationCondition`] is *bidirectional*: its formula is
//! the violation predicate over an OVER-approximation of the function's
//! reachable states, so SAT is a (possibly spurious) alarm and UNSAT is a real
//! proof. The whole verifier is built on that convention, and one VC serves both
//! answers.
//!
//! A **path-enumerating** formula inverts exactly one half of that. The formula
//! of a [`RefuteOnlyVc`] is the exact symbolic execution of a FINITE set of
//! enumerated acyclic CFG paths, so it UNDER-approximates:
//!
//! * **SAT is sound and stronger than usual.** Every model is a concrete
//!   execution of one enumerated path — a witness, not an alarm. There is no
//!   spurious-counterexample risk to discharge, because nothing was
//!   over-approximated away.
//! * **UNSAT is UNSOUND as a proof.** It says only "none of the *enumerated*
//!   paths reaches the failure block". Everything past a back edge — every
//!   execution that goes round a loop more times than the enumeration unrolled —
//!   is simply absent from the formula. Reading that UNSAT as a proof is a false
//!   proof, and it is the *default* outcome for any loop.
//!
//! # How the type enforces it
//!
//! The marker is not a flag a consumer can forget to read. It is the return
//! type:
//!
//! * A [`RefuteOnlyVc`] never hands out an owned [`VerificationCondition`].
//!   The query is visible only as a `&` inside the closure passed to
//!   [`RefuteOnlyVc::refute_with`].
//! * That closure's [`VerificationResult`] is consumed INSIDE `refute_with` and
//!   never escapes. The only value that comes back out is [`RefuteOnlyOutcome`],
//!   which has exactly two variants and must be matched.
//! * [`RefuteOnlyOutcome::NoRefutation`] is **payload-free and undifferentiated**:
//!   a solver `Proved` (UNSAT) and a solver `Unknown` produce the byte-identical
//!   value. A consumer cannot distinguish them, so it cannot bank one as a proof
//!   even if it wanted to. The UNSAT direction is erased at the type boundary,
//!   which is the only representation of "MUST DISCARD" that a future edit
//!   cannot quietly undo.
//! * The [`VerificationResult`] inside [`RefuteOnlyOutcome::Refuted`] is minted
//!   by `refute_with` itself and is always [`VerificationResult::Failed`]. There
//!   is no code path through this API that produces a `Proved` row for a
//!   refute-only VC.
//!
//! `RefuteOnlyOutcome` is deliberately NOT `#[non_exhaustive]`: a downstream
//! wildcard arm is exactly the escape hatch this class must not have.

use super::vc::VerificationCondition;
use crate::model::BlockId;
use crate::result::VerificationResult;

/// Where a [`RefuteOnlyVc`]'s under-approximating formula came from.
///
/// Diagnostic provenance only — it grants nothing. Kept alongside the query so a
/// report can say *which* paths were enumerated when a refutation lands, and so
/// a consumer can avoid re-solving sibling paths of a block that already
/// refuted.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum RefuteOnlyProvenance {
    /// The formula is the exact symbolic execution of ONE acyclic CFG path from
    /// the entry block to `panic_block`, with every read resolved to the value
    /// written by the last write ON THAT PATH.
    ///
    /// `blocks` is that path, entry first. It visits no block twice, so no back
    /// edge is taken and no loop iteration beyond the enumerated prefix is
    /// modeled — which is precisely why UNSAT proves nothing here.
    AcyclicPath {
        /// The failure block this path reaches.
        panic_block: BlockId,
        /// The path, entry first. No repeats.
        blocks: Vec<BlockId>,
    },
}

impl RefuteOnlyProvenance {
    /// The failure block this query is about.
    #[must_use]
    pub fn panic_block(&self) -> BlockId {
        match self {
            RefuteOnlyProvenance::AcyclicPath { panic_block, .. } => *panic_block,
        }
    }
}

/// A verification condition whose formula UNDER-approximates the function's
/// reachable states, and which may therefore report only a REFUTATION.
///
/// See the module docs for the soundness argument and for why the restriction is
/// expressed as a type rather than as a flag.
#[derive(Debug, Clone)]
pub struct RefuteOnlyVc {
    // PRIVATE, and there is no accessor. Handing out an owned
    // `VerificationCondition` would hand out the ability to pair it with an
    // arbitrary `VerificationResult` — including a `Proved` — which is the exact
    // false-proof this class exists to make unrepresentable.
    query: VerificationCondition,
    provenance: RefuteOnlyProvenance,
}

/// The ONLY verdict a [`RefuteOnlyVc`] can produce.
///
/// Two variants, both of which a consumer must handle. `NoRefutation` carries no
/// payload BY CONSTRUCTION: solver-UNSAT and solver-Unknown collapse onto it
/// indistinguishably, so the unsound (UNSAT-as-proof) direction is not merely
/// discouraged — it is unrepresentable.
#[must_use = "a refute-only outcome must be matched: `Refuted` is the ONLY verdict this VC class \
              may report, and `NoRefutation` is NOT a proof"]
#[derive(Debug, Clone)]
pub enum RefuteOnlyOutcome {
    /// The under-approximating formula was SAT: a concrete model of one
    /// enumerated acyclic path, hence a genuine execution that reaches the
    /// failure block. `result` is always [`VerificationResult::Failed`].
    Refuted {
        /// The query, for reporting. Its result is fixed at `Failed`.
        vc: VerificationCondition,
        /// Always [`VerificationResult::Failed`] — minted here, never passed
        /// through from the solver.
        result: VerificationResult,
        /// Provenance of the refuted path, for diagnostics.
        provenance: RefuteOnlyProvenance,
    },
    /// No refutation was obtained. This is **not** a proof and **not** an
    /// unknown: it is the absence of a witness, and it says nothing whatsoever
    /// about the function. A solver UNSAT on an under-approximation covers only
    /// the enumerated paths; everything past the back edge is unmodeled.
    NoRefutation,
}

impl RefuteOnlyVc {
    /// Wrap a path-enumerated query as a refute-only VC.
    ///
    /// The caller asserts that `query.formula` UNDER-approximates: every model
    /// of it must be a real execution of the function. Producers that cannot
    /// model a construct exactly must DROP the path rather than leave a read
    /// unconstrained — an unconstrained read is an over-approximation, and SAT
    /// under an over-approximation is a spurious witness, i.e. a false
    /// refutation.
    #[must_use]
    pub fn new(query: VerificationCondition, provenance: RefuteOnlyProvenance) -> Self {
        Self { query, provenance }
    }

    /// Provenance of this query (diagnostics; grants nothing).
    #[must_use]
    pub fn provenance(&self) -> &RefuteOnlyProvenance {
        &self.provenance
    }

    /// Where the failure block sits, for reporting.
    #[must_use]
    pub fn location(&self) -> &crate::model::SourceSpan {
        &self.query.location
    }

    /// Run `solve` on the under-approximating query and return the only verdict
    /// this class admits.
    ///
    /// `solve` receives the query by reference (so it can be handed to a router)
    /// and returns the solver's raw [`VerificationResult`], or `None` if the
    /// backend produced no result at all. That raw result is consumed HERE: it
    /// does not escape, and the `Proved` / `Unknown` / `Timeout` cases collapse
    /// onto the payload-free [`RefuteOnlyOutcome::NoRefutation`].
    ///
    /// The `Failed` result attached to a refutation is constructed here, from
    /// this function's own `solver` label and the solver's counterexample. The
    /// solver's own `Proved` value is never forwarded anywhere.
    #[must_use = "the outcome must be matched; `NoRefutation` is not a proof"]
    pub fn refute_with<F>(self, solver: crate::Symbol, solve: F) -> RefuteOnlyOutcome
    where
        F: FnOnce(&VerificationCondition) -> Option<VerificationResult>,
    {
        match solve(&self.query) {
            // SAT on an under-approximation: every model is a real execution of
            // one enumerated acyclic path. Witness-backed refutation.
            Some(VerificationResult::Failed { time_ms, counterexample, .. }) => {
                RefuteOnlyOutcome::Refuted {
                    vc: self.query,
                    result: VerificationResult::Failed { solver, time_ms, counterexample },
                    provenance: self.provenance,
                }
            }
            // EVERYTHING else — including a solver UNSAT reported as `Proved`.
            // An UNSAT here covers only the enumerated paths and is not a proof
            // of anything about the function, so it is discarded without being
            // distinguishable from `Unknown`.
            _ => RefuteOnlyOutcome::NoRefutation,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::formula::vc_kind::VcKind;
    use crate::model::SourceSpan;
    use crate::{Formula, ProofStrength, Sort, Symbol};

    fn query() -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::Assertion { message: "per-path".into() },
            function: Symbol::intern("f"),
            location: SourceSpan::default(),
            formula: Formula::Eq(
                Box::new(Formula::Var("n".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ),
            contract_metadata: None,
            obligation: None,
        }
    }

    fn vc() -> RefuteOnlyVc {
        RefuteOnlyVc::new(
            query(),
            RefuteOnlyProvenance::AcyclicPath {
                panic_block: BlockId(4),
                blocks: vec![BlockId(0), BlockId(1), BlockId(2), BlockId(4)],
            },
        )
    }

    #[test]
    fn sat_is_a_refutation_with_a_failed_result() {
        let out = vc().refute_with(Symbol::intern("test"), |_| {
            Some(VerificationResult::Failed {
                solver: Symbol::intern("ay"),
                time_ms: 3,
                counterexample: None,
            })
        });
        match out {
            RefuteOnlyOutcome::Refuted { result, provenance, .. } => {
                assert!(matches!(result, VerificationResult::Failed { .. }));
                assert_eq!(provenance.panic_block(), BlockId(4));
            }
            RefuteOnlyOutcome::NoRefutation => panic!("SAT must refute"),
        }
    }

    /// THE soundness test for this class: an UNSAT of an under-approximating
    /// formula must be indistinguishable from an Unknown at the API boundary.
    /// If these two ever produce different values, a consumer can bank the
    /// UNSAT — a false proof of everything past the back edge.
    #[test]
    fn unsat_and_unknown_are_byte_identical_at_the_boundary() {
        let unsat = vc().refute_with(Symbol::intern("test"), |_| {
            Some(VerificationResult::Proved {
                solver: Symbol::intern("ay"),
                time_ms: 1,
                strength: ProofStrength::smt_unsat_strict_checked(),
                proof_certificate: None,
                solver_warnings: None,
                native_proof_envelope: None,
            })
        });
        let unknown = vc().refute_with(Symbol::intern("test"), |_| {
            Some(VerificationResult::Unknown {
                solver: Symbol::intern("ay"),
                time_ms: 1,
                reason: "incomplete".into(),
            })
        });
        let nothing = vc().refute_with(Symbol::intern("test"), |_| None);
        for out in [&unsat, &unknown, &nothing] {
            assert!(
                matches!(out, RefuteOnlyOutcome::NoRefutation),
                "an under-approximating UNSAT must never reach a consumer as a proof"
            );
        }
        // Payload-free, so the three are literally the same value.
        assert_eq!(format!("{unsat:?}"), format!("{unknown:?}"));
        assert_eq!(format!("{unsat:?}"), format!("{nothing:?}"));
    }

    /// A timeout is a `NoRefutation` too — never a proof, never a refutation.
    #[test]
    fn timeout_is_no_refutation() {
        let out = vc().refute_with(Symbol::intern("test"), |_| {
            Some(VerificationResult::Timeout { solver: Symbol::intern("ay"), timeout_ms: 10 })
        });
        assert!(matches!(out, RefuteOnlyOutcome::NoRefutation));
    }
}
