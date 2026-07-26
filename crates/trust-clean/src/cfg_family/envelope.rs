// Trust: M4 v0 — the static envelope checker (design §4.3, requirement 4).
// Every rule fires at PLAN TIME, before any Lean is emitted or loaded:
// violation is `Err(EnvelopeError)`, never a watchdog / timeout / attempt.
// "The envelope is enforced by shape, never by watchdog — per the envelope's
// own closing rule, 'watchdog ceilings are not measurements of demand.'"
// (design §4.3).
//
// For a family registered in `GENERATED_FAMILIES`, a planning failure is a
// hard `BridgeGateError` (`gate.rs`) — release evidence must not silently
// shrink the claimed family set. Exploratory callers (tests exercising the
// checker directly) see the same typed `EnvelopeError`.

use thiserror::Error;

use super::spec::{ClaimSpec, ComposeLevel, TermSpec};

/// E3 — visit budget. The measured depth (design §2 cost model, risk 3);
/// raising it needs a v0.5 depth-ramp artifact.
pub const K_MAX: usize = 6;

/// E4 — per-visit instruction budget. The measured point (W2/B6); `I = 2`
/// unlocks only after the v0.5 `I=2` measurement.
pub const I_MAX: usize = 1;

/// Every violation is a refusal to generate, with the rule, the measured
/// basis, and (where relevant) what would raise the limit — never a silent
/// truncation of the family.
#[derive(Debug, Error, Clone, PartialEq, Eq)]
pub enum EnvelopeError {
    #[error(
        "E3 (visit budget): family {family:?} would need {needed} block-visits, exceeding \
         K_MAX = {K_MAX} (the measured depth, design §2 cost model risk 3); raising it needs a \
         v0.5 depth-ramp artifact (k = 8, 12, 20) before the gate can assert it"
    )]
    VisitBudgetExceeded { family: &'static str, needed: usize },

    #[error(
        "E4 (instruction budget): family {family:?} block {block} has {count} instructions, \
         exceeding I_MAX = {I_MAX} (the measured point, W2/B6); I = 2 unlocks only after the \
         v0.5 I=2 measurement"
    )]
    InstructionBudgetExceeded { family: &'static str, block: usize, count: usize },

    #[error(
        "family {family:?} block {block}: {insts} instructions but {dests} bodyResultDests \
         rows — v0 requires exactly one destination row per instruction (single-result \
         instructions only)"
    )]
    DestArityMismatch { family: &'static str, block: usize, insts: usize, dests: usize },

    #[error(
        "family {family:?} block {block}: {given} entry/branch args but the block declares \
         {params} params — bindBlockParams would throw a type error at plan time, which the \
         envelope catches statically instead of letting it surface as a pinned rfl failure"
    )]
    ParamArityMismatch { family: &'static str, block: usize, given: usize, params: usize },

    #[error(
        "family {family:?} block {block}: operand ValueId {value_id} is not bound by any \
         param or prior instruction in this block — undefined SSA value"
    )]
    UndefinedValueId { family: &'static str, block: usize, value_id: u32 },

    #[error(
        "family {family:?} block {block}: Br target index {target} is out of range \
         (blocks.len() = {len})"
    )]
    UndefinedBlockTarget { family: &'static str, block: usize, target: usize, len: usize },

    #[error(
        "E6 (dependency closure): family {family:?} visit {visit} cites {lemma:?}, which is \
         not yet loaded in the active mode's closure — the generated family's value-arm \
         dependency (ARMS in trustir_bridge.rs) must load before any generated family that \
         cites it (catalog §0's manually-maintained load-order invariant, mechanized here)"
    )]
    DependencyMissing { family: &'static str, visit: usize, lemma: &'static str },

    #[error(
        "E8 (branch guard): family {family:?} block {block} has a symbolic branch guard — the \
         planner cannot ground it, so the trace is undecidable. Refuse and point at a \
         per-guard-literal case-split arm (v1's CondBr expansion) or T7 induction (v2) instead"
    )]
    SymbolicGuard { family: &'static str, block: usize },

    #[error(
        "E9 (unbounded claims): family {family:?} requests an unbounded/divergence claim; only \
         T7 induction may express that (v2 scope) — unrolling is refused unconditionally"
    )]
    UnrollingRefused { family: &'static str },

    #[error(
        "family {family:?}: ComposeLevel::C1 (transitive prefix) is refused — v0 does not \
         implement the v0.5 measurement harness (env-gated, isolated host, k = 2..6 ramp) that \
         the design requires before C1 may be asserted in gate-loaded sources (design §3, T5 \
         'C1 — transitive prefix': 'the gate never asserts C1 before that'). C2 (ground f := 0) \
         is not refused here because it cannot even be REQUESTED — ComposeLevel has no C2 \
         variant; ground multi-visit stepNWithContext is banned by the type, not by this check"
    )]
    UnmeasuredComposition { family: &'static str },

    #[error(
        "family {family:?} declares {count} claims; v0 requires exactly one \
         (ClaimSpec::BoundedRun) — multi-claim families are a v1+ extension"
    )]
    ClaimArityUnsupported { family: &'static str, count: usize },

    #[error("family {family:?}: entry index {entry} is out of range (blocks.len() = {len})")]
    UndefinedEntry { family: &'static str, entry: usize, len: usize },

    #[error(
        "E7 (name uniqueness): family name {name:?} is registered more than once in \
         GENERATED_FAMILIES — every generated identifier is prefixed by the family name, so a \
         collision here would silently shadow another family's declarations in the cumulative \
         gate Environment"
    )]
    NameCollision { name: &'static str },
}

/// E7, applied to the whole registry (not just pairwise): every
/// [`CfgFamilySpec::name`] in `specs` must be unique. Called once, before any
/// family in the slice is planned, so a collision refuses the WHOLE gate run
/// rather than nondeterministically depending on iteration order.
pub fn check_registry_unique(specs: &[super::spec::CfgFamilySpec]) -> Result<(), EnvelopeError> {
    let mut seen = std::collections::BTreeSet::new();
    for s in specs {
        if !seen.insert(s.name) {
            return Err(EnvelopeError::NameCollision { name: s.name });
        }
    }
    Ok(())
}

/// E9 + the ComposeLevel half of E2: exactly one `BoundedRun { compose }`
/// claim, with `compose` statically refused unless it is `C0`.
pub fn check_claims(
    family: &'static str,
    claims: &'static [ClaimSpec],
) -> Result<ComposeLevel, EnvelopeError> {
    if claims.len() != 1 {
        return Err(EnvelopeError::ClaimArityUnsupported { family, count: claims.len() });
    }
    match claims[0] {
        ClaimSpec::BoundedRun { compose: ComposeLevel::C0 } => Ok(ComposeLevel::C0),
        ClaimSpec::BoundedRun { compose: ComposeLevel::C1 } => {
            Err(EnvelopeError::UnmeasuredComposition { family })
        }
    }
}

/// E4 + the dest-arity structural check, applied to one block.
pub fn check_block_shape(
    family: &'static str,
    block_idx: usize,
    block: &super::spec::BlockSpec,
) -> Result<(), EnvelopeError> {
    if block.insts.len() > I_MAX {
        return Err(EnvelopeError::InstructionBudgetExceeded {
            family,
            block: block_idx,
            count: block.insts.len(),
        });
    }
    if block.insts.len() != block.dests.len() {
        return Err(EnvelopeError::DestArityMismatch {
            family,
            block: block_idx,
            insts: block.insts.len(),
            dests: block.dests.len(),
        });
    }
    // E8 (vacuous in v0 by construction): TermSpec has no CondBr variant, so
    // there is no branch guard to ground. Retained as an explicit match arm
    // (not a wildcard) so v1's CondBr addition trips a compile error here
    // until this function actually grounds the guard, rather than silently
    // passing a case it was never updated to handle.
    match block.term {
        TermSpec::Return(_) | TermSpec::Br { .. } => {}
    }
    Ok(())
}

/// E3 — call once per visit as the planner walks the trace; `k` is the
/// 1-based visit index about to be emitted.
pub fn check_visit_budget(family: &'static str, k: usize) -> Result<(), EnvelopeError> {
    if k > K_MAX {
        return Err(EnvelopeError::VisitBudgetExceeded { family, needed: k });
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cfg_family::spec::{BinOpLit, BlockSpec, CfgFamilySpec, InstSpec, ModeSlice, TyLit};

    #[test]
    fn registry_unique_accepts_distinct_names() {
        const A: CfgFamilySpec = CfgFamilySpec {
            name: "envelope_test_a",
            blocks: &[BlockSpec {
                params: &[],
                insts: &[],
                dests: &[],
                term: TermSpec::Return(&[]),
            }],
            entry: 0,
            entry_args: &[],
            claims: &[ClaimSpec::BoundedRun { compose: ComposeLevel::C0 }],
            mode: ModeSlice::AllModes,
        };
        const B: CfgFamilySpec = CfgFamilySpec { name: "envelope_test_b", ..A };
        assert!(check_registry_unique(&[A, B]).is_ok());
    }

    #[test]
    fn registry_unique_rejects_duplicate_names() {
        const A: CfgFamilySpec = CfgFamilySpec {
            name: "envelope_test_dup",
            blocks: &[BlockSpec {
                params: &[],
                insts: &[],
                dests: &[],
                term: TermSpec::Return(&[]),
            }],
            entry: 0,
            entry_args: &[],
            claims: &[ClaimSpec::BoundedRun { compose: ComposeLevel::C0 }],
            mode: ModeSlice::AllModes,
        };
        let err = check_registry_unique(&[A, A]).expect_err("duplicate names must refuse (E7)");
        assert!(matches!(err, EnvelopeError::NameCollision { name: "envelope_test_dup" }));
    }

    /// THE MISSION'S EXPLICIT ENVELOPE-REFUSAL TEST: a spec requesting
    /// `ComposeLevel::C1` (the design's "measure before trusting" transitive
    /// composition, the closest thing to the ground multi-visit
    /// `stepNWithContext` ban that is even representable in the type — `C2`
    /// itself has NO variant, so it cannot be requested at all) must be
    /// REFUSED by `check_claims` with an honest, typed error — never a
    /// silent downgrade to C0 and never a watchdog/timeout.
    #[test]
    fn compose_level_c1_is_refused_honestly() {
        let err = check_claims(
            "envelope_test_c1",
            &[ClaimSpec::BoundedRun { compose: ComposeLevel::C1 }],
        )
        .expect_err("C1 must refuse until the v0.5 measurement harness lands");
        assert!(
            matches!(err, EnvelopeError::UnmeasuredComposition { family: "envelope_test_c1" }),
            "got {err:?}"
        );
        // The refusal text is honest about WHY (v0.5 harness missing) and
        // about the STRONGER guarantee for C2 (unrepresentable, not merely
        // refused).
        let msg = err.to_string();
        assert!(msg.contains("v0.5"), "refusal must name what would unlock it: {msg}");
        assert!(msg.contains("C2"), "refusal must state the stronger C2 guarantee: {msg}");
    }

    #[test]
    fn compose_level_c0_is_accepted() {
        assert_eq!(
            check_claims(
                "envelope_test_c0",
                &[ClaimSpec::BoundedRun { compose: ComposeLevel::C0 }]
            )
            .expect("C0 is the only asserted level in v0"),
            ComposeLevel::C0
        );
    }

    #[test]
    fn multi_claim_families_are_refused() {
        let claims: &[ClaimSpec] = &[
            ClaimSpec::BoundedRun { compose: ComposeLevel::C0 },
            ClaimSpec::BoundedRun { compose: ComposeLevel::C0 },
        ];
        let err =
            check_claims("envelope_test_multi", claims).expect_err("v0 requires exactly one claim");
        assert!(matches!(err, EnvelopeError::ClaimArityUnsupported { count: 2, .. }));
    }

    #[test]
    fn instruction_budget_exceeded_refuses() {
        const TWO_INSTS: BlockSpec = BlockSpec {
            params: &[(0, TyLit::I8), (1, TyLit::I8)],
            insts: &[
                InstSpec::BinOp { op: BinOpLit::Add, ty: TyLit::I8, lhs: 0, rhs: 1 },
                InstSpec::BinOp { op: BinOpLit::Sub, ty: TyLit::I8, lhs: 0, rhs: 1 },
            ],
            dests: &[2, 3],
            term: TermSpec::Return(&[3]),
        };
        let err = check_block_shape("envelope_test_i2", 0, &TWO_INSTS)
            .expect_err("I_MAX = 1 must refuse a 2-instruction block (E4)");
        assert!(matches!(
            err,
            EnvelopeError::InstructionBudgetExceeded {
                family: "envelope_test_i2",
                block: 0,
                count: 2
            }
        ));
    }

    #[test]
    fn visit_budget_exceeded_refuses_past_k_max() {
        assert!(check_visit_budget("envelope_test_k", K_MAX).is_ok());
        let err = check_visit_budget("envelope_test_k", K_MAX + 1)
            .expect_err("k > K_MAX must refuse (E3)");
        assert!(
            matches!(err, EnvelopeError::VisitBudgetExceeded { needed, .. } if needed == K_MAX + 1)
        );
    }
}
