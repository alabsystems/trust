//! Typed source question retained when body lowering withholds a proof query.
//!
//! This is a refusal claim, not proof or freshness authority. Consumers must
//! bind it to the current compiler source clause and fresh generated VC.

use serde::{Deserialize, Serialize};

use super::Formula;

/// A closed account of the body-lowering decision that withheld a contract VC.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum ContractBodyDeclineCause {
    /// An unmodeled sysroot call writes the return slot, and no positive
    /// premise constrains it before the negated authored postcondition.
    UnconstrainedReturnCall,
}

/// Authored predicate carried separately from the non-proving refusal query.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ContractBodyDecline {
    /// The actual closed producer branch, not a diagnostic classification.
    pub cause: ContractBodyDeclineCause,
    /// Dense authored clause index, requiring independent current-source binding.
    pub source_contract_index: usize,
    /// The actual typed predicate, never diagnostic text or the refusal's
    /// `Bool(true)` query. Exact source domains are independently rebound from
    /// the current compiler contract proposition before monitor association.
    pub source_predicate: Formula,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ProofLevel, RuntimeCheckEnv, SourceSpan, VcKind, VerificationCondition};

    #[test]
    fn contract_decline_never_mints_static_or_language_check_authority() {
        let kind = VcKind::DeclinedContractBody(Box::new(ContractBodyDecline {
            cause: ContractBodyDeclineCause::UnconstrainedReturnCall,
            source_contract_index: 0,
            source_predicate: Formula::Var("authored_predicate".into(), crate::Sort::Bool),
        }));
        assert_eq!(kind.proof_level(), ProofLevel::L1Functional);
        for formula in [Formula::Bool(false), Formula::Bool(true)] {
            let row = VerificationCondition {
                kind: kind.clone(),
                function: "declined".into(),
                location: SourceSpan::default(),
                formula,
                contract_metadata: None,
                obligation: None,
            };
            assert!(row.kernel_authority_refusal().is_some());
        }
        for overflow_checks in [false, true] {
            for ub_checks in [false, true] {
                assert!(
                    !kind.has_runtime_fallback_in(RuntimeCheckEnv { overflow_checks, ub_checks })
                );
            }
        }
        let round_trip: VcKind =
            serde_json::from_str(&serde_json::to_string(&kind).unwrap()).unwrap();
        assert_eq!(round_trip, kind, "typed refusal data is not freshness or proof authority");
        let generic = VcKind::UnsupportedMir {
            kind: "SpecUnverifiable".into(),
            detail: "UnconstrainedReturnCall source_contract_index=0".into(),
        };
        assert!(generic.declined_contract_body().is_none(), "diagnostic text has no typed claim");
    }
}
