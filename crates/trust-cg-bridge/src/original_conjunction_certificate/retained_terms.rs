//! Select the existing carrier for each distinct packet model. Legacy wire
//! shape and limits remain exactly TermPacket v1. Formula packets use the
//! maintained TrustIR CEXDAG02 carrier, never a second expression schema.

use serde::{Deserialize, Serialize};

use super::terms::TermPacket;

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(untagged)]
pub(super) enum RetainedTerms {
    Legacy(TermPacket),
    Formula(DagTerms),
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct DagTerms {
    clean_expr_dag_v2: DagPair,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct DagPair {
    goal: Vec<u8>,
    proof: Vec<u8>,
}

impl From<TermPacket> for RetainedTerms {
    fn from(packet: TermPacket) -> Self {
        Self::Legacy(packet)
    }
}

impl RetainedTerms {
    pub(super) fn is_formula(&self) -> bool {
        matches!(self, Self::Formula(_))
    }

    pub(super) fn validate(&self) -> Result<(), String> {
        match self {
            Self::Legacy(packet) => packet.validate(),
            Self::Formula(packet) => {
                for bytes in [&packet.clean_expr_dag_v2.goal, &packet.clean_expr_dag_v2.proof] {
                    if bytes.is_empty() || bytes.len() > super::MAX_WIRE_BYTES {
                        return Err("retained Formula DAG byte bound".into());
                    }
                }
                #[cfg(feature = "fmrel")]
                {
                    let _ = self.restore()?;
                    Ok(())
                }
                #[cfg(not(feature = "fmrel"))]
                Err("retained Formula DAG requires the fmrel feature".into())
            }
        }
    }

    /// Diagnostic carrier records only. CEXDAG02 counts Name/Level/Expr
    /// records; its maintained decoder, not this header observation, validates
    /// the carrier. No branch or budget depends on this reported count.
    pub(super) fn node_count(&self) -> usize {
        match self {
            Self::Legacy(packet) => packet.node_count(),
            Self::Formula(packet) => {
                [&packet.clean_expr_dag_v2.goal, &packet.clean_expr_dag_v2.proof]
                    .into_iter()
                    .map(|bytes| {
                        bytes
                            .get(8..12)
                            .and_then(|count| count.try_into().ok())
                            .map(u32::from_le_bytes)
                            .unwrap_or(0) as usize
                    })
                    .sum()
            }
        }
    }

    #[cfg(feature = "fmrel")]
    pub(super) fn capture_formula(
        goal: &clean_kernel::Expr,
        proof: &clean_kernel::Expr,
    ) -> Result<Self, String> {
        let packet = Self::Formula(DagTerms {
            clean_expr_dag_v2: DagPair {
                goal: trust_ir::proof::encode_clean_expr_dag_v2(goal)
                    .map_err(|error| format!("retained Formula final goal: {error}"))?,
                proof: trust_ir::proof::encode_clean_expr_dag_v2(proof)
                    .map_err(|error| format!("retained Formula final proof: {error}"))?,
            },
        });
        packet.validate()?;
        Ok(packet)
    }

    /// The distinct Formula model hashes the exact canonical owner-carrier
    /// bytes. It never expands a shared proof through Expr's tree serializer.
    #[cfg(feature = "fmrel")]
    pub(super) fn formula_digests(&self) -> Result<(String, String), String> {
        use sha2::{Digest, Sha256};
        let Self::Formula(packet) = self else {
            return Err("retained Formula model requires CEXDAG02 terms".into());
        };
        Ok((
            format!("{:x}", Sha256::digest(&packet.clean_expr_dag_v2.goal)),
            format!("{:x}", Sha256::digest(&packet.clean_expr_dag_v2.proof)),
        ))
    }

    #[cfg(feature = "kernel-recheck")]
    pub(super) fn restore(&self) -> Result<(clean_kernel::Expr, clean_kernel::Expr), String> {
        match self {
            Self::Legacy(packet) => packet.restore(),
            Self::Formula(packet) => {
                #[cfg(feature = "fmrel")]
                {
                    Ok((
                        trust_ir::proof::decode_clean_expr_dag_v2(&packet.clean_expr_dag_v2.goal)?,
                        trust_ir::proof::decode_clean_expr_dag_v2(&packet.clean_expr_dag_v2.proof)?,
                    ))
                }
                #[cfg(not(feature = "fmrel"))]
                {
                    let _ = packet;
                    Err("retained Formula DAG requires the fmrel feature".into())
                }
            }
        }
    }
}

#[cfg(all(test, feature = "fmrel"))]
mod tests {
    use clean_kernel::Expr;

    use super::*;

    #[test]
    fn existing_legacy_wire_is_unchanged_and_formula_uses_the_owner_dag() {
        let goal = Expr::const_str("Bool");
        let legacy = TermPacket::capture(&goal, &goal).unwrap();
        let wire = serde_json::to_vec(&legacy).unwrap();
        let wrapped: RetainedTerms = legacy.into();
        assert_eq!(serde_json::to_vec(&wrapped).unwrap(), wire);
        assert!(!wrapped.is_formula());
        let mut proof = Expr::const_str("Bool.true");
        for _ in 0..30 {
            proof = Expr::app(proof.clone(), proof);
        }
        assert!(TermPacket::capture(&goal, &proof).is_err());
        let dag = RetainedTerms::capture_formula(&goal, &proof).unwrap();
        assert!(dag.is_formula());
        assert_eq!(dag.restore().unwrap(), (goal, proof));
        assert!(dag.node_count() < 100);
        let restored: RetainedTerms =
            serde_json::from_slice(&serde_json::to_vec(&dag).unwrap()).unwrap();
        assert_eq!(dag.formula_digests().unwrap(), restored.formula_digests().unwrap());
        restored.validate().unwrap();
    }

    #[test]
    fn malformed_owner_carrier_and_mixed_wire_are_refused() {
        let expr = Expr::const_str("Bool.true");
        let mut dag = RetainedTerms::capture_formula(&expr, &expr).unwrap();
        let RetainedTerms::Formula(packet) = &mut dag else { unreachable!() };
        packet.clean_expr_dag_v2.proof.push(0);
        assert!(dag.validate().is_err());
        let mut wire = serde_json::to_value(&dag).unwrap();
        wire["version"] = 1.into();
        assert!(serde_json::from_value::<RetainedTerms>(wire).is_err());
    }
}
