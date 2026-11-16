//! The actual successful queue branch that materialized a native output.
//! This private, nonserialized observation grants neither input custody nor GO.
use crate::util::CargoResult;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Materialization {
    Warm,
    Compiled { member: [u8; 16] },
}

impl Materialization {
    /// `warm` is the branch actually executed, including the ordinary recheck
    /// under the unit lock. `compiler` is from that job's original loan AFTER
    /// successful target retirement. Missing cold provenance never means warm.
    pub(crate) fn completed(warm: bool, compiler: Option<[u8; 16]>) -> CargoResult<Self> {
        match (warm, compiler) {
            (true, None) => Ok(Self::Warm),
            (false, Some(member)) if member != [0; 16] => Ok(Self::Compiled { member }),
            _ => anyhow::bail!(
                "native output lacks its actual successful warm branch or original compiler member"
            ),
        }
    }

    pub(crate) fn producer_attempt(self) -> Option<[u8; 16]> {
        match self {
            Self::Warm => None,
            Self::Compiled { member } => Some(member),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn current_branch_and_actual_compiler_must_agree_without_a_cold_to_warm_fallback() {
        assert_eq!(
            Materialization::completed(true, None).unwrap(),
            Materialization::Warm
        );
        assert_eq!(
            Materialization::completed(false, Some([3; 16]))
                .unwrap()
                .producer_attempt(),
            Some([3; 16])
        );
        assert!(Materialization::completed(false, None).is_err());
        assert!(Materialization::completed(true, Some([3; 16])).is_err());
        assert!(Materialization::completed(false, Some([0; 16])).is_err());
    }
}
