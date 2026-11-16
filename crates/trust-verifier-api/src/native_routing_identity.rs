//! Decode native request routing from the public obligation, never proof authority.
//!
//! The channels must agree when both are present. Engines retain their own
//! required fields and suite admission after this shared correspondence check.

use crate::TrustObligation;

pub const SUITE_KEY: &str = "trust.trust_ir.native.verifier_suite";
pub const REQUEST_KEY: &str = "trust.trust_ir.native.request_id";
pub const PROOF_KEY: &str = "trust.trust_ir.native.proof_obligation_id";

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeRoutingIdentity {
    pub suite: Option<String>,
    pub request_id: Option<u32>,
    pub proof_obligation_id: Option<u32>,
}

/// Existing transport spelling policies, not engine or proof admission.
#[derive(Debug, Clone, Copy)]
pub enum SuiteComparison {
    Exact,
    /// Transport suite tokens may differ in ASCII case or use `_` for `-`.
    /// The consumer must still enforce its own admitted metadata spelling.
    VerifierAliases,
}

#[derive(Debug, Clone, Copy)]
pub struct NativeRoutingIdentityPolicy {
    /// Router indexing permits an ID-only channel; some engines require metadata.
    pub canonical_id_fallback: bool,
    /// MC's metadata protocol requires the unique decimal representation.
    pub canonical_metadata_numbers: bool,
    pub suite_comparison: SuiteComparison,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NativeRoutingIdentityError {
    DuplicateMetadata { key: &'static str },
    InvalidNumber { key: &'static str, value: String },
    Conflict { key: &'static str, metadata: String, canonical: String },
}

impl std::fmt::Display for NativeRoutingIdentityError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::DuplicateMetadata { key } => {
                write!(f, "duplicate native routing metadata `{key}`")
            }
            Self::InvalidNumber { key, value } => {
                write!(f, "invalid native routing number `{key}`: `{value}`")
            }
            Self::Conflict { key, metadata, canonical } => write!(
                f,
                "native routing metadata `{key}` value `{metadata}` disagrees with canonical obligation id value `{canonical}`"
            ),
        }
    }
}

impl std::error::Error for NativeRoutingIdentityError {}

fn canonical_identity(id: &str) -> Option<NativeRoutingIdentity> {
    let suffix = id.strip_prefix("trust_ir-native-")?;
    let (suite, rest) = suffix.split_once("-request-")?;
    let (request, proof) = rest.split_once("-proof-")?;
    Some(NativeRoutingIdentity {
        suite: Some(suite.to_string()),
        request_id: Some(request.parse().ok()?),
        proof_obligation_id: Some(proof.parse().ok()?),
    })
}

pub fn parse_native_routing_identity(
    obligation: &TrustObligation,
    policy: NativeRoutingIdentityPolicy,
) -> Result<NativeRoutingIdentity, NativeRoutingIdentityError> {
    let mut values = [None, None, None];
    for (index, key) in [SUITE_KEY, REQUEST_KEY, PROOF_KEY].into_iter().enumerate() {
        for entry in obligation.metadata.iter().filter(|entry| entry.key == key) {
            if values[index].replace(entry.value.as_str()).is_some() {
                return Err(NativeRoutingIdentityError::DuplicateMetadata { key });
            }
        }
    }
    let number = |key, value: Option<&str>| -> Result<Option<u32>, NativeRoutingIdentityError> {
        value
            .map(|value| {
                let parsed = value.parse::<u32>().ok().filter(|parsed| {
                    !policy.canonical_metadata_numbers || parsed.to_string() == value
                });
                parsed.ok_or_else(|| NativeRoutingIdentityError::InvalidNumber {
                    key,
                    value: value.to_string(),
                })
            })
            .transpose()
    };
    // Keep the router's historical malformed-number precedence.
    let proof_obligation_id = number(PROOF_KEY, values[2])?;
    let request_id = number(REQUEST_KEY, values[1])?;
    let mut identity = NativeRoutingIdentity {
        suite: values[0].map(str::to_string),
        request_id,
        proof_obligation_id,
    };
    if let Some(canonical) = canonical_identity(&obligation.obligation_id) {
        if let (Some(metadata), Some(id_suite)) = (&identity.suite, &canonical.suite) {
            let agrees = match policy.suite_comparison {
                SuiteComparison::Exact => metadata == id_suite,
                SuiteComparison::VerifierAliases => {
                    metadata.replace('-', "_").eq_ignore_ascii_case(&id_suite.replace('-', "_"))
                }
            };
            if !agrees {
                return Err(NativeRoutingIdentityError::Conflict {
                    key: SUITE_KEY,
                    metadata: metadata.clone(),
                    canonical: id_suite.clone(),
                });
            }
        }
        for (key, metadata, id_value) in [
            (REQUEST_KEY, identity.request_id, canonical.request_id),
            (PROOF_KEY, identity.proof_obligation_id, canonical.proof_obligation_id),
        ] {
            if let (Some(metadata), Some(id_value)) = (metadata, id_value) {
                if metadata != id_value {
                    return Err(NativeRoutingIdentityError::Conflict {
                        key,
                        metadata: metadata.to_string(),
                        canonical: id_value.to_string(),
                    });
                }
            }
        }
        if policy.canonical_id_fallback {
            identity.suite = identity.suite.or(canonical.suite);
            identity.request_id = identity.request_id.or(canonical.request_id);
            identity.proof_obligation_id =
                identity.proof_obligation_id.or(canonical.proof_obligation_id);
        }
    }
    Ok(identity)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{MetadataEntry, ObligationKind, SourceLocation};

    fn obligation(id: &str, metadata: &[(&str, &str)]) -> TrustObligation {
        TrustObligation {
            obligation_id: id.into(),
            kind: ObligationKind::Assertion,
            contract_id: None,
            proof_item_id: None,
            source: SourceLocation::default(),
            description: "routing correspondence only".into(),
            required_strength: None,
            summary_facts: Vec::new(),
            metadata: metadata
                .iter()
                .map(|(key, value)| MetadataEntry { key: (*key).into(), value: (*value).into() })
                .collect(),
        }
    }

    const ROUTER: NativeRoutingIdentityPolicy = NativeRoutingIdentityPolicy {
        canonical_id_fallback: true,
        canonical_metadata_numbers: false,
        suite_comparison: SuiteComparison::Exact,
    };

    #[test]
    fn complete_and_partial_channels_reconcile_without_inventing_fields() {
        let expected = NativeRoutingIdentity {
            suite: Some("trust-mc".into()),
            request_id: Some(7),
            proof_obligation_id: Some(2),
        };
        for metadata in [
            vec![],
            vec![(REQUEST_KEY, "7")],
            vec![(SUITE_KEY, "trust-mc"), (REQUEST_KEY, "7"), (PROOF_KEY, "2")],
        ] {
            assert_eq!(
                parse_native_routing_identity(
                    &obligation("trust_ir-native-trust-mc-request-7-proof-2", &metadata),
                    ROUTER
                )
                .unwrap(),
                expected
            );
        }
        assert_eq!(
            parse_native_routing_identity(&obligation("public", &[(PROOF_KEY, "2")]), ROUTER)
                .unwrap(),
            NativeRoutingIdentity { suite: None, request_id: None, proof_obligation_id: Some(2) }
        );
        let metadata_only = NativeRoutingIdentityPolicy { canonical_id_fallback: false, ..ROUTER };
        assert_eq!(
            parse_native_routing_identity(
                &obligation("trust_ir-native-trust-mc-request-7-proof-2", &[]),
                metadata_only
            )
            .unwrap(),
            NativeRoutingIdentity { suite: None, request_id: None, proof_obligation_id: None }
        );
    }

    #[test]
    fn every_duplicate_identity_key_refuses_even_equal_values() {
        for (key, value) in [(SUITE_KEY, "trust-mc"), (REQUEST_KEY, "7"), (PROOF_KEY, "2")] {
            for second in [value, "different"] {
                let error = parse_native_routing_identity(
                    &obligation("public", &[(key, value), (key, second)]),
                    ROUTER,
                )
                .unwrap_err();
                assert_eq!(error, NativeRoutingIdentityError::DuplicateMetadata { key });
            }
        }
    }

    #[test]
    fn each_canonical_component_rejects_metadata_substitution() {
        for (key, value) in [(SUITE_KEY, "trust-vc"), (REQUEST_KEY, "8"), (PROOF_KEY, "3")] {
            let error = parse_native_routing_identity(
                &obligation("trust_ir-native-trust-mc-request-7-proof-2", &[(key, value)]),
                ROUTER,
            )
            .unwrap_err();
            assert!(
                matches!(error, NativeRoutingIdentityError::Conflict { key: actual, .. } if actual == key)
            );
        }
    }

    #[test]
    fn numeric_transport_policies_preserve_their_exact_domains() {
        let strict = NativeRoutingIdentityPolicy { canonical_metadata_numbers: true, ..ROUTER };
        for (value, permissive, canonical) in [
            ("0", true, true),
            ("4294967295", true, true),
            ("01", true, false),
            ("+1", true, false),
            ("4294967296", false, false),
            ("-1", false, false),
            (" 1", false, false),
            ("1 ", false, false),
            ("", false, false),
        ] {
            for key in [REQUEST_KEY, PROOF_KEY] {
                let input = obligation("public", &[(key, value)]);
                assert_eq!(
                    parse_native_routing_identity(&input, ROUTER).is_ok(),
                    permissive,
                    "{key}={value}"
                );
                assert_eq!(
                    parse_native_routing_identity(&input, strict).is_ok(),
                    canonical,
                    "{key}={value}"
                );
            }
        }
    }

    #[test]
    fn suite_comparison_never_changes_the_returned_spelling() {
        for (id_suite, metadata_suite, comparison, accepted) in [
            ("trust-vc", "TRUST-VC", SuiteComparison::VerifierAliases, true),
            ("trust-vc", "trust_vc", SuiteComparison::VerifierAliases, true),
            ("trust_mc", "trust-mc", SuiteComparison::VerifierAliases, true),
            ("trust_mc", "TRUST-MC", SuiteComparison::VerifierAliases, true),
            ("trust_mc", "trust-mc", SuiteComparison::Exact, false),
        ] {
            let input = obligation(
                &format!("trust_ir-native-{id_suite}-request-7-proof-2"),
                &[(SUITE_KEY, metadata_suite)],
            );
            let result = parse_native_routing_identity(
                &input,
                NativeRoutingIdentityPolicy { suite_comparison: comparison, ..ROUTER },
            );
            assert_eq!(result.is_ok(), accepted);
            if let Ok(identity) = result {
                assert_eq!(identity.suite.as_deref(), Some(metadata_suite));
            }
        }
    }

    #[test]
    fn unrelated_and_incomplete_public_ids_do_not_create_routing() {
        for id in [
            "public",
            "trust_ir-native-trust-mc-request-7",
            "trust_ir-native-trust-mc-request-x-proof-2",
            "trust_ir-native-trust-mc-request-7-proof-2-extra",
        ] {
            let result =
                parse_native_routing_identity(&obligation(id, &[("unrelated", "9")]), ROUTER)
                    .unwrap();
            assert_eq!(
                result,
                NativeRoutingIdentity { suite: None, request_id: None, proof_obligation_id: None }
            );
        }
    }
}
