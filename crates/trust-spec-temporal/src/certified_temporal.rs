//! Kernel-rechecked temporal certificate transport.
//!
//! This is the production connection to ty's safety and liveness proof objects.
//! It never accepts a producer verdict string: every accepted object is parsed,
//! bound byte-for-byte to the caller's semantic inputs, and independently
//! replayed by the repository-pinned verifier.

/// Schema for Trust's normalized temporal evidence record.
pub const CERTIFIED_TEMPORAL_EVIDENCE_SCHEMA_V1: &str = "trust.certified-temporal-evidence/v1";

/// The temporal proposition class proved by an evidence object.
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum CertifiedTemporalPropertyClass {
    /// An invariant holds at every reachable state (`□ Safety`).
    AlwaysSafety,
    /// An eventual target is reached (`◇ P`) under weak fairness of `Next`.
    EventuallyUnderWeakFairness,
}

/// Exact-input-bound evidence after independent kernel replay.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct CertifiedTemporalEvidence {
    /// Versioned Trust wrapper schema.
    pub schema: String,
    /// The proved temporal property class.
    pub property_class: CertifiedTemporalPropertyClass,
    /// Original ty certificate schema.
    pub certificate_schema: String,
    /// Exact self-contained semantic source checked by the verifier.
    pub spec_src: String,
    /// Exact checker configuration whose Init/Next/constants are bound below.
    pub config_src: String,
    /// Named property operator for liveness; invariant names for safety.
    pub properties: Vec<String>,
    /// Named measure operator for liveness, absent for safety.
    pub measure: Option<String>,
    /// Independent verifier diagnostic, retained for audit only.
    pub recheck_detail: String,
    /// The exact producer object. It is evidence only because replay succeeded.
    pub raw_certificate_json: String,
}

/// Fail-closed temporal certificate binding/replay errors.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CertifiedTemporalError {
    /// Input is not a JSON object with a string schema.
    Malformed(String),
    /// The certificate schema has no Certified Trust consumer.
    UnsupportedSchema(String),
    /// Embedded spec bytes differ from the expected semantic input.
    SpecSourceMismatch,
    /// Init/Next/constants differ from the expected checker configuration.
    ConfigBindingMismatch { expected: String, found: String },
    /// Property or measure identity differs from the expected claim.
    PropertyBindingMismatch { expected: String, found: String },
    /// A producer or independent checker declined the fragment.
    Declined(String),
}

impl std::fmt::Display for CertifiedTemporalError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Malformed(detail) => {
                write!(formatter, "malformed temporal certificate: {detail}")
            }
            Self::UnsupportedSchema(schema) => {
                write!(formatter, "unsupported temporal certificate schema `{schema}`")
            }
            Self::SpecSourceMismatch => {
                formatter.write_str("temporal certificate spec_src does not byte-match the claim")
            }
            Self::ConfigBindingMismatch { expected, found } => write!(
                formatter,
                "temporal configuration binding mismatch: expected {expected}; found {found}"
            ),
            Self::PropertyBindingMismatch { expected, found } => write!(
                formatter,
                "temporal property binding mismatch: expected {expected}; found {found}"
            ),
            Self::Declined(detail) => {
                write!(formatter, "temporal certificate replay declined: {detail}")
            }
        }
    }
}

impl std::error::Error for CertifiedTemporalError {}

fn schema(raw: &str) -> Result<String, CertifiedTemporalError> {
    let value: serde_json::Value = serde_json::from_str(raw)
        .map_err(|error| CertifiedTemporalError::Malformed(error.to_string()))?;
    value
        .get("schema")
        .and_then(serde_json::Value::as_str)
        .map(ToOwned::to_owned)
        .ok_or_else(|| CertifiedTemporalError::Malformed("missing string `schema`".to_owned()))
}

/// Independently replay a kernel certificate and bind it to exact expected
/// semantic inputs.
///
/// Safety accepts only an unbounded invariant proof or a finite explicit
/// fixpoint with complete, matched `Init` and `Next` completeness pairs. Merely
/// rechecking membership legs over a producer-enumerated set is not Certified
/// authority. The older scalar closed theorem remains available through
/// [`crate::certify_model`]. Liveness accepts only ty's solver-free countdown
/// lane; the enumerator-assisted explicit-state and AY-only schemas are not
/// promoted here.
pub fn recheck_certified_temporal_evidence(
    raw: &str,
    expected_spec_src: &str,
    expected_config_src: &str,
    expected_properties: &[&str],
    expected_measure: Option<&str>,
) -> Result<CertifiedTemporalEvidence, CertifiedTemporalError> {
    let _ty_transaction = crate::in_process_ty_transaction_lock();
    let (expected_config, expected_init, expected_next) =
        resolved_config(expected_spec_src, expected_config_src)?;
    let certificate_schema = schema(raw)?;
    match certificate_schema.as_str() {
        "ty.cert/v1" => {
            let certificate = tla_check::cert::SafetyCertificate::from_json(raw)
                .map_err(CertifiedTemporalError::Malformed)?;
            if certificate.spec_src != expected_spec_src {
                return Err(CertifiedTemporalError::SpecSourceMismatch);
            }
            let expected =
                expected_properties.iter().map(|name| (*name).to_owned()).collect::<Vec<_>>();
            if certificate.invariants != expected {
                return Err(CertifiedTemporalError::PropertyBindingMismatch {
                    expected: format!("invariants {expected:?}"),
                    found: format!("invariants {:?}", certificate.invariants),
                });
            }
            let mut expected_constants = expected_config
                .constants
                .iter()
                .map(|(name, value)| (name.clone(), value.clone()))
                .collect::<Vec<_>>();
            expected_constants.sort_by(|left, right| left.0.cmp(&right.0));
            if certificate.init.as_deref() != Some(expected_init.as_str())
                || certificate.next.as_deref() != Some(expected_next.as_str())
                || certificate.constants != expected_constants
            {
                return Err(CertifiedTemporalError::ConfigBindingMismatch {
                    expected: format!(
                        "Init={expected_init:?}, Next={expected_next:?}, constants={expected_constants:?}"
                    ),
                    found: format!(
                        "Init={:?}, Next={:?}, constants={:?}",
                        certificate.init, certificate.next, certificate.constants
                    ),
                });
            }
            if expected_measure.is_some() {
                return Err(CertifiedTemporalError::PropertyBindingMismatch {
                    expected: "no safety measure".to_owned(),
                    found: format!("measure {expected_measure:?}"),
                });
            }
            let authority = crate::certified_explicit_fixpoint_authority(&certificate)
                .map_err(CertifiedTemporalError::Declined)?;
            let report = tla_check::cert::verify_safety_certificate(&certificate);
            if !matches!(report.verdict, tla_check::cert::CertVerdict::Accepted)
                || report.kernel_recheck != Some(true)
            {
                return Err(CertifiedTemporalError::Declined(report.detail));
            }
            Ok(CertifiedTemporalEvidence {
                schema: CERTIFIED_TEMPORAL_EVIDENCE_SCHEMA_V1.to_owned(),
                property_class: CertifiedTemporalPropertyClass::AlwaysSafety,
                certificate_schema,
                spec_src: certificate.spec_src,
                config_src: expected_config_src.to_owned(),
                properties: certificate.invariants,
                measure: None,
                recheck_detail: format!("{authority}; {}", report.detail),
                raw_certificate_json: raw.to_owned(),
            })
        }
        "ty.live-free-cert/v1" => {
            let certificate = tla_check::live_cert::LivenessFreeCert::from_json(raw)
                .map_err(CertifiedTemporalError::Malformed)?;
            bind_liveness(
                &certificate.spec_src,
                &certificate.property_op,
                &certificate.measure_op,
                expected_spec_src,
                expected_properties,
                expected_measure,
            )?;
            bind_liveness_config(
                certificate.init.as_deref(),
                certificate.next.as_deref(),
                &expected_config,
                &expected_init,
                &expected_next,
            )?;
            let report = tla_check::live_cert::verify_liveness_free(&certificate);
            if !matches!(report.verdict, tla_check::live_cert::LiveExplicitVerdict::Accepted) {
                return Err(CertifiedTemporalError::Declined(report.detail));
            }
            Ok(liveness_evidence(
                certificate_schema,
                certificate.spec_src,
                certificate.property_op,
                certificate.measure_op,
                report.detail,
                raw,
                expected_config_src,
            ))
        }
        "ty.live-explicit-cert/v1" => Err(CertifiedTemporalError::Declined(
            "ty.live-explicit-cert/v1 is enumerator-assisted and cannot authorize Certified \
             liveness; use the solver-free ty.live-free-cert/v1 lane"
                .to_owned(),
        )),
        other => Err(CertifiedTemporalError::UnsupportedSchema(other.to_owned())),
    }
}

fn resolved_config(
    spec_src: &str,
    config_src: &str,
) -> Result<(tla_check::Config, String, String), CertifiedTemporalError> {
    let config = tla_check::Config::parse(config_src)
        .map_err(|error| CertifiedTemporalError::Malformed(format!("{error:?}")))?;
    if !config.module_overrides.is_empty()
        || !config.module_assignments.is_empty()
        || !config.constraints.is_empty()
        || !config.action_constraints.is_empty()
    {
        return Err(CertifiedTemporalError::ConfigBindingMismatch {
            expected:
                "plain Init/Next semantics without module overrides or state/action constraints"
                    .to_owned(),
            found: format!(
                "module_overrides={:?}, module_assignments={:?}, constraints={:?}, action_constraints={:?}",
                config.module_overrides,
                config.module_assignments,
                config.constraints,
                config.action_constraints
            ),
        });
    }
    let tree = tla_core::parse_to_syntax_tree(spec_src);
    let resolved = tla_check::resolve_spec_from_config(&config, &tree)
        .map_err(|error| CertifiedTemporalError::Declined(error.to_string()))?;
    if resolved.next_node.is_some() {
        return Err(CertifiedTemporalError::Declined(
            "inline Next expressions are not certificate operator identities".to_owned(),
        ));
    }
    let init = resolved.init;
    let next = resolved.next;
    Ok((config, init, next))
}

fn bind_liveness_config(
    certificate_init: Option<&str>,
    certificate_next: Option<&str>,
    expected_config: &tla_check::Config,
    expected_init: &str,
    expected_next: &str,
) -> Result<(), CertifiedTemporalError> {
    // The current kernel liveness schemas carry operator identities but no
    // constant environment.  Accepting a configured constant would therefore
    // claim a semantic binding the independent verifier cannot reconstruct.
    if !expected_config.constants.is_empty() {
        return Err(CertifiedTemporalError::ConfigBindingMismatch {
            expected: format!(
                "constant-free liveness config, found {:?}",
                expected_config.constants
            ),
            found: "liveness certificate schema has no constant carrier".to_owned(),
        });
    }
    if certificate_init != Some(expected_init) || certificate_next != Some(expected_next) {
        return Err(CertifiedTemporalError::ConfigBindingMismatch {
            expected: format!("Init={expected_init:?}, Next={expected_next:?}"),
            found: format!("Init={certificate_init:?}, Next={certificate_next:?}"),
        });
    }
    Ok(())
}

fn bind_liveness(
    spec_src: &str,
    property: &str,
    measure: &str,
    expected_spec_src: &str,
    expected_properties: &[&str],
    expected_measure: Option<&str>,
) -> Result<(), CertifiedTemporalError> {
    if spec_src != expected_spec_src {
        return Err(CertifiedTemporalError::SpecSourceMismatch);
    }
    let expected_property = match expected_properties {
        [property] => *property,
        properties => {
            return Err(CertifiedTemporalError::PropertyBindingMismatch {
                expected: "exactly one liveness property".to_owned(),
                found: format!("{properties:?}"),
            });
        }
    };
    if property != expected_property || expected_measure != Some(measure) {
        return Err(CertifiedTemporalError::PropertyBindingMismatch {
            expected: format!("property {expected_property:?}, measure {expected_measure:?}"),
            found: format!("property {property:?}, measure {measure:?}"),
        });
    }
    Ok(())
}

fn liveness_evidence(
    certificate_schema: String,
    spec_src: String,
    property: String,
    measure: String,
    detail: String,
    raw: &str,
    config_src: &str,
) -> CertifiedTemporalEvidence {
    CertifiedTemporalEvidence {
        schema: CERTIFIED_TEMPORAL_EVIDENCE_SCHEMA_V1.to_owned(),
        property_class: CertifiedTemporalPropertyClass::EventuallyUnderWeakFairness,
        certificate_schema,
        spec_src,
        config_src: config_src.to_owned(),
        properties: vec![property],
        measure: Some(measure),
        recheck_detail: detail,
        raw_certificate_json: raw.to_owned(),
    }
}

/// Produce and immediately replay a kernel liveness certificate.
///
/// Only the solver-free countdown lane can authorize Certified liveness. It
/// proves `◇P` conditionally under weak fairness of `Next` and fails closed
/// outside its recognized fragment; the enumerator-assisted explicit-state
/// fallback is deliberately not promoted.
pub fn certify_liveness_with_ty(
    spec_src: &str,
    config_src: &str,
    property_op: &str,
    measure_op: &str,
) -> Result<CertifiedTemporalEvidence, CertifiedTemporalError> {
    let _ty_transaction = crate::in_process_ty_transaction_lock();
    let mut config = tla_check::Config::parse(config_src)
        .map_err(|error| CertifiedTemporalError::Malformed(format!("{error:?}")))?;
    let tree = tla_core::parse_to_syntax_tree(spec_src);
    let resolved = tla_check::resolve_spec_from_config(&config, &tree)
        .map_err(|error| CertifiedTemporalError::Declined(error.to_string()))?;
    if resolved.next_node.is_some() {
        return Err(CertifiedTemporalError::Declined(
            "inline Next expressions are not certificate operator identities".to_owned(),
        ));
    }
    config.init = Some(resolved.init);
    config.next = Some(resolved.next);

    let raw = if let Some(certificate) =
        tla_check::live_cert::certify_liveness_free(spec_src, &config, property_op, measure_op)
    {
        certificate.to_json()
    } else {
        return Err(CertifiedTemporalError::Declined(
            "the solver-free liveness certificate lane declined; the explicit-state fallback is \
             enumerator-assisted and cannot authorize Certified liveness"
                .to_owned(),
        ));
    };
    recheck_certified_temporal_evidence(
        &raw,
        spec_src,
        config_src,
        &[property_op],
        Some(measure_op),
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    const COUNTDOWN: &str = "---- MODULE Countdown ----\n\
VARIABLE x\n\
Init == x = 4\n\
Next == x > 0 /\\ x' = x - 1\n\
Reaches == <>(x = 0)\n\
Measure == x\n\
Spec == Init /\\ [][Next]_x /\\ WF_x(Next)\n\
====\n";

    const CONFIG: &str = "SPECIFICATION Spec\nCHECK_DEADLOCK FALSE\n";

    #[test]
    fn countdown_liveness_is_kernel_replayed_and_exactly_bound() {
        let evidence = certify_liveness_with_ty(COUNTDOWN, CONFIG, "Reaches", "Measure")
            .expect("countdown must certify");
        assert_eq!(
            evidence.property_class,
            CertifiedTemporalPropertyClass::EventuallyUnderWeakFairness
        );
        assert_eq!(evidence.spec_src, COUNTDOWN);
        assert_eq!(evidence.properties, ["Reaches"]);
        assert_eq!(evidence.measure.as_deref(), Some("Measure"));

        assert!(matches!(
            recheck_certified_temporal_evidence(
                &evidence.raw_certificate_json,
                &format!("{COUNTDOWN}\n"),
                CONFIG,
                &["Reaches"],
                Some("Measure")
            ),
            Err(CertifiedTemporalError::SpecSourceMismatch)
        ));
        assert!(matches!(
            recheck_certified_temporal_evidence(
                &evidence.raw_certificate_json,
                COUNTDOWN,
                CONFIG,
                &["Other"],
                Some("Measure")
            ),
            Err(CertifiedTemporalError::PropertyBindingMismatch { .. })
        ));
        assert!(matches!(
            recheck_certified_temporal_evidence(
                &evidence.raw_certificate_json,
                COUNTDOWN,
                "INIT Init\nNEXT Next\nCONSTANT Unbound = 1\nCHECK_DEADLOCK FALSE\n",
                &["Reaches"],
                Some("Measure")
            ),
            Err(CertifiedTemporalError::ConfigBindingMismatch { .. })
        ));
    }

    /// SAFETY-class scope of the S4 finite-fragment routing: liveness/fairness
    /// is a SEPARATE lane from the multi-variable safety finite keystone. It
    /// produces a distinct evidence type (`◇`-under-weak-fairness bound to a
    /// measure operator), never a finite safety certificate — and a `□`-only
    /// safety `Model` has no liveness/fairness field, so nothing can smuggle a
    /// liveness obligation into `crate::certify_model`'s finite dispatch. A
    /// liveness obligation therefore never routes to the finite keystone.
    #[test]
    fn liveness_lane_is_never_routed_to_the_finite_safety_keystone() {
        let evidence = certify_liveness_with_ty(COUNTDOWN, CONFIG, "Reaches", "Measure")
            .expect("the solver-free countdown liveness certificate must kernel-replay");
        assert_eq!(
            evidence.property_class,
            CertifiedTemporalPropertyClass::EventuallyUnderWeakFairness
        );
        assert!(evidence.measure.is_some(), "liveness carries a measure operator");
        assert!(
            !evidence.recheck_detail.contains("finite keystone"),
            "liveness evidence must never carry a finite safety discharge: {}",
            evidence.recheck_detail
        );
    }

    #[test]
    fn enumerator_assisted_live_explicit_certificate_is_never_promoted() {
        // This test intentionally calls pinned-TY producer/verifier APIs
        // directly. Keep that semantic-input transaction under the same guard
        // as the public Trust entry points: the Rust test harness runs sibling
        // producer tests concurrently, while TY retains run-scoped state.
        let _ty_transaction = crate::in_process_ty_transaction_lock();
        let mut config = tla_check::Config::parse(CONFIG).expect("countdown config parses");
        let tree = tla_core::parse_to_syntax_tree(COUNTDOWN);
        let resolved = tla_check::resolve_spec_from_config(&config, &tree)
            .expect("countdown Init/Next resolve");
        config.init = Some(resolved.init);
        config.next = Some(resolved.next);
        let certificate = tla_check::live_cert::certify_liveness_explicit(
            COUNTDOWN, &config, "Reaches", "Measure",
        )
        .expect("regression fixture has a valid explicit-state liveness certificate");
        let raw = certificate.to_json();
        let report = tla_check::live_cert::verify_liveness_explicit(&certificate);
        assert!(matches!(report.verdict, tla_check::live_cert::LiveExplicitVerdict::Accepted));

        let error = recheck_certified_temporal_evidence(
            &raw,
            COUNTDOWN,
            CONFIG,
            &["Reaches"],
            Some("Measure"),
        )
        .unwrap_err();
        assert!(
            matches!(error, CertifiedTemporalError::Declined(ref detail)
                if detail.contains("enumerator-assisted")
                    && detail.contains("ty.live-free-cert/v1")),
            "unexpected result: {error:?}"
        );
    }
}
