//! Authenticated native resource observations, separate from every proof DTO.
use std::collections::BTreeSet;
use std::io;
use std::path::Path;

use serde::Serialize;
use trust_types::native_admission::NativeAdmissionCensus;

use crate::pipeline::transport::CargoTargetIdentity;

pub(crate) const FILE_NAME: &str = "compiler-admission.json";

#[derive(Clone, Debug, Serialize)]
pub(crate) struct Observation {
    pub(crate) cargo_target: CargoTargetIdentity,
    pub(crate) census: NativeAdmissionCensus,
}

#[derive(Debug, Serialize)]
pub(crate) struct Report {
    schema: &'static str,
    authority: &'static str,
    scope: &'static str,
    external_solver: &'static str,
    availability: &'static str,
    expected_units: Vec<CargoTargetIdentity>,
    units: Vec<Observation>,
    problems: Vec<String>,
}

impl Report {
    pub(crate) fn new(
        expected: &BTreeSet<CargoTargetIdentity>,
        completed: &BTreeSet<CargoTargetIdentity>,
        units: Vec<Observation>,
        mut problems: Vec<String>,
    ) -> Self {
        let mut seen = BTreeSet::new();
        for unit in &units {
            if !expected.contains(&unit.cargo_target) || !seen.insert(unit.cargo_target.clone()) {
                problems.push("unknown or duplicate native admission unit".into());
            }
            if let Err(error) = unit.census.validate() {
                problems.push(error);
            }
            if !unit.census.complete {
                problems.push("native admission unit did not close".into());
            }
        }
        for target in expected.difference(completed) {
            problems.push(format!(
                "native admission unit has no completed compiler artifact: {}",
                target.report_label()
            ));
        }
        for target in expected.difference(&seen) {
            problems.push(format!("missing native admission census: {}", target.report_label()));
        }
        if expected.is_empty() {
            problems.push("no authenticated Cargo native-unit population".into());
        }
        Self {
            schema: "trust.compiler-native-admission.v1",
            authority: "authenticated_correlation_not_proof_or_process_attestation",
            scope: "native_verification_only_not_prestart_admission_or_rss_cap",
            external_solver: "incomplete_separate_binary_namespace",
            availability: if problems.is_empty() { "complete" } else { "incomplete" },
            expected_units: expected.iter().cloned().collect(),
            units,
            problems,
        }
    }

    pub(crate) fn write(&self, root: &Path, canonical: &[u8]) -> io::Result<()> {
        #[derive(Serialize)]
        struct Bound<'a> {
            proof_report_hash: String,
            #[serde(flatten)]
            report: &'a Report,
        }
        let bound = Bound {
            proof_report_hash: format!(
                "sha256:{}",
                trust_types::digest::stable_sha256_hex(canonical)
            ),
            report: self,
        };
        let mut bytes = serde_json::to_vec_pretty(&bound).map_err(io::Error::other)?;
        bytes.push(b'\n');
        // This artifact is part of the transaction. A failure cannot silently
        // retain a prior run's resource claim or turn missing data into success.
        std::fs::write(root.join(FILE_NAME), bytes)
    }
}

pub(crate) fn authenticate(
    census: &NativeAdmissionCensus,
    target: &CargoTargetIdentity,
    session: &str,
) -> Result<(), String> {
    census.validate()?;
    let b = &census.binding;
    if b.run_digest != trust_types::native_admission::run_digest(session)
        || b.unit_digest != target.unit_identity_sha256
        || b.semantics_digest != target.semantics_sha256
        || b.role != target.proof_unit_role
        || b.target != target.compile_target
        || census.package_name != target.package_name
        || census.crate_name != target.crate_name()
    {
        return Err("native admission claims do not match authenticated Cargo run/unit".into());
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use trust_types::native_admission::*;

    use super::*;

    fn target() -> CargoTargetIdentity {
        CargoTargetIdentity {
            package_id: "path+file:///fixture#demo@1.0.0".into(),
            package_name: "demo".into(),
            target_name: "demo".into(),
            target_kinds: vec!["lib".into()],
            compile_target: "aarch64-apple-darwin".into(),
            compile_mode: "check".into(),
            compile_kind: "host".into(),
            unit_identity_sha256: "a".repeat(64),
            compile_target_spec_sha256: None,
            proof_unit_index: 1,
            proof_unit_mode: "check".into(),
            proof_unit_role: "primary".into(),
            semantics_sha256: "b".repeat(64),
        }
    }

    fn census() -> NativeAdmissionCensus {
        let binding = NativeAdmissionBinding {
            run_digest: run_digest("secret"),
            unit_digest: "a".repeat(64),
            semantics_digest: "b".repeat(64),
            role: "primary".into(),
            target: "aarch64-apple-darwin".into(),
        };
        let body = NativeAdmissionBody { function: "demo::f".into(), body_digest: "c".repeat(64) };
        NativeAdmissionCensus {
            transport_type: None,
            schema: SCHEMA.into(),
            package_name: "demo".into(),
            crate_name: "demo".into(),
            attempts: vec![NativeAdmissionAttempt {
                work_digest: work_digest(&binding, &body),
                request_digest: body.body_digest.clone(),
                body: body.clone(),
                attempt: 1,
                outcome: NativeAdmissionOutcome::CacheReuse,
                terminal: true,
            }],
            binding,
            bodies: vec![body],
            auxiliary_bodies: vec![],
            complete: true,
            problems: vec![],
        }
    }

    #[test]
    fn joined_unit_is_accepted_and_stale_or_swapped_bindings_are_rejected() {
        let c = census();
        let t = target();
        authenticate(&c, &t, "secret").unwrap();
        assert!(authenticate(&c, &t, "stale").is_err());
        for mutation in 0..4 {
            let mut wrong = t.clone();
            match mutation {
                0 => wrong.unit_identity_sha256 = "d".repeat(64),
                1 => wrong.semantics_sha256 = "d".repeat(64),
                2 => wrong.proof_unit_role = "test-execution".into(),
                _ => wrong.compile_target = "aarch64-unknown-linux-gnu".into(),
            }
            assert!(authenticate(&c, &wrong, "secret").is_err());
        }
    }

    #[test]
    fn no_terminal_or_missing_duplicate_census_is_never_complete() {
        let t = target();
        let expected = BTreeSet::from([t.clone()]);
        let observation = Observation { cargo_target: t, census: census() };
        assert_eq!(
            Report::new(&expected, &expected, vec![observation.clone()], vec![]).availability,
            "complete"
        );
        assert_eq!(
            Report::new(&expected, &BTreeSet::new(), vec![observation.clone()], vec![])
                .availability,
            "incomplete"
        );
        assert_eq!(Report::new(&expected, &expected, vec![], vec![]).availability, "incomplete");
        assert_eq!(
            Report::new(&expected, &expected, vec![observation.clone(), observation], vec![])
                .availability,
            "incomplete"
        );
    }

    #[test]
    fn required_resource_write_failure_is_returned() {
        let root = tempfile::tempdir().unwrap();
        std::fs::create_dir(root.path().join(FILE_NAME)).unwrap();
        let report = Report::new(&BTreeSet::new(), &BTreeSet::new(), vec![], vec![]);
        assert!(report.write(root.path(), b"canonical").is_err());
    }

    #[test]
    fn custom_target_path_is_checked_as_part_of_exact_unit_identity() {
        let mut c = census();
        let mut t = target();
        c.binding.target = "/fixture/custom.json".into();
        t.compile_target = c.binding.target.clone();
        t.compile_target_spec_sha256 = Some("e".repeat(64));
        authenticate(&c, &t, "secret").unwrap();
        t.compile_target = "/other/custom.json".into();
        assert!(authenticate(&c, &t, "secret").is_err());
    }
}
