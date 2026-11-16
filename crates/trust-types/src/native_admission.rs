//! Compiler-native cooperative admission accounting. This is resource evidence,
//! never a proof capability or an enforced compiler-process RSS limit.

use std::collections::BTreeSet;

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

pub const SCHEMA: &str = "trust.native-admission-census.v1";
pub const RUN_DOMAIN: &[u8] = b"trust.native-admission.run.v1\0";

pub fn valid_digest(value: &str) -> bool {
    value.len() == 64 && value.bytes().all(|c| c.is_ascii_digit() || (b'a'..=b'f').contains(&c))
}

/// Public correlation only. Never send the private verification nonce to trustd.
pub fn run_digest(session: &str) -> String {
    let mut hash = Sha256::new();
    hash.update(RUN_DOMAIN);
    hash.update(session.as_bytes());
    crate::digest::lowercase_hex(&hash.finalize())
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeAdmissionBinding {
    pub run_digest: String,
    pub unit_digest: String,
    pub semantics_digest: String,
    /// Cargo's graph role, including `test-execution`, not the compiler's coarser role.
    pub role: String,
    pub target: String,
}

impl NativeAdmissionBinding {
    pub fn validate(&self) -> Result<(), String> {
        if ![&self.run_digest, &self.unit_digest, &self.semantics_digest]
            .into_iter()
            .all(|d| valid_digest(d))
            || !matches!(self.role.as_str(), "primary" | "test-execution" | "dependency")
            || self.target.is_empty()
            || self.target.len() > 4096
        {
            return Err("invalid native admission run/unit binding".into());
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeAdmissionBody {
    pub function: String,
    /// Hash of the compiler-owned DefPathHash, independent of its display name.
    pub body_digest: String,
}

pub fn work_digest(binding: &NativeAdmissionBinding, body: &NativeAdmissionBody) -> String {
    request_work_digest(binding, body, &body.body_digest)
}

pub fn request_work_digest(
    binding: &NativeAdmissionBinding,
    body: &NativeAdmissionBody,
    request: &str,
) -> String {
    let mut hash = Sha256::new();
    hash.update(b"trust.native-admission.work.v1\0");
    for value in [
        binding.run_digest.as_str(),
        binding.unit_digest.as_str(),
        binding.semantics_digest.as_str(),
        body.body_digest.as_str(),
        body.function.as_str(),
        request,
    ] {
        hash.update((value.len() as u64).to_le_bytes());
        hash.update(value.as_bytes());
    }
    crate::digest::lowercase_hex(&hash.finalize())
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct AdmissionDaemonIdentity {
    pub version: String,
    pub protocol: String,
    pub release: String,
    pub commit: String,
    pub executable_sha256: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct AdmissionAuthority {
    pub version: String,
    pub daemon: AdmissionDaemonIdentity,
    pub incarnation: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct AdmissionWorkClaim {
    pub run_digest: String,
    pub unit_digest: String,
    pub semantics_digest: String,
    pub work_digest: String,
    pub kind: String,
    pub attempt: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct AdmissionGrantObservation {
    pub version: String,
    pub authority: AdmissionAuthority,
    pub token: u64,
    pub bytes: u64,
    pub budget_at_grant_bytes: u64,
    pub reserved_before_bytes: u64,
    pub reserved_after_bytes: u64,
    pub grant_sequence: u64,
    pub work: AdmissionWorkClaim,
}

/// A closed wire view of the coordinator's immutable receipt. Parsing it does
/// not authenticate a grant; the enclosing compiler/Cargo join is mandatory.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeAdmissionReceipt {
    pub version: String,
    pub client_budget_at_preflight_bytes: u64,
    pub daemon_budget_at_preflight_bytes: u64,
    pub grant: AdmissionGrantObservation,
}

impl NativeAdmissionReceipt {
    pub fn validate(
        &self,
        binding: &NativeAdmissionBinding,
        work: &str,
        attempt: u64,
    ) -> Result<(), String> {
        let grant = &self.grant;
        let authority = &grant.authority;
        let daemon = &authority.daemon;
        if self.version != "trustd.admission-receipt.v1"
            || grant.version != "trustd.admission-grant.v1"
            || authority.version != "trustd.admission-identity.v1"
            || daemon.version != "trustd.identity.v1"
            || daemon.protocol != "trustd.status.v1"
            || daemon.release.is_empty()
            || daemon.commit.is_empty()
            || !valid_digest(&daemon.executable_sha256)
            || !valid_digest(&authority.incarnation)
            || authority.incarnation.bytes().all(|b| b == b'0')
            || grant.token == 0
            || grant.bytes == 0
            || grant.grant_sequence == 0
            || grant.reserved_before_bytes.checked_add(grant.bytes)
                != Some(grant.reserved_after_bytes)
            || grant.reserved_after_bytes > grant.budget_at_grant_bytes
            || grant.budget_at_grant_bytes == 0
            || grant.budget_at_grant_bytes > self.daemon_budget_at_preflight_bytes
            || self.daemon_budget_at_preflight_bytes > self.client_budget_at_preflight_bytes
            || grant.work.run_digest != binding.run_digest
            || grant.work.unit_digest != binding.unit_digest
            || grant.work.semantics_digest != binding.semantics_digest
            || grant.work.work_digest != work
            || grant.work.attempt != attempt
            || grant.work.kind != "native_verification"
        {
            return Err("invalid or misbound native admission receipt".into());
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "state", rename_all = "snake_case", deny_unknown_fields)]
pub enum NativeAdmissionOutcome {
    Admitted {
        receipt: Box<NativeAdmissionReceipt>,
    },
    Refused {
        reason: String,
    },
    CacheReuse,
    CachedAbsence,
    PolicySkipped,
    DumpOnly,
    /// Work returned before the real native scheduling boundary. No grant is implied.
    BeforeScheduling,
    /// A compiler-owned pre-pass outcome (tainted or no executable path).
    EarlyOut {
        reason: String,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeAdmissionAttempt {
    pub body: NativeAdmissionBody,
    pub work_digest: String,
    /// Digest of the concrete instance/promoted-body and effective collection request.
    pub request_digest: String,
    pub attempt: u64,
    pub outcome: NativeAdmissionOutcome,
    /// Set only when the collection scope returned; unwinding leaves it false.
    pub terminal: bool,
}

/// Exactly one per native compiler unit. Completeness concerns only this
/// resource population, not proofs, process RSS, pre-start admission or binaries.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeAdmissionCensus {
    /// Consumes the surrounding transport tag during direct typed parsing;
    /// never serializes a second tag or buffers duplicate keys through Value.
    #[serde(rename = "type", default, skip_serializing)]
    pub transport_type: Option<String>,
    pub schema: String,
    pub binding: NativeAdmissionBinding,
    pub package_name: String,
    pub crate_name: String,
    pub bodies: Vec<NativeAdmissionBody>,
    /// Collections demanded while checking a root (for example a callee query).
    /// These belong to this unit's resource work, not its coverage denominator.
    pub auxiliary_bodies: Vec<NativeAdmissionBody>,
    pub attempts: Vec<NativeAdmissionAttempt>,
    pub complete: bool,
    pub problems: Vec<String>,
}

impl NativeAdmissionCensus {
    pub fn validate(&self) -> Result<(), String> {
        self.binding.validate()?;
        if self.transport_type.as_deref().is_some_and(|t| t != "native_admission_census")
            || self.schema != SCHEMA
            || self.package_name.is_empty()
            || self.package_name.len() > 4096
            || self.crate_name.is_empty()
            || self.crate_name.len() > 4096
        {
            return Err("invalid native admission census schema/scope".into());
        }
        if self.complete != self.problems.is_empty() {
            return Err("native admission completeness contradicts its problems".into());
        }
        let mut bodies = BTreeSet::new();
        for body in self.bodies.iter().chain(&self.auxiliary_bodies) {
            if body.function.is_empty() || !valid_digest(&body.body_digest) || !bodies.insert(body)
            {
                return Err("invalid or duplicate native body inventory".into());
            }
        }
        if self.bodies.windows(2).any(|w| w[0] >= w[1])
            || self.auxiliary_bodies.windows(2).any(|w| w[0] >= w[1])
        {
            return Err("native body inventory is not canonical".into());
        }
        let mut keys = BTreeSet::new();
        let mut next_attempt = std::collections::BTreeMap::new();
        let mut seen = BTreeSet::new();
        let mut grants = BTreeSet::new();
        let mut sequences = BTreeSet::new();
        let mut authority = None;
        for row in &self.attempts {
            if !bodies.contains(&row.body)
                || row.attempt == 0
                || !valid_digest(&row.request_digest)
                || row.work_digest
                    != request_work_digest(&self.binding, &row.body, &row.request_digest)
                || !keys.insert((&row.work_digest, row.attempt))
            {
                return Err("unknown, duplicated or misbound native work attempt".into());
            }
            let expected = next_attempt.entry(&row.body).or_insert(1);
            if row.attempt != *expected {
                return Err("native admission attempt sequence has a gap or reordering".into());
            }
            *expected = expected
                .checked_add(1)
                .ok_or_else(|| "native admission attempt sequence exhausted".to_string())?;
            seen.insert(&row.body);
            if self.complete && !row.terminal {
                return Err("complete native admission census contains unclosed work".into());
            }
            match &row.outcome {
                NativeAdmissionOutcome::Admitted { receipt } => {
                    receipt.validate(&self.binding, &row.work_digest, row.attempt)?;
                    let grant = &receipt.grant;
                    if authority.as_ref().is_some_and(|a| *a != &grant.authority) {
                        return Err("native admission daemon changed within one unit".into());
                    }
                    authority = Some(&grant.authority);
                    if !grants.insert((&grant.authority.incarnation, grant.token))
                        || !sequences.insert((&grant.authority.incarnation, grant.grant_sequence))
                    {
                        return Err("replayed native admission grant".into());
                    }
                }
                NativeAdmissionOutcome::Refused { reason }
                | NativeAdmissionOutcome::EarlyOut { reason }
                    if reason.is_empty() =>
                {
                    return Err("native admission outcome omitted reason".into());
                }
                _ => {}
            }
        }
        if self.complete && seen != bodies {
            return Err("complete native admission census omitted a body".into());
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    pub fn census() -> NativeAdmissionCensus {
        let binding = NativeAdmissionBinding {
            run_digest: run_digest("nonce"),
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
            bodies: vec![body.clone()],
            auxiliary_bodies: vec![],
            attempts: vec![NativeAdmissionAttempt {
                work_digest: work_digest(&binding, &body),
                request_digest: body.body_digest.clone(),
                body,
                attempt: 1,
                outcome: NativeAdmissionOutcome::CacheReuse,
                terminal: true,
            }],
            binding,
            complete: true,
            problems: vec![],
        }
    }

    #[test]
    fn census_scope_names_are_bounded_for_an_incomplete_producer_fallback() {
        let mut value = census();
        value.package_name = "p".repeat(4097);
        assert!(value.validate().is_err());
        value.package_name = "demo".into();
        value.crate_name = "c".repeat(4097);
        assert!(value.validate().is_err());
    }

    #[test]
    fn complete_inventory_and_terminal_are_both_required() {
        let good = census();
        good.validate().unwrap();
        let mut bad = good.clone();
        bad.attempts.clear();
        assert!(bad.validate().is_err());
        let mut bad = good.clone();
        bad.attempts[0].terminal = false;
        assert!(bad.validate().is_err());
        let mut bad = good.clone();
        bad.attempts.push(bad.attempts[0].clone());
        assert!(bad.validate().is_err());
        let mut bad = good;
        bad.binding.unit_digest = "d".repeat(64);
        assert!(bad.validate().is_err());
    }

    #[test]
    fn run_binding_is_domain_separated_and_contains_no_private_nonce() {
        let digest = run_digest("private nonce");
        assert!(valid_digest(&digest));
        assert_ne!(digest, run_digest("other nonce"));
        assert!(!serde_json::to_string(&census()).unwrap().contains("nonce"));
    }

    #[test]
    fn native_transport_rejects_unknown_and_duplicate_fields_without_value_normalization() {
        let json = serde_json::to_string(&crate::TransportMessage::NativeAdmissionCensus(census()))
            .unwrap();
        crate::parse_transport_payload(&json).unwrap();
        for bad in [
            json.replacen("\"schema\":", "\"unknown_root\":0,\"schema\":", 1),
            json.replacen("\"schema\":", "\"schema\":\"duplicate\",\"schema\":", 1),
            json.replacen("\"type\":", "\"type\":\"native_admission_census\",\"type\":", 1),
            json.replacen("\"unit_digest\":", "\"unit_digest\":\"duplicate\",\"unit_digest\":", 1),
        ] {
            assert!(crate::parse_transport_payload(&bad).is_err(), "{bad}");
        }
    }

    fn admitted() -> NativeAdmissionCensus {
        let mut c = census();
        let work = c.attempts[0].work_digest.clone();
        c.attempts[0].outcome = NativeAdmissionOutcome::Admitted {
            receipt: Box::new(NativeAdmissionReceipt {
                version: "trustd.admission-receipt.v1".into(),
                client_budget_at_preflight_bytes: 4096,
                daemon_budget_at_preflight_bytes: 2048,
                grant: AdmissionGrantObservation {
                    version: "trustd.admission-grant.v1".into(),
                    authority: AdmissionAuthority {
                        version: "trustd.admission-identity.v1".into(),
                        daemon: AdmissionDaemonIdentity {
                            version: "trustd.identity.v1".into(),
                            protocol: "trustd.status.v1".into(),
                            release: "test".into(),
                            commit: "test".into(),
                            executable_sha256: "d".repeat(64),
                        },
                        incarnation: "e".repeat(64),
                    },
                    token: 1,
                    bytes: 1024,
                    budget_at_grant_bytes: 2048,
                    reserved_before_bytes: 512,
                    reserved_after_bytes: 1536,
                    grant_sequence: 1,
                    work: AdmissionWorkClaim {
                        run_digest: c.binding.run_digest.clone(),
                        unit_digest: c.binding.unit_digest.clone(),
                        semantics_digest: c.binding.semantics_digest.clone(),
                        work_digest: work,
                        kind: "native_verification".into(),
                        attempt: 1,
                    },
                },
            }),
        };
        c
    }

    #[test]
    fn positive_grant_is_bound_to_the_exact_work_and_budget() {
        admitted().validate().unwrap();
        for mutation in 0..7 {
            let mut bad = admitted();
            let NativeAdmissionOutcome::Admitted { receipt } = &mut bad.attempts[0].outcome else {
                unreachable!()
            };
            match mutation {
                0 => receipt.grant.work.run_digest = "0".repeat(64),
                1 => receipt.grant.work.unit_digest = "0".repeat(64),
                2 => receipt.grant.work.semantics_digest = "0".repeat(64),
                3 => receipt.grant.work.work_digest = "0".repeat(64),
                4 => receipt.grant.work.attempt = 2,
                5 => receipt.grant.reserved_after_bytes += 1,
                _ => receipt.grant.budget_at_grant_bytes = 0,
            }
            assert!(bad.validate().is_err(), "mutation {mutation}");
        }
    }

    #[test]
    fn cloned_grant_and_changed_daemon_incarnation_do_not_authorize_a_retry() {
        let mut c = admitted();
        let mut retry = c.attempts[0].clone();
        retry.attempt = 2;
        // Merely copying a receipt cannot claim a second successful attempt.
        c.attempts.push(retry);
        assert!(c.validate().is_err());
        let NativeAdmissionOutcome::Admitted { receipt } = &mut c.attempts[1].outcome else {
            unreachable!()
        };
        receipt.grant.work.attempt = 2;
        assert!(c.validate().is_err()); // same grant token/sequence
        let NativeAdmissionOutcome::Admitted { receipt } = &mut c.attempts[1].outcome else {
            unreachable!()
        };
        receipt.grant.token = 2;
        receipt.grant.grant_sequence = 2;
        receipt.grant.authority.incarnation = "f".repeat(64);
        assert!(c.validate().is_err()); // another daemon within one unit
    }
}
