//! Opt-in cooperative admission observations. These are not proof capabilities,
//! authenticated Cargo identities, a terminal work census, or compiler RSS caps.
//!
//! The daemon echoes bounded caller correlation claims. A future authenticated
//! report transport must join those claims to its own exact run/unit/work before
//! using this observation; deserializing a receipt cannot establish that join.

use super::*;

pub const ADMISSION_IDENTITY_VERSION: &str = "trustd.admission-identity.v1";
pub const ADMISSION_REQUEST_VERSION: &str = "trustd.admission-request.v1";
pub const ADMISSION_GRANT_VERSION: &str = "trustd.admission-grant.v1";
pub const ADMISSION_RECEIPT_VERSION: &str = "trustd.admission-receipt.v1";
/// Evidence replies are much smaller than a full STATUS snapshot.
pub const MAX_ADMISSION_REPLY_BYTES: usize = 4096;
const MAX_IDENTITY_TEXT_BYTES: usize = 128;

/// What the caller says it is reserving for; the daemon does not authenticate it.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum AdmissionWorkKind {
    NativeVerification,
    ExternalSolver,
}

/// Public correlation claims, never a private session nonce. Digests are exactly
/// 64 lowercase hex characters. The unit digest must eventually be joined to the
/// authenticated full Cargo identity (including role, mode, target and semantics).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct AdmissionWork {
    pub run_digest: String,
    pub unit_digest: String,
    pub semantics_digest: String,
    pub work_digest: String,
    pub kind: AdmissionWorkKind,
    /// Positive caller attempt number. Only live duplicate claims are rejected;
    /// the daemon deliberately keeps no completed-work history.
    pub attempt: u64,
}

impl AdmissionWork {
    fn is_valid(&self) -> bool {
        self.attempt != 0
            && [&self.run_digest, &self.unit_digest, &self.semantics_digest, &self.work_digest]
                .into_iter()
                .all(|digest| valid_digest(digest))
    }
}

fn valid_digest(value: &str) -> bool {
    value.len() == 64
        && value.bytes().all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
}

/// Checked self-reported build identity plus a fresh OS-random daemon lifetime.
/// This does not upgrade the existing same-user endpoint checks to executable
/// attestation. The incarnation prevents token reuse across daemon restarts.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct AdmissionIdentity {
    pub version: String,
    pub daemon: DaemonIdentity,
    pub incarnation: String,
}

impl AdmissionIdentity {
    pub(super) fn fresh(daemon: DaemonIdentity) -> Option<Self> {
        Self::with_entropy(daemon, |bytes| trust_rand::try_fill_bytes(bytes).is_ok())
    }

    fn with_entropy(
        daemon: DaemonIdentity,
        entropy: impl FnOnce(&mut [u8]) -> bool,
    ) -> Option<Self> {
        let mut bytes = [0u8; 32];
        if !entropy(&mut bytes) {
            return None;
        }
        let incarnation = bytes.iter().map(|byte| format!("{byte:02x}")).collect();
        let value = Self { version: ADMISSION_IDENTITY_VERSION.to_string(), daemon, incarnation };
        value.is_valid().then_some(value)
    }

    pub(super) fn is_valid(&self) -> bool {
        self.version == ADMISSION_IDENTITY_VERSION
            && self.daemon.has_valid_invariants()
            && valid_digest(&self.daemon.executable_sha256)
            && self.daemon.release.len() <= MAX_IDENTITY_TEXT_BYTES
            && self.daemon.commit.len() <= MAX_IDENTITY_TEXT_BYTES
            && valid_digest(&self.incarnation)
            && self.incarnation.bytes().any(|byte| byte != b'0')
    }
}

#[derive(Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub(super) struct AdmissionRequest {
    version: String,
    pub(super) bytes: u64,
    pub(super) pid: u32,
    pub(super) work: AdmissionWork,
}

impl AdmissionRequest {
    pub(super) fn parse(value: &str) -> Option<Self> {
        let request: Self = serde_json::from_str(value).ok()?;
        (request.version == ADMISSION_REQUEST_VERSION
            && request.bytes > 0
            && request.pid > 0
            && request.pid <= i32::MAX as u32
            && request.work.is_valid())
        .then_some(request)
    }
}

/// Exact snapshot taken under the grant's ledger lock, after budget refresh.
/// `budget_at_grant_bytes` is cooperative capacity, not an enforced process RSS limit.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct AdmissionGrant {
    pub version: String,
    pub authority: AdmissionIdentity,
    pub token: u64,
    pub bytes: u64,
    pub budget_at_grant_bytes: u64,
    pub reserved_before_bytes: u64,
    pub reserved_after_bytes: u64,
    pub grant_sequence: u64,
    pub work: AdmissionWork,
}

impl AdmissionGrant {
    fn is_valid(&self) -> bool {
        self.version == ADMISSION_GRANT_VERSION
            && self.authority.is_valid()
            && self.token > 0
            && self.bytes > 0
            && self.budget_at_grant_bytes > 0
            && self.reserved_before_bytes.checked_add(self.bytes) == Some(self.reserved_after_bytes)
            && self.reserved_after_bytes <= self.budget_at_grant_bytes
            && self.grant_sequence > 0
            && self.work.is_valid()
    }
}

/// Retainable observation of a checked exchange, including the distinct
/// preflight upper bound and exact grant-time budget. Fields are private to keep
/// a live receipt immutable. Serialization is for later transport, not authority.
#[derive(Debug, Clone, Serialize)]
pub struct AdmissionReceipt {
    version: &'static str,
    client_budget_at_preflight_bytes: u64,
    daemon_budget_at_preflight_bytes: u64,
    grant: AdmissionGrant,
}

impl AdmissionReceipt {
    pub fn grant(&self) -> &AdmissionGrant {
        &self.grant
    }

    pub fn client_budget_at_preflight_bytes(&self) -> u64 {
        self.client_budget_at_preflight_bytes
    }

    pub fn daemon_budget_at_preflight_bytes(&self) -> u64 {
        self.daemon_budget_at_preflight_bytes
    }
}

/// A positive live reservation and its immutable receipt. Dropping it preserves
/// the ordinary reservation's release/EOF rules. A cloned receipt holds no bytes.
#[derive(Debug)]
pub struct EvidencedReservation {
    reservation: Reservation,
    receipt: AdmissionReceipt,
}

impl EvidencedReservation {
    pub fn receipt(&self) -> &AdmissionReceipt {
        &self.receipt
    }

    pub fn bytes(&self) -> u64 {
        self.reservation.bytes()
    }

    /// Separate retained data from the existing lifetime guard, e.g. to apply
    /// the external solver's child-lifetime handling. The receipt is inert.
    pub fn into_parts(self) -> (Reservation, AdmissionReceipt) {
        (self.reservation, self.receipt)
    }
}

impl Daemon {
    pub(super) fn admission_identity_line(&self) -> String {
        self.admission_identity
            .as_ref()
            .filter(|identity| identity.is_valid())
            .and_then(|identity| serde_json::to_string(identity).ok())
            .unwrap_or_else(|| "ERR evidence-unavailable".to_string())
    }

    pub(super) fn reserve_evidence(&self, rest: &str) -> ServerReply {
        let Some(request) = AdmissionRequest::parse(rest) else {
            return ServerReply::plain("ERR bad-evidence-request");
        };
        if !self.admission_identity.as_ref().is_some_and(AdmissionIdentity::is_valid) {
            return ServerReply::plain("ERR evidence-unavailable");
        }
        self.reserve_impl(request.bytes, request.pid, String::new(), Some(request.work))
    }
}

pub(super) fn requests_evidence_grant(verb: &str, rest: &str) -> bool {
    verb.eq_ignore_ascii_case("RESERVE_EVIDENCE") && AdmissionRequest::parse(rest).is_some()
}

pub(super) fn evidence_request_body(line: &str) -> Option<&str> {
    let trimmed = line.trim_end_matches(['\r', '\n']);
    if trimmed.len() > MAX_REQUEST_BYTES {
        return None;
    }
    let verb_end = trimmed.find(' ').unwrap_or(trimmed.len());
    trimmed[..verb_end]
        .eq_ignore_ascii_case("RESERVE_EVIDENCE")
        .then(|| trimmed[verb_end..].trim_start())
}

/// Opt in using the configured socket. No socket, disable, unsupported protocol,
/// malformed response or zero grant is an error; there is no legacy/file fallback.
#[cfg(unix)]
pub fn reserve_with_evidence(
    bytes: u64,
    expected: &DaemonIdentity,
    work: AdmissionWork,
) -> Result<EvidencedReservation, ReservationError> {
    if disabled() {
        return Err(evidence_error("TRUSTD_DISABLE cannot provide admission evidence"));
    }
    let sock = sock_path().map_err(ReservationError::Daemon)?.ok_or_else(|| {
        evidence_error("admission evidence requires a configured trustd socket authority")
    })?;
    reserve_with_evidence_at(&sock, bytes, expected, work)
}

/// Match the expected build identity and grant on the same checked endpoint
/// connection. `expected` is an identity expectation, not process attestation.
#[cfg(unix)]
pub fn reserve_with_evidence_at(
    sock: &Path,
    bytes: u64,
    expected: &DaemonIdentity,
    work: AdmissionWork,
) -> Result<EvidencedReservation, ReservationError> {
    reserve_at_with(sock, bytes, expected, work, OBSERVER_IO_TIMEOUT, machine_budget_bytes)
}

#[cfg(unix)]
fn evidence_error(message: impl Into<String>) -> ReservationError {
    ReservationError::Daemon(message.into())
}

#[cfg(unix)]
fn reserve_at_with(
    sock: &Path,
    bytes: u64,
    expected: &DaemonIdentity,
    work: AdmissionWork,
    observer_timeout: Duration,
    current_client_budget_at_preflight_bytes: impl FnOnce() -> u64,
) -> Result<EvidencedReservation, ReservationError> {
    reserve_at_with_timeouts(
        sock,
        bytes,
        expected,
        work,
        (observer_timeout, acquire_deadline().saturating_add(CLIENT_IO_MARGIN)),
        current_client_budget_at_preflight_bytes,
    )
}

#[cfg(unix)]
fn reserve_at_with_timeouts(
    sock: &Path,
    bytes: u64,
    expected: &DaemonIdentity,
    work: AdmissionWork,
    timeouts: (Duration, Duration),
    current_client_budget_at_preflight_bytes: impl FnOnce() -> u64,
) -> Result<EvidencedReservation, ReservationError> {
    let (observer_timeout, reservation_timeout) = timeouts;
    if bytes == 0 || !work.is_valid() || !expected.has_valid_invariants() {
        return Err(evidence_error(
            "invalid positive admission evidence request or expected identity",
        ));
    }
    let deadline = Instant::now().checked_add(observer_timeout).unwrap_or_else(Instant::now);
    let mut stream = connect_trusted_until_with_pid(sock, deadline, None).map_err(|error| {
        evidence_error(format!("could not connect for admission evidence: {error}"))
    })?;
    write_line_until(&mut stream, "ADMISSION_IDENTITY", deadline).map_err(|error| {
        evidence_error(format!("could not request admission identity: {error}"))
    })?;
    let identity = read_one_line_until_limited(&stream, deadline, MAX_ADMISSION_REPLY_BYTES)
        .and_then(|line| serde_json::from_str::<AdmissionIdentity>(&line).ok())
        .filter(AdmissionIdentity::is_valid)
        .ok_or_else(|| evidence_error("missing, unsupported or malformed admission identity"))?;
    if &identity.daemon != expected {
        return Err(evidence_error(format!(
            "admission authority build identity mismatch: expected release {:?}, source {:?}, executable SHA-256 {}; received release {:?}, source {:?}, executable SHA-256 {}. Build the same-stage targo-trust and trustd companions alongside trustc (for a stage1 development sysroot: `x.py build --stage 1 targo-trust`); do not bypass the configured memory authority",
            expected.release,
            expected.commit,
            expected.executable_sha256,
            identity.daemon.release,
            identity.daemon.commit,
            identity.daemon.executable_sha256,
        )));
    }
    write_line_until(&mut stream, "STATUS", deadline)
        .map_err(|error| evidence_error(format!("could not request admission STATUS: {error}")))?;
    let status = read_one_line_until(&stream, deadline)
        .and_then(|line| serde_json::from_str::<DaemonStatus>(&line).ok())
        .filter(DaemonStatus::is_semantically_valid)
        .ok_or_else(|| evidence_error("missing or malformed admission STATUS"))?;
    let client_budget_at_preflight_bytes = current_client_budget_at_preflight_bytes();
    if !daemon_budget_is_acceptable(&status, client_budget_at_preflight_bytes)
        || bytes > client_budget_at_preflight_bytes
    {
        return Err(evidence_error(
            "admission evidence exceeds this client's effective-memory domain",
        ));
    }
    let request = AdmissionRequest {
        version: ADMISSION_REQUEST_VERSION.to_string(),
        bytes,
        pid: std::process::id(),
        work: work.clone(),
    };
    let frame = format!(
        "RESERVE_EVIDENCE {}",
        serde_json::to_string(&request).map_err(|error| {
            evidence_error(format!("could not encode admission request: {error}"))
        })?
    );
    if frame.len() > MAX_REQUEST_BYTES {
        return Err(evidence_error("admission evidence request exceeds the protocol bound"));
    }
    let deadline = Instant::now().checked_add(reservation_timeout).unwrap_or_else(Instant::now);
    write_line_until(&mut stream, &frame, deadline).map_err(|error| {
        evidence_error(format!("could not send admission evidence request: {error}"))
    })?;
    let grant = read_one_line_until_limited(&stream, deadline, MAX_ADMISSION_REPLY_BYTES)
        .and_then(|line| {
            serde_json::from_str::<AdmissionGrant>(line.strip_prefix("ADMITTED ")?).ok()
        })
        .filter(|grant| {
            grant.is_valid()
                && grant.authority == identity
                && grant.bytes == bytes
                && grant.work == work
                && grant.grant_sequence > status.granted_total
                && grant.budget_at_grant_bytes <= status.budget_bytes
                && grant.budget_at_grant_bytes <= client_budget_at_preflight_bytes
        })
        .ok_or_else(|| {
            evidence_error("missing, refused, unsupported or contradictory admission grant")
        })?;
    let _ = stream.set_write_timeout(Some(observer_timeout));
    let reservation = Reservation {
        inner: ReservationKind::Daemon {
            stream,
            token: grant.token,
            bytes,
            owner_pid: request.pid,
            explicit_release_on_drop: true,
        },
    };
    Ok(EvidencedReservation {
        reservation,
        receipt: AdmissionReceipt {
            version: ADMISSION_RECEIPT_VERSION,
            client_budget_at_preflight_bytes,
            daemon_budget_at_preflight_bytes: status.budget_bytes,
            grant,
        },
    })
}

#[cfg(all(test, unix))]
#[path = "admission/tests.rs"]
mod tests;
