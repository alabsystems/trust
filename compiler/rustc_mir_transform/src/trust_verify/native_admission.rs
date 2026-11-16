//! Trust: native scheduling observations. All state belongs to this Session;
//! nested queries and concurrent workers own distinct attempt slots.
use std::collections::{BTreeMap, BTreeSet};
use std::io::{self, Write};
use std::sync::{Arc, Mutex, OnceLock};

use rustc_middle::ty::TyCtxt;
use rustc_span::def_id::{DefId, LOCAL_CRATE, LocalDefId};
#[cfg(unix)]
use trust_types::native_admission::NativeAdmissionReceipt;
use trust_types::native_admission::{
    NativeAdmissionAttempt, NativeAdmissionBinding, NativeAdmissionBody, NativeAdmissionCensus,
    NativeAdmissionOutcome, SCHEMA, request_work_digest, run_digest,
};

// Keep one resource diagnostic well below the unchanged 128 MiB outer Cargo
// line limit, including both its escaped message and rendered diagnostic copy.
const MAX_CENSUS_TRANSPORT_BYTES: usize = 1024 * 1024;

struct BoundedWriter {
    bytes: Vec<u8>,
    limit: usize,
}

impl Write for BoundedWriter {
    fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
        if bytes.len() > self.limit.saturating_sub(self.bytes.len()) {
            return Err(io::Error::other(
                "native admission census exceeded producer payload bound",
            ));
        }
        self.bytes.extend_from_slice(bytes);
        Ok(bytes.len())
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

fn bounded_census_json(census: &NativeAdmissionCensus) -> Result<String, String> {
    #[derive(serde::Serialize)]
    struct Tagged<'a> {
        #[serde(rename = "type")]
        kind: &'static str,
        #[serde(flatten)]
        census: &'a NativeAdmissionCensus,
    }
    let mut writer = BoundedWriter { bytes: Vec::new(), limit: MAX_CENSUS_TRANSPORT_BYTES };
    serde_json::to_writer(&mut writer, &Tagged { kind: "native_admission_census", census })
        .map_err(|error| error.to_string())?;
    String::from_utf8(writer.bytes).map_err(|error| error.to_string())
}

fn census_transport_json(mut census: NativeAdmissionCensus) -> Result<String, String> {
    match bounded_census_json(&census) {
        Ok(json) => Ok(json),
        Err(error) => {
            // Publish explicit incompleteness, including for a late census that
            // must invalidate an earlier snapshot. Never truncate a population
            // and preserve its old `complete` claim.
            census.complete = false;
            census.problems = vec![format!("{error}; full native work population omitted")];
            census.bodies.clear();
            census.auxiliary_bodies.clear();
            census.attempts.clear();
            bounded_census_json(&census)
        }
    }
}

#[derive(Default)]
struct Ledger {
    attempts: Vec<NativeAdmissionAttempt>,
    last_attempt_by_body: BTreeMap<NativeAdmissionBody, u64>,
    problems: Vec<String>,
    published: bool,
}

impl Ledger {
    fn begin(
        &mut self,
        binding: &NativeAdmissionBinding,
        body: NativeAdmissionBody,
        request: &str,
    ) -> Option<usize> {
        let last_attempt = self.last_attempt_by_body.entry(body.clone()).or_default();
        let Some(attempt) = last_attempt.checked_add(1) else {
            self.problems
                .push(format!("native-work attempt sequence exhausted for {}", body.function));
            return None;
        };
        *last_attempt = attempt;
        let index = self.attempts.len();
        let request_digest = trust_types::digest::stable_sha256_hex(request.as_bytes());
        self.attempts.push(NativeAdmissionAttempt {
            work_digest: request_work_digest(binding, &body, &request_digest),
            request_digest,
            body,
            attempt,
            outcome: NativeAdmissionOutcome::BeforeScheduling,
            terminal: false,
        });
        Some(index)
    }

    fn finish(&mut self, index: usize, unwinding: bool) {
        self.attempts[index].terminal = !unwinding;
    }
}

#[derive(Default)]
struct SessionLedger {
    ledger: Arc<Mutex<Ledger>>,
    // One authorized executable hash per unit, not one large binary read per body.
    expected: Arc<OnceLock<Result<trust_router::coordinator::DaemonIdentity, String>>>,
}

fn session_binding(
    session_options: &rustc_session::config::Options,
) -> Option<NativeAdmissionBinding> {
    let options = &session_options.unstable_opts;
    let binding = NativeAdmissionBinding {
        run_digest: options.trust_admission_run_digest.clone()?,
        unit_digest: options.trust_admission_unit_digest.clone()?,
        semantics_digest: options.trust_admission_semantics_digest.clone()?,
        role: options.trust_admission_unit_role.clone()?,
        // Cargo owns the exact canonical target path. TargetTuple deliberately
        // drops that path during metadata serialization, so its rustdoc-only
        // field and display tuple cannot be used as the resource identity.
        target: options.trust_admission_compile_target.clone()?,
    };
    let session = options.trust_verify_session.as_deref()?;
    if session_options.target_triple.json_contents().is_none()
        && binding.target != session_options.target_triple.tuple()
    {
        return None;
    }
    (binding.validate().is_ok() && binding.run_digest == run_digest(session)).then_some(binding)
}

fn body(tcx: TyCtxt<'_>, def: DefId) -> NativeAdmissionBody {
    NativeAdmissionBody {
        function: trust_mir_extract::safe_def_path_str(tcx, def),
        body_digest: trust_types::digest::stable_sha256_hex(
            format!("trust.native-admission.body.v1\0{:?}", tcx.def_path_hash(def)).as_bytes(),
        ),
    }
}

pub(super) struct Scope<'tcx> {
    tcx: TyCtxt<'tcx>,
    binding: Option<NativeAdmissionBinding>,
    ledger: Arc<Mutex<Ledger>>,
    expected: Arc<OnceLock<Result<trust_router::coordinator::DaemonIdentity, String>>>,
    index: Option<usize>,
}

impl<'tcx> Scope<'tcx> {
    pub(super) fn open(tcx: TyCtxt<'tcx>, def: DefId, request: &str) -> Self {
        let binding = session_binding(&tcx.sess.opts);
        let (ledger, expected) = tcx.sess.with_trust_compiler_state::<SessionLedger, _>(|s| {
            (s.ledger.clone(), s.expected.clone())
        });
        let index = binding.as_ref().and_then(|binding| {
            let body = body(tcx, def);
            let mut state = ledger.lock().unwrap_or_else(|e| e.into_inner());
            state.begin(binding, body, request)
        });
        Self { tcx, binding, ledger, expected, index }
    }

    pub(super) fn outcome(&self, outcome: NativeAdmissionOutcome) {
        if let Some(index) = self.index {
            self.ledger.lock().unwrap_or_else(|e| e.into_inner()).attempts[index].outcome = outcome;
        }
    }

    pub(super) fn reserve(
        &self,
        bytes: u64,
    ) -> Result<trust_router::coordinator::Reservation, String> {
        let Some(binding) = &self.binding else {
            // Direct/unscoped compilation retains the original scheduling contract.
            return trust_router::coordinator::reserve_labeled(bytes, "trustc-native")
                .map_err(|error| error.to_string());
        };
        // A scoped recording failure must stop at the admission boundary. It is
        // not unscoped compilation and cannot silently use the legacy path.
        let index = self.index.ok_or("native admission work could not be recorded")?;
        let row = self.ledger.lock().unwrap_or_else(|e| e.into_inner()).attempts[index].clone();
        let work = trust_router::coordinator::AdmissionWork {
            run_digest: binding.run_digest.clone(),
            unit_digest: binding.unit_digest.clone(),
            semantics_digest: binding.semantics_digest.clone(),
            work_digest: row.work_digest,
            kind: trust_router::coordinator::AdmissionWorkKind::NativeVerification,
            attempt: row.attempt,
        };
        #[cfg(not(unix))]
        {
            let _ = (work, &self.expected);
            self.ledger
                .lock()
                .unwrap_or_else(|e| e.into_inner())
                .problems
                .push("native admission receipts unavailable on this non-Unix platform".into());
            return trust_router::coordinator::reserve_labeled(bytes, "trustc-native")
                .map_err(|error| error.to_string());
        }
        #[cfg(unix)]
        {
            let result = self
                .expected
                .get_or_init(|| {
                    trust_router::coordinator::expected_daemon_identity().map_err(|e| e.to_string())
                })
                .as_ref()
                .map_err(|error| error.clone())
                .and_then(|expected| {
                    trust_router::coordinator::reserve_with_evidence(bytes, expected, work)
                        .map_err(|error| error.to_string())
                });
            match result {
                Ok(reservation) => {
                    let (guard, receipt) = reservation.into_parts();
                    let wire = serde_json::to_value(receipt)
                        .and_then(serde_json::from_value::<NativeAdmissionReceipt>);
                    match wire {
                        Ok(receipt) => self.outcome(NativeAdmissionOutcome::Admitted {
                            receipt: Box::new(receipt),
                        }),
                        Err(error) => self
                            .ledger
                            .lock()
                            .unwrap_or_else(|e| e.into_inner())
                            .problems
                            .push(format!("could not retain native admission receipt: {error}")),
                    }
                    Ok(guard)
                }
                Err(error) => {
                    self.outcome(NativeAdmissionOutcome::Refused { reason: error.clone() });
                    Err(error)
                }
            }
        }
    }
}

impl Drop for Scope<'_> {
    fn drop(&mut self) {
        if let Some(index) = self.index {
            let late = {
                let mut ledger = self.ledger.lock().unwrap_or_else(|e| e.into_inner());
                ledger.finish(index, std::thread::panicking());
                ledger.published
            };
            if late {
                // Any work after the terminal snapshot invalidates resource completeness.
                // A second census is deliberately rejected by the resource consumer.
                emit(self.tcx, &[]);
            }
        }
    }
}

#[cfg(test)]
mod tests;

pub(super) fn early_out(tcx: TyCtxt<'_>, def: LocalDefId, reason: &str) {
    Scope::open(tcx, def.to_def_id(), reason)
        .outcome(NativeAdmissionOutcome::EarlyOut { reason: reason.to_string() });
}

pub(super) fn emit(tcx: TyCtxt<'_>, eligible: &[LocalDefId]) {
    let Some(binding) = session_binding(&tcx.sess.opts) else { return };
    let mut bodies: Vec<_> = eligible.iter().map(|d| body(tcx, d.to_def_id())).collect();
    bodies.sort();
    let (attempts, mut problems) = tcx.sess.with_trust_compiler_state::<SessionLedger, _>(|s| {
        let mut ledger = s.ledger.lock().unwrap_or_else(|e| e.into_inner());
        if ledger.published {
            ledger.problems.push("work occurred after terminal admission census".into());
        }
        ledger.published = true;
        (ledger.attempts.clone(), ledger.problems.clone())
    });
    let root_bodies: BTreeSet<_> = bodies.iter().collect();
    let attempted_bodies: BTreeSet<_> = attempts.iter().map(|a| &a.body).collect();
    for body in &bodies {
        if !attempted_bodies.contains(body) {
            problems.push(format!("no native-work disposition for {}", body.function));
        }
    }
    if attempts.iter().any(|a| !a.terminal) {
        problems.push("unclosed native work".into());
    }
    let auxiliary_bodies =
        attempted_bodies.difference(&root_bodies).map(|body| (**body).clone()).collect();
    let mut census = NativeAdmissionCensus {
        transport_type: None,
        schema: SCHEMA.into(),
        binding,
        package_name: tcx
            .sess
            .opts
            .unstable_opts
            .trust_verify_package_name
            .clone()
            .unwrap_or_default(),
        crate_name: tcx.crate_name(LOCAL_CRATE).to_string(),
        bodies,
        auxiliary_bodies,
        attempts,
        complete: problems.is_empty(),
        problems,
    };
    if let Err(error) = census.validate() {
        census.complete = false;
        census.problems.push(error);
    }
    match census_transport_json(census) {
        Ok(json) => super::emit_transport_payload(tcx, &json),
        Err(error) => tcx.dcx().note(format!("native admission census unavailable: {error}")),
    }
}
