//! Retained original CIC evidence. Wire data never grants a verdict by itself.
//!
//! Only the kernel-checking constructors create CheckedOriginalConjunction.
//! Replay rebuilds the original goal/context and restores the retained proof;
//! it never invokes proof production, code generation, or a solver.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::io::{self, Write};
use std::sync::Arc;

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use trust_types::{Formula, Sort};

mod call_instance;
#[cfg(feature = "fmrel")]
mod fmrel;
#[cfg(feature = "kernel-recheck")]
mod frame_environment;
mod retained_terms;
mod subject;
mod terms;
pub(crate) use call_instance::{
    specialize_original_for_call, specialize_original_for_expected_transition,
};
use retained_terms::RetainedTerms;
pub(crate) use subject::SubjectBinding;
pub(crate) use terms::TermPacket;

const MODEL: u32 = 2;
const FRAME_MODEL: u32 = 3;
const FORMULA_MODEL: u32 = 4;
const MAX_WIRE_BYTES: usize = 4 * 1024 * 1024;
pub(crate) const MAX_SIDECAR_BYTES: usize = 64 * 1024 * 1024;
pub(crate) const MAX_REPLAY_FUNCTIONS: usize = 32;
const MAX_ORIGINAL_BYTES: usize = 1024 * 1024;
const MAX_CONJUNCTS: usize = 256;
const RECIPE: &str = "clean.with_prelude+init_bv_coercion+original-m8-data-parameters/v2";
const FRAME_RECIPE: &str = "clean.with_prelude+init_bv_coercion+retained-byte-shift-v1+retained-frame-offsets-v1+retained-frame-reads-v1+retained-frame-word-transport-v1+retained-frame-word-assembly-v1+original-m8-data-parameters/v3";
const LEGACY_RECIPE: &str = "clean.with_prelude+init_bv_coercion+original-m8-data-parameters/v1";
const FORMULA_RECIPE: &str =
    "trust-ir.formula-v2-original-bytes+checked-source-goal+final-source-proof/v4";

/// Portable advice only. The shared TrustIR codecs impose their own decoding
/// bounds; neither these bytes nor the cohort digest constitute admission.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct FormulaEvidence {
    cohort_sha256: String,
    foundations: Vec<String>,
    declarations: Vec<u8>,
    relation: Vec<u8>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    preconditions: Option<Vec<u8>>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct SymbolicContext {
    pub(crate) bits: BTreeSet<String>,
    pub(crate) memories: BTreeSet<String>,
    pub(crate) sorts: BTreeMap<String, Sort>,
    pub(crate) exact_byte_arrays: bool,
}

/// Untrusted, bounded portable data. This type is not proof authority.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct OriginalConjunctionPacket {
    model: u32,
    original: Vec<(Formula, Formula)>,
    original_sha256: String,
    context: SymbolicContext,
    context_sha256: String,
    terms: RetainedTerms,
    goal_sha256: String,
    proof_sha256: String,
    environment_sha256: String,
    environment_mode: String,
    environment_recipe: String,
    kernel_version: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    formula_evidence: Option<FormulaEvidence>,
}

/// This private construction boundary is intentionally not Deserialize.
#[derive(Clone, PartialEq, Eq)]
pub struct CheckedOriginalConjunction {
    packet: Arc<OriginalConjunctionPacket>,
    label: String,
}
impl fmt::Debug for CheckedOriginalConjunction {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("CheckedOriginalConjunction")
            .field("theorem", &self.label)
            .field("terms", &self.packet.terms.node_count())
            .finish()
    }
}
impl CheckedOriginalConjunction {
    pub(crate) fn label(&self) -> &str {
        &self.label
    }
    pub(crate) fn packet(&self) -> &OriginalConjunctionPacket {
        &self.packet
    }
    pub(crate) fn original_equations(&self) -> &[(Formula, Formula)] {
        &self.packet.original
    }
    pub(crate) fn variable_sorts(&self) -> &BTreeMap<String, Sort> {
        &self.packet.context.sorts
    }
}

/// Object/IR/P binding plus portable proof data. Deserializing is untrusted.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct OriginalConjunctionCertificate {
    subject: SubjectBinding,
    packet: OriginalConjunctionPacket,
}
impl OriginalConjunctionCertificate {
    pub(crate) fn uses_formula_semantics(&self) -> bool {
        self.packet.model == FORMULA_MODEL
    }

    #[cfg(feature = "fmrel")]
    pub(crate) fn replay_formula(
        &self,
        original: &[(Formula, Formula)],
        preconditions: &[(Formula, Formula)],
    ) -> Result<CheckedOriginalConjunction, String> {
        self.packet.validate()?;
        if !self.uses_formula_semantics() {
            return Err("retained Formula replay requires its distinct model".into());
        }
        crate::verify_output_instantiate::on_route_stack(|| {
            fmrel::replay_with_preconditions(&self.packet, original, preconditions)
        })
    }
    pub(crate) fn bind(
        checked: &CheckedOriginalConjunction,
        input: &crate::call_event::CerInput<'_>,
        certificate: &crate::call_event::FunctionCertificate,
    ) -> Result<Self, String> {
        checked.packet.validate()?;
        let certificate = Self {
            subject: SubjectBinding::from_input(input, certificate)?,
            packet: checked.packet().clone(),
        };
        certificate.encoded_bytes()?;
        Ok(certificate)
    }
    pub(crate) fn require_subject(
        &self,
        input: &crate::call_event::CerInput<'_>,
        certificate: &crate::call_event::FunctionCertificate,
    ) -> Result<(), String> {
        self.encoded_bytes()?;
        if self.subject != SubjectBinding::from_input(input, certificate)? {
            return Err(
                "retained original proof: actual object/module/body/P/target subject mismatch"
                    .into(),
            );
        }
        self.packet.validate()
    }
    /// Untrusted finite witness choices only. Callers must independently rebuild
    /// each actual term and require the complete retained goal/kernel check.
    pub(crate) fn original_equations(&self) -> &[(Formula, Formula)] {
        &self.packet.original
    }
    pub(crate) fn replay(
        &self,
        original: &[(Formula, Formula)],
    ) -> Result<CheckedOriginalConjunction, String> {
        self.packet.replay(original)
    }
    /// The complete portable packet size, independently of a JSON report's formatting.
    pub fn encoded_bytes(&self) -> Result<usize, String> {
        bounded_len(self, MAX_WIRE_BYTES)
    }
    /// Carrier records (Expr records in v1; Name/Level/Expr records in CEXDAG02).
    pub fn term_nodes(&self) -> usize {
        self.packet.terms.node_count()
    }
}

struct BoundedWriter {
    bytes: usize,
    limit: usize,
    hash: Sha256,
}
impl Write for BoundedWriter {
    fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
        self.bytes = self
            .bytes
            .checked_add(bytes.len())
            .filter(|n| *n <= self.limit)
            .ok_or_else(|| io::Error::other("original certificate serialization budget"))?;
        self.hash.update(bytes);
        Ok(bytes.len())
    }
    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}
fn encoded_hash<T: Serialize>(value: &T, limit: usize) -> Result<(String, usize), String> {
    let mut writer = BoundedWriter { bytes: 0, limit, hash: Sha256::new() };
    serde_json::to_writer(&mut writer, value).map_err(|e| e.to_string())?;
    Ok((format!("{:x}", writer.hash.finalize()), writer.bytes))
}
fn bounded_len<T: Serialize>(value: &T, limit: usize) -> Result<usize, String> {
    encoded_hash(value, limit).map(|(_, n)| n)
}
fn bounded_pretty_len<T: Serialize>(value: &T, limit: usize) -> Result<usize, String> {
    let mut writer = BoundedWriter { bytes: 0, limit, hash: Sha256::new() };
    value
        .serialize(&mut serde_json::Serializer::pretty(&mut writer))
        .map_err(|error| error.to_string())?;
    Ok(writer.bytes)
}
/// Producer and replay share the same actual denominator and transport limits.
/// Exceeding them can only remove the new retained-original favorable grade.
pub(crate) fn enforce_report_limits(
    report: &mut crate::call_event::CerReport,
    actual_functions: usize,
) {
    if !report.certificates.iter().any(|row| row.original_proof.is_some()) {
        return;
    }
    let reason = if actual_functions > MAX_REPLAY_FUNCTIONS
        || report.certificates.len() > MAX_REPLAY_FUNCTIONS
    {
        Some("retained original sidecar exceeds replay function population bound".to_string())
    } else {
        bounded_pretty_len(report, MAX_SIDECAR_BYTES).err().map(|reason| {
            format!("retained original sidecar exceeds replay byte/serialization bound: {reason}")
        })
    };
    if let Some(reason) = reason {
        for certificate in &mut report.certificates {
            if certificate.original_proof.take().is_some() && certificate.is_kernel_proved() {
                certificate.obligations.o4_return = crate::call_event::ObligationGrade {
                    grade: crate::call_event::Grade::Unknown,
                    detail: reason.clone(),
                };
                certificate.grade = "Unknown".into();
                certificate.verdict =
                    crate::verify_output::OutputVerdict::Unknown { reason: reason.clone() };
            }
        }
        report.closure = crate::call_event::closure_report(&report.certificates);
    }
}

fn digest_is_valid(value: &str) -> bool {
    value.len() == 64 && value.bytes().all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
}
impl OriginalConjunctionPacket {
    fn validate(&self) -> Result<(), String> {
        if !matches!(self.model, 1 | MODEL | FRAME_MODEL | FORMULA_MODEL)
            || self.original.is_empty()
            || self.original.len() > MAX_CONJUNCTS
            || !self.context.exact_byte_arrays
            || self.context.bits.len() > 8192
            || self.context.memories.len() > 1024
            || self.context.sorts.len() > 1024
            || self.environment_recipe
                != match self.model {
                    1 => LEGACY_RECIPE,
                    FRAME_MODEL => FRAME_RECIPE,
                    FORMULA_MODEL => FORMULA_RECIPE,
                    _ => RECIPE,
                }
            || self.kernel_version.is_empty()
            || [
                &self.original_sha256,
                &self.context_sha256,
                &self.goal_sha256,
                &self.proof_sha256,
                &self.environment_sha256,
            ]
            .iter()
            .any(|s| !digest_is_valid(s))
        {
            return Err(
                "retained original proof: model/population/context/environment identity".into()
            );
        }
        match (&self.formula_evidence, self.model) {
            (Some(evidence), FORMULA_MODEL)
                if digest_is_valid(&evidence.cohort_sha256)
                    && !evidence.declarations.is_empty()
                    && !evidence.relation.is_empty()
                    && evidence.declarations.len() <= MAX_WIRE_BYTES
                    && evidence.relation.len() <= MAX_WIRE_BYTES => {}
            (None, 1 | MODEL | FRAME_MODEL) => {}
            _ => return Err("retained original proof: Formula evidence/model mismatch".into()),
        }
        if self.terms.is_formula() != (self.model == FORMULA_MODEL) {
            return Err("retained original proof: term carrier/model mismatch".into());
        }
        self.terms.validate()?;
        if encoded_hash(&self.original, MAX_ORIGINAL_BYTES)?.0 != self.original_sha256
            || encoded_hash(&self.context, MAX_ORIGINAL_BYTES)?.0 != self.context_sha256
        {
            return Err("retained original proof: original/context digest mismatch".into());
        }
        bounded_len(self, MAX_WIRE_BYTES)?;
        Ok(())
    }

    #[cfg(not(feature = "kernel-recheck"))]
    pub(crate) fn replay(
        &self,
        _original: &[(Formula, Formula)],
    ) -> Result<CheckedOriginalConjunction, String> {
        Err("retained original proof: kernel-recheck feature unavailable".into())
    }
    #[cfg(feature = "kernel-recheck")]
    pub(crate) fn replay(
        &self,
        original: &[(Formula, Formula)],
    ) -> Result<CheckedOriginalConjunction, String> {
        self.validate()?;
        if self.original != original {
            return Err(
                "retained original proof: independently expected original equations mismatch"
                    .into(),
            );
        }
        if self.model == FORMULA_MODEL {
            #[cfg(feature = "fmrel")]
            return fmrel::replay(self, original);
            #[cfg(not(feature = "fmrel"))]
            return Err("retained original proof: canonical Formula replay unavailable".into());
        }
        let (expected, context) =
            crate::verify_output_instantiate::original_conjunction_goal_version(
                original, self.model,
            )
            .ok_or("retained original proof: expected original goal cannot be rendered")?;
        if context != self.context {
            return Err(
                "retained original proof: independently rebuilt typed context mismatch".into()
            );
        }
        let environment = environment(&context, self.model)?;
        require_environment(self, &environment)?;
        let (goal, proof) = self.terms.restore()?;
        if goal != expected
            || encoded_hash(&goal, 64 * 1024 * 1024)?.0 != self.goal_sha256
            || encoded_hash(&proof, 64 * 1024 * 1024)?.0 != self.proof_sha256
        {
            return Err(
                "retained original proof: restored goal/proof/original binding mismatch".into()
            );
        }
        crate::verify_output_instantiate::run_recheck_thread(
            "trust-replay-original-CIC",
            move || {
                clean_kernel::TypeChecker::with_mode(&environment, environment.mode())
                    .check_type(&proof, &expected)
                    .map_err(|e| format!("retained original CIC kernel rejection: {e:?}"))
            },
        )
        .map_err(|e| format!("retained original CIC checker thread: {e:?}"))??;
        Ok(CheckedOriginalConjunction { packet: Arc::new(self.clone()), label: self.label() })
    }
    fn label(&self) -> String {
        let mut label = format!(
            "Clean.CIC.original-conjunction/v{} n={} inputs-sha256={} goal-sha256={} proof-sha256={}",
            self.model,
            self.original.len(),
            self.original_sha256,
            self.goal_sha256,
            self.proof_sha256
        );
        if let Some(evidence) = &self.formula_evidence {
            label.push_str(" conditional-foundations=");
            label.push_str(&evidence.foundations.join(","));
        }
        label
    }
}

#[cfg(feature = "kernel-recheck")]
fn environment(context: &SymbolicContext, model: u32) -> Result<clean_kernel::Environment, String> {
    use clean_kernel::{Declaration, Expr, Name};

    use crate::verify_output_instantiate::{discharge_env, kx};
    if !context.exact_byte_arrays {
        return Err("original CIC replay requires exact byte arrays".into());
    }
    let mut environment = if model == FRAME_MODEL {
        static BASE: std::sync::OnceLock<clean_kernel::Environment> = std::sync::OnceLock::new();
        static INIT: std::sync::Mutex<()> = std::sync::Mutex::new(());
        if let Some(base) = BASE.get() {
            base.clone()
        } else {
            let _guard =
                INIT.lock().map_err(|_| "closed frame environment initialization poisoned")?;
            if let Some(base) = BASE.get() {
                base.clone()
            } else {
                let mut base = discharge_env(&[], &[])?;
                crate::verify_output_instantiate::install_original_frame_bank(&mut base)?;
                // Only fully checked parameter-free environments reach BASE.
                BASE.set(base.clone()).map_err(|_| "closed frame environment initialized twice")?;
                base
            }
        }
    } else {
        discharge_env(&[], &[])?
    };
    for name in &context.bits {
        environment
            .add_decl(Declaration::Axiom {
                name: Name::from_string(name),
                level_params: vec![],
                type_: kx::bool_ty(),
            })
            .map_err(|e| format!("original CIC Bool data parameter refused: {e:?}"))?;
    }
    for name in &context.memories {
        environment
            .add_decl(Declaration::Axiom {
                name: Name::from_string(name),
                level_params: vec![],
                type_: Expr::arrow(kx::list_bool(), kx::bool_ty()),
            })
            .map_err(|e| format!("original CIC array-bit data parameter refused: {e:?}"))?;
    }
    Ok(environment)
}
#[cfg(feature = "kernel-recheck")]
fn require_environment(
    packet: &OriginalConjunctionPacket,
    environment: &clean_kernel::Environment,
) -> Result<(), String> {
    if packet.environment_sha256 != environment_digest(environment, packet.model)?
        || packet.environment_mode != format!("{:?}", environment.mode())
        || packet.kernel_version != clean_kernel::VERSION
    {
        return Err("retained original proof: actual trusted kernel environment mismatch".into());
    }
    Ok(())
}

#[cfg(feature = "kernel-recheck")]
fn environment_digest(
    environment: &clean_kernel::Environment,
    model: u32,
) -> Result<String, String> {
    if model == FRAME_MODEL {
        frame_environment::digest(environment)
    } else {
        crate::object_replay::original_environment_digest(environment)
    }
}

#[cfg(any(test, feature = "test-hooks"))]
thread_local! { static FORBID_PRODUCTION: std::cell::Cell<bool> = const { std::cell::Cell::new(false) }; }
#[cfg(any(test, feature = "test-hooks"))]
pub(crate) fn require_production_allowed() {
    FORBID_PRODUCTION.with(|flag| {
        assert!(!flag.get(), "proof production or solver invoked during retained replay")
    });
}
#[cfg(any(test, feature = "test-hooks"))]
pub(crate) fn without_production<T>(action: impl FnOnce() -> T) -> T {
    struct Reset(bool);
    impl Drop for Reset {
        fn drop(&mut self) {
            FORBID_PRODUCTION.set(self.0);
        }
    }
    let _reset = Reset(FORBID_PRODUCTION.replace(true));
    action()
}

/// Original proof production remains prohibited during replay/transport.
#[cfg(feature = "kernel-recheck")]
pub(crate) fn check_produced(
    original: &[(Formula, Formula)],
    goal: &clean_kernel::Expr,
    proof: &clean_kernel::Expr,
) -> Result<CheckedOriginalConjunction, String> {
    #[cfg(any(test, feature = "test-hooks"))]
    require_production_allowed();
    check_supplied(original, goal, proof)
}

/// Canonical Formula route has a distinct retained recipe and admission
/// boundary. Unavailable source operations and artifact cohorts refuse.
#[cfg(feature = "fmrel")]
pub(crate) fn check_formula_produced(
    original: &[(Formula, Formula)],
) -> Result<CheckedOriginalConjunction, String> {
    crate::verify_output_instantiate::on_route_stack(|| fmrel::produce(original))
}

#[cfg(feature = "fmrel")]
pub(crate) fn check_formula_with_preconditions(
    original: &[(Formula, Formula)],
    preconditions: &[(Formula, Formula)],
) -> Result<CheckedOriginalConjunction, String> {
    crate::verify_output_instantiate::on_route_stack(|| {
        fmrel::produce_with_preconditions(original, preconditions)
    })
}

/// Shared private supplied-proof boundary: independently render the full exact
/// goal, enforce the retained codec/environment limits, and perform ONE actual
/// check_type. Unlike the producer entry it may run under without_production.
#[cfg(feature = "kernel-recheck")]
fn check_supplied(
    original: &[(Formula, Formula)],
    goal: &clean_kernel::Expr,
    proof: &clean_kernel::Expr,
) -> Result<CheckedOriginalConjunction, String> {
    let (expected, context) = crate::verify_output_instantiate::original_conjunction_goal(original)
        .ok_or("original CIC packet: original goal cannot be rendered")?;
    if *goal != expected {
        return Err("original CIC packet: produced goal differs from original renderer".into());
    }
    let model = crate::verify_output_instantiate::original_conjunction_model(original);
    let environment = environment(&context, model)?;
    let packet = OriginalConjunctionPacket {
        model,
        original: original.to_vec(),
        original_sha256: encoded_hash(&original, MAX_ORIGINAL_BYTES)?.0,
        context_sha256: encoded_hash(&context, MAX_ORIGINAL_BYTES)?.0,
        context,
        terms: TermPacket::capture(goal, proof)?.into(),
        goal_sha256: encoded_hash(goal, 64 * 1024 * 1024)?.0,
        proof_sha256: encoded_hash(proof, 64 * 1024 * 1024)?.0,
        environment_sha256: environment_digest(&environment, model)?,
        environment_mode: format!("{:?}", environment.mode()),
        environment_recipe: if model == FRAME_MODEL { FRAME_RECIPE } else { RECIPE }.into(),
        kernel_version: clean_kernel::VERSION.into(),
        formula_evidence: None,
    };
    packet.validate()?;
    let result = clean_kernel::TypeChecker::with_mode(&environment, environment.mode())
        .check_type(proof, goal);
    if let Some(output) = std::env::var_os("TRUST_M8_ORIGINAL_OUTPUT_DIR") {
        let output = std::path::PathBuf::from(output).join(&packet.original_sha256);
        std::fs::create_dir_all(&output).map_err(|e| e.to_string())?;
        for (name, bytes) in [
            ("original.json", serde_json::to_vec(&original)),
            ("goal.json", serde_json::to_vec(goal)),
            ("proof.json", serde_json::to_vec(proof)),
        ] {
            std::fs::write(output.join(name), bytes.map_err(|e| e.to_string())?)
                .map_err(|e| e.to_string())?;
        }
        let record = serde_json::json!({"original_sha256":packet.original_sha256,"goal_sha256":packet.goal_sha256,"proof_sha256":packet.proof_sha256,
            "conjuncts":original.len(),"kernel_check_type":format!("{result:?}"),"accepted":result.is_ok(),
            "bool_parameters":packet.context.bits,"array_bit_functions":packet.context.memories,"original_variable_sorts":packet.context.sorts,
            "exact_byte_arrays":true,"environment_sha256":packet.environment_sha256,"environment_mode":packet.environment_mode,
            "kernel_version":packet.kernel_version,"packet_bytes":bounded_len(&packet,MAX_WIRE_BYTES)?});
        std::fs::write(
            output.join("kernel-result.json"),
            serde_json::to_vec_pretty(&record).map_err(|e| e.to_string())?,
        )
        .map_err(|e| e.to_string())?;
    }
    result.map_err(|e| format!("original CIC kernel rejected produced proof: {e:?}"))?;
    Ok(CheckedOriginalConjunction { label: packet.label(), packet: Arc::new(packet) })
}

#[cfg(test)]
mod tests;

#[cfg(all(test, feature = "kernel-recheck"))]
mod current_legacy_advice;
