// Copyright 2026 Andrew Yates | Apache-2.0
//! Fixed-source/cohort original-input mathematics. No model/context selector,
//! Rust source theorem, SourceNoUB/body grade, physical ABI or shipping path.
use std::fmt;
use std::path::Path;

use clean_kernel::EnvDigest;
use clean_olean::semr_scalar::{CheckedScalarMathematics, ScalarContext, ScalarPacket};
use serde::{Deserialize, Serialize};
use trust_ir::proof::{decode_clean_expr_dag_v2, encode_clean_expr_dag_v2};

use super::scalar_contract::{ROOT_MODULES, ROOTS, SCHEMA as COHORT_SCHEMA};
use super::{ExpectedScalarInput, ScalarBinding};
use crate::call_event::CerInput;
use crate::compiler_input_capture::{CompilerCaptureConfig, CompilerInputCapture};
use crate::object_replay::{artifact_digest, encode};

const MANIFEST: &str = include_str!("cohort.json");
const PACKET_SCHEMA: &str = "trust.compiler-original-scalar-mathematics.v1";
const ENCODING: &str = "clean.expr.lossless-dag.v2";
const PROOF_BYTES: usize = 1 << 20;
const WIRE_BYTES: usize = 3 << 20;

/// Only the compiled source+owned-byte cohort and a genuinely completed FULL
/// closed replay construct this context. Caller names/ReferenceBase data are
/// not public constructors. The directory only locates the already fixed bytes.
///
/// ```compile_fail
/// use trust_cg_bridge::compiler_input_capture::CanonicalScalarEnvironment;
/// let context = CanonicalScalarEnvironment::from_environment(
///     clean_kernel::Environment::for_lean_replay());
/// ```
pub struct CanonicalScalarEnvironment {
    context: ScalarContext,
    cohort: String,
}

/// Untrusted transport. It carries no expected module bytes/model selector;
/// the current Compiler input owner derives those independently at replay.
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct OriginalScalarPacket {
    schema: String,
    encoding: String,
    capture_sha256: String,
    subject: ScalarBinding,
    cohort_sha256: String,
    context: EnvDigest,
    proofs: [Vec<u8>; 3],
}
impl OriginalScalarPacket {
    pub fn to_bytes(&self) -> Result<Vec<u8>, String> {
        encode(self, WIRE_BYTES)
    }
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, String> {
        if bytes.len() > WIRE_BYTES {
            return Err("scalar packet byte bound".into());
        }
        let packet: Self = serde_json::from_slice(bytes).map_err(|e| e.to_string())?;
        if packet.schema != PACKET_SCHEMA
            || packet.encoding != ENCODING
            || packet.proofs.iter().any(|p| p.is_empty() || p.len() > PROOF_BYTES)
        {
            return Err("scalar packet schema/encoding/proof bound".into());
        }
        Ok(packet)
    }
}

/// Checked mathematics about actual selected original-IR INPUT DATA. Private
/// fields and no Deserialize/grade/token conversion preserve its limited role.
pub struct CheckedOriginalScalar {
    packet: OriginalScalarPacket,
    mathematics: CheckedScalarMathematics,
}
impl fmt::Debug for CheckedOriginalScalar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("CheckedOriginalScalar")
            .field("subject", &self.packet.subject)
            .field("scope", &"original IR input mathematics only; no source/ABI/grade")
            .finish()
    }
}
impl CheckedOriginalScalar {
    pub fn packet(&self) -> &OriginalScalarPacket {
        &self.packet
    }
    pub fn mathematics(&self) -> &CheckedScalarMathematics {
        &self.mathematics
    }
}

impl CanonicalScalarEnvironment {
    pub fn open(directory: &Path) -> Result<Self, String> {
        super::source_binding::check(MANIFEST)?;
        let (base, cohort) = crate::frame_step_evidence::cohort::open_replay(
            directory,
            MANIFEST,
            COHORT_SCHEMA,
            &ROOT_MODULES,
            &ROOTS,
        )?;
        let context =
            ScalarContext::from_profile_reference_base(base).map_err(|e| e.to_string())?;
        Ok(Self { context, cohort })
    }
    pub fn cohort_digest(&self) -> &str {
        &self.cohort
    }

    fn check(
        &self,
        expected: &ExpectedScalarInput,
        capture_sha256: &str,
        packet: &OriginalScalarPacket,
    ) -> Result<CheckedOriginalScalar, String> {
        if packet.schema != PACKET_SCHEMA
            || packet.encoding != ENCODING
            || packet.capture_sha256 != capture_sha256
            || packet.subject != expected.binding
            || packet.cohort_sha256 != self.cohort
            || packet.context != self.context.digest()
            || packet.proofs.iter().any(|p| p.is_empty() || p.len() > PROOF_BYTES)
        {
            return Err("scalar packet/current original input/cohort/context differs".into());
        }
        let _ = packet.to_bytes()?;
        let decoded = decode_clean_expr_dag_v2(&packet.proofs[0]).map_err(|e| e.to_string())?;
        let returned = decode_clean_expr_dag_v2(&packet.proofs[1]).map_err(|e| e.to_string())?;
        let no_bad = decode_clean_expr_dag_v2(&packet.proofs[2]).map_err(|e| e.to_string())?;
        // Actual expected bytes/literal and fixed context are supplied by this
        // owner. The untrusted packet supplies proof DATA, not expected claims.
        let retained = ScalarPacket {
            context: self.context.digest(),
            subject: expected.subject.clone(),
            decoded,
            returned,
            no_bad,
        };
        let mathematics =
            self.context.check(&expected.subject, &retained).map_err(|e| e.to_string())?;
        Ok(CheckedOriginalScalar { packet: packet.clone(), mathematics })
    }

    fn bind(
        &self,
        expected: &ExpectedScalarInput,
        capture_sha256: String,
    ) -> Result<CheckedOriginalScalar, String> {
        // Ordinary proof DATA instantiates the checked universal decoder/profile
        // theorem at the COMPLETE actual current bytes/literal. The real kernel
        // reduces the canonical decoder and profile; no host shape boolean or
        // assumed successful run is accepted. One check below verifies all3.
        let retained = self.context.profile_packet(&expected.subject).map_err(|e| e.to_string())?;
        let mut encoded = Vec::new();
        for proof in [&retained.decoded, &retained.returned, &retained.no_bad] {
            let bytes = encode_clean_expr_dag_v2(proof).map_err(|e| e.to_string())?;
            if bytes.len() > PROOF_BYTES {
                return Err("scalar retained proof byte bound".into());
            }
            encoded.push(bytes);
        }
        let proofs: [Vec<u8>; 3] = encoded.try_into().map_err(|_| "scalar retained proof count")?;
        let packet = OriginalScalarPacket {
            schema: PACKET_SCHEMA.into(),
            encoding: ENCODING.into(),
            capture_sha256,
            subject: expected.binding.clone(),
            cohort_sha256: self.cohort.clone(),
            context: self.context.digest(),
            proofs,
        };
        self.check(expected, &packet.capture_sha256, &packet)
    }
}

impl CompilerInputCapture {
    pub(super) fn current_scalar_input(
        &self,
        expected: &CerInput<'_>,
        configuration: &CompilerCaptureConfig,
        symbol: &str,
    ) -> Result<(ExpectedScalarInput, String), String> {
        let current = Self::capture(expected, configuration.clone()).map_err(|e| e.reason)?;
        if self != &current {
            return Err("scalar replay independent complete current input/config differs".into());
        }
        let subject = ExpectedScalarInput::from_current(expected, symbol)?;
        Ok((subject, artifact_digest(&current.to_bytes()?)))
    }

    /// Bind the fixed canonical generic decoder/profile mathematics to
    /// actual ORIGINAL current Compiler inputs, after complete capture equality.
    /// This creates no Rust/body/ABI/ISA proof, grade or emission capability.
    pub fn bind_original_scalar_mathematics(
        &self,
        expected: &CerInput<'_>,
        configuration: &CompilerCaptureConfig,
        symbol: &str,
        environment: &CanonicalScalarEnvironment,
    ) -> Result<CheckedOriginalScalar, String> {
        let (subject, capture) = self.current_scalar_input(expected, configuration, symbol)?;
        environment.bind(&subject, capture)
    }

    /// Replay ORIGINAL retained proof data against independently selected
    /// current input. No decoded capture/packet may be its own reference.
    pub fn replay_original_scalar_mathematics(
        &self,
        expected: &CerInput<'_>,
        configuration: &CompilerCaptureConfig,
        symbol: &str,
        environment: &CanonicalScalarEnvironment,
        packet: &OriginalScalarPacket,
    ) -> Result<CheckedOriginalScalar, String> {
        let (subject, capture) = self.current_scalar_input(expected, configuration, symbol)?;
        environment.check(&subject, &capture, packet)
    }
}

#[cfg(test)]
mod tests;
