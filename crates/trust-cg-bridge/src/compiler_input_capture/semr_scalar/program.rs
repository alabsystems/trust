// Copyright 2026 Andrew Yates | Apache-2.0
//! Complete current IR input → checked actual MiniRust program construction.
//! The model C/unit Exit entry is an explicit harness, not a compiled Rust
//! process entry. No raw-source refinement, ABI, SourceNoUB or grade follows.
use std::fmt;
use std::path::Path;

use clean_kernel::{EnvDigest, Expr, Level, Name, ReferenceKernel};
use serde::{Deserialize, Serialize};
use trust_ir::proof::{decode_clean_expr_dag_v2, encode_clean_expr_dag_v2};

use super::program_contract::{ROOT_MODULE as NAMESPACE, ROOTS, SCHEMA as COHORT_SCHEMA};
use super::{program_contract, source_binding as foundation_source_binding, source_contract};
use super::{ExpectedScalarInput, ScalarBinding};
use crate::call_event::CerInput;
use crate::compiler_input_capture::{CompilerCaptureConfig, CompilerInputCapture};
use crate::object_replay::encode;

mod source_binding;
const MANIFEST: &str = include_str!("program/cohort.json");
const PACKET_SCHEMA: &str = "trust.compiler-original-scalar-program-mathematics.v1";
const ENCODING: &str = "clean.expr.lossless-dag.v2";
const PROOF_BYTES: usize = 1 << 20;
const WIRE_BYTES: usize = 3 << 20;

/// Only the fixed source/byte cohort and actual complete Clean replay build
/// this environment. No caller environment/model/expected-goal constructor.
pub struct CanonicalScalarProgramEnvironment {
    kernel: ReferenceKernel,
    cohort: String,
}

/// Untrusted proof transport: it contains no program, expected bytes, model
/// selector, expected goal or successful-machine flag.
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct OriginalScalarProgramPacket {
    schema: String,
    encoding: String,
    capture_sha256: String,
    subject: ScalarBinding,
    cohort_sha256: String,
    context: EnvDigest,
    proofs: [Vec<u8>; 3],
}
impl OriginalScalarProgramPacket {
    pub fn to_bytes(&self) -> Result<Vec<u8>, String> {
        encode(self, WIRE_BYTES)
    }
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, String> {
        if bytes.len() > WIRE_BYTES {
            return Err("scalar program packet byte bound".into());
        }
        let packet: Self = serde_json::from_slice(bytes).map_err(|e| e.to_string())?;
        if packet.schema != PACKET_SCHEMA
            || packet.encoding != ENCODING
            || packet.proofs.iter().any(|p| p.is_empty() || p.len() > PROOF_BYTES)
        {
            return Err("scalar program packet schema/encoding/proof bound".into());
        }
        Ok(packet)
    }
}

/// Checked construction, IR-Core/model correspondence and availability only.
/// No Deserialize or compiler/body/ABI/grade conversion exists.
pub struct CheckedOriginalScalarProgram {
    packet: OriginalScalarProgramPacket,
    claims: [Expr; 3],
    proofs: [Expr; 3],
}
impl fmt::Debug for CheckedOriginalScalarProgram {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("CheckedOriginalScalarProgram")
            .field("subject", &self.packet.subject)
            .field("scope", &"actual IR-input/model construction only; no source/ABI/grade")
            .finish()
    }
}
impl CheckedOriginalScalarProgram {
    pub fn packet(&self) -> &OriginalScalarProgramPacket {
        &self.packet
    }
    pub fn claims(&self) -> &[Expr; 3] {
        &self.claims
    }
    pub fn proofs(&self) -> &[Expr; 3] {
        &self.proofs
    }
}

fn constant(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}
fn byte_list(bytes: &[u8]) -> Expr {
    bytes.iter().rev().fold(
        Expr::app(
            Expr::const_(Name::from_string("List.nil"), vec![Level::zero()]),
            constant("Nat"),
        ),
        |tail, byte| {
            Expr::apps(
                Expr::const_(Name::from_string("List.cons"), vec![Level::zero()]),
                [constant("Nat"), Expr::nat_lit(u64::from(*byte)), tail],
            )
        },
    )
}

impl CanonicalScalarProgramEnvironment {
    pub fn open(directory: &Path) -> Result<Self, String> {
        source_binding::check(MANIFEST)?;
        let (base, cohort) = crate::frame_step_evidence::cohort::open_replay(
            directory,
            MANIFEST,
            COHORT_SCHEMA,
            &[NAMESPACE],
            &ROOTS,
        )?;
        let kernel = base.into_kernel().map_err(|r| r.verdict_sentence())?;
        Ok(Self { kernel, cohort })
    }
    pub fn cohort_digest(&self) -> &str {
        &self.cohort
    }

    fn check(
        &self,
        expected: &ExpectedScalarInput,
        capture: &str,
        packet: &OriginalScalarProgramPacket,
    ) -> Result<CheckedOriginalScalarProgram, String> {
        if packet.schema != PACKET_SCHEMA
            || packet.encoding != ENCODING
            || packet.capture_sha256 != capture
            || packet.subject != expected.binding
            || packet.cohort_sha256 != self.cohort
            || packet.context != self.kernel.env_digest()
            || packet.proofs.iter().any(|p| p.is_empty() || p.len() > PROOF_BYTES)
        {
            return Err("scalar program packet/current input/cohort/context differs".into());
        }
        let _ = packet.to_bytes()?;
        let bytes = byte_list(expected.module_bytes());
        let literal = Expr::nat_lit(expected.literal());
        let claims = ["Construction", "Correspondence", "Available"].map(|name| {
            Expr::apps(constant(&format!("{NAMESPACE}.{name}")), [bytes.clone(), literal.clone()])
        });
        let decoded = packet
            .proofs
            .iter()
            .map(|proof| decode_clean_expr_dag_v2(proof).map_err(|e| e.to_string()))
            .collect::<Result<Vec<_>, _>>()?;
        let proofs: [Expr; 3] =
            decoded.try_into().map_err(|_| "scalar program proof population")?;
        for ((claim, proof), label) in
            claims.iter().zip(&proofs).zip(["construction", "correspondence", "availability"])
        {
            self.kernel
                .check_closed_term(claim, proof)
                .map_err(|error| format!("{label}: {error:?}"))?;
        }
        Ok(CheckedOriginalScalarProgram { packet: packet.clone(), claims, proofs })
    }

    fn bind(
        &self,
        expected: &ExpectedScalarInput,
        capture: String,
    ) -> Result<CheckedOriginalScalarProgram, String> {
        let bytes = byte_list(expected.module_bytes());
        let literal = Expr::nat_lit(expected.literal());
        let truth = Expr::apps(
            Expr::const_(Name::from_string("Eq.refl"), vec![Level::succ(Level::zero())]),
            [constant("Bool"), constant("Bool.true")],
        );
        // These are ordinary proof DATA. The kernel must reduce the complete
        // actual decoder/profile and actual closed range decision below.
        let decoded = Expr::apps(
            constant("SemRU64ScalarProfile.decode_profile"),
            [bytes.clone(), literal.clone(), truth.clone()],
        );
        let valid =
            Expr::apps(constant(&format!("{NAMESPACE}.literal_valid")), [literal.clone(), truth]);
        let mut encoded = Vec::new();
        for name in ["construction", "correspondence", "available"] {
            let proof = Expr::apps(
                constant(&format!("{NAMESPACE}.{name}")),
                [bytes.clone(), literal.clone(), decoded.clone(), valid.clone()],
            );
            let proof = encode_clean_expr_dag_v2(&proof).map_err(|e| e.to_string())?;
            if proof.len() > PROOF_BYTES {
                return Err("scalar program proof byte bound".into());
            }
            encoded.push(proof);
        }
        let packet = OriginalScalarProgramPacket {
            schema: PACKET_SCHEMA.into(),
            encoding: ENCODING.into(),
            capture_sha256: capture,
            subject: expected.binding.clone(),
            cohort_sha256: self.cohort.clone(),
            context: self.kernel.env_digest(),
            proofs: encoded.try_into().map_err(|_| "scalar program proof population")?,
        };
        self.check(expected, &packet.capture_sha256, &packet)
    }
}

impl CompilerInputCapture {
    /// Derive the byte subject only from independently supplied real current
    /// original Compiler input, after complete capture/configuration equality.
    /// This checks the actual model constructor, not Rust-to-IR refinement.
    pub fn bind_original_scalar_program_mathematics(
        &self,
        current: &CerInput<'_>,
        configuration: &CompilerCaptureConfig,
        symbol: &str,
        environment: &CanonicalScalarProgramEnvironment,
    ) -> Result<CheckedOriginalScalarProgram, String> {
        let (subject, capture) = self.current_scalar_input(current, configuration, symbol)?;
        environment.bind(&subject, capture)
    }

    pub fn replay_original_scalar_program_mathematics(
        &self,
        current: &CerInput<'_>,
        configuration: &CompilerCaptureConfig,
        symbol: &str,
        environment: &CanonicalScalarProgramEnvironment,
        packet: &OriginalScalarProgramPacket,
    ) -> Result<CheckedOriginalScalarProgram, String> {
        let (subject, capture) = self.current_scalar_input(current, configuration, symbol)?;
        environment.check(&subject, &capture, packet)
    }
}

#[cfg(test)]
mod tests;
