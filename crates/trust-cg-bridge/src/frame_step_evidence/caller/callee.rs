// Copyright 2026 Andrew Yates | Apache-2.0
//! Retained proof for actual callee data effects, conditional on destination
//! separation. No entry ABI, source NoUB, physical execution or function grade.
use std::path::Path;

use clean_kernel::ReferenceKernel;
use trust_ir::proof::{decode_clean_expr_dag_v2, encode_clean_expr_dag_v2};

use super::super::*;

mod binding;
mod terms;

const MANIFEST: &str = include_str!("callee/cohort.json");
const ROOT: &str = "SemRFrameCaller";
const THEOREM: &str = "SemR.MemoryEmbedding.FrameCaller.separate_store_agreement";
const ENCODING: &str = "clean.expr.lossless-dag.v2";

pub struct CalleeFrameEnvironment {
    kernel: ReferenceKernel,
    cohort: String,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SeparateCalleeFramePacket {
    version: u32,
    encoding: String,
    subject: binding::CalleeSubject,
    cohort_sha256: String,
    environment_sha256: String,
    goal_sha256: String,
    proof_sha256: String,
    proof: Vec<u8>,
}

/// A private checked component. The address-separation obligation remains in
/// its closed proposition; no conversion to a caller/function grade exists.
pub struct CheckedSeparateCalleeFrame {
    packet: SeparateCalleeFramePacket,
    _accepted: ReferenceAccepted,
}

impl CheckedSeparateCalleeFrame {
    pub fn packet(&self) -> &SeparateCalleeFramePacket {
        &self.packet
    }
}

impl SeparateCalleeFramePacket {
    pub fn to_bytes(&self) -> Result<Vec<u8>, String> {
        let _ = digest(self)?;
        serde_json::to_vec(self).map_err(|error| error.to_string())
    }

    pub fn from_bytes(bytes: &[u8]) -> Result<Self, String> {
        if bytes.len() > WIRE_BYTES {
            return Err("callee frame wire byte bound".into());
        }
        serde_json::from_slice(bytes).map_err(|error| error.to_string())
    }
}

impl CalleeFrameEnvironment {
    pub fn open(directory: &Path) -> Result<Self, String> {
        let (kernel, cohort) = super::super::cohort::open_unit(directory, MANIFEST, ROOT, THEOREM)?;
        Ok(Self { kernel, cohort })
    }

    pub fn cohort_digest(&self) -> &str {
        &self.cohort
    }

    pub fn prove_separate_callee(
        &self,
        input: &CerInput<'_>,
        caller: &str,
    ) -> Result<CheckedSeparateCalleeFrame, String> {
        let trace = binding::observe(input, caller)?;
        let goal = terms::build(&trace)?;
        let proof = goal.produce()?;
        let accepted =
            self.kernel.check_closed_term(&goal.goal, &proof).map_err(|error| error.to_string())?;
        let proof = encode_clean_expr_dag_v2(&proof).map_err(|error| error.to_string())?;
        if proof.len() > PROOF_BYTES {
            return Err("callee frame proof byte bound".into());
        }
        let packet = SeparateCalleeFramePacket {
            version: 1,
            encoding: ENCODING.into(),
            subject: trace.subject,
            cohort_sha256: self.cohort.clone(),
            environment_sha256: super::super::cohort::hash(&self.kernel.env_digest().0),
            goal_sha256: digest(&goal.goal)?,
            proof_sha256: super::super::cohort::hash(&proof),
            proof,
        };
        let _ = packet.to_bytes()?;
        Ok(CheckedSeparateCalleeFrame { packet, _accepted: accepted })
    }

    /// Rebind the actual source, caller/callee bytes, placements and symbolic
    /// data-effect trace, then check retained proof bytes in this fresh kernel.
    /// Observation never invokes a solver or a proof-producing verification.
    pub fn replay_separate_callee(
        &self,
        packet: &SeparateCalleeFramePacket,
        input: &CerInput<'_>,
    ) -> Result<CheckedSeparateCalleeFrame, String> {
        if packet.version != 1
            || packet.encoding != ENCODING
            || packet.proof.len() > PROOF_BYTES
            || packet.proof_sha256 != super::super::cohort::hash(&packet.proof)
            || packet.cohort_sha256 != self.cohort
            || packet.environment_sha256 != super::super::cohort::hash(&self.kernel.env_digest().0)
        {
            return Err("callee proof/cohort/environment/encoding differs".into());
        }
        let trace = binding::observe(input, &packet.subject.caller.symbol)?;
        if trace.subject != packet.subject {
            return Err("actual callee source/P/caller/bytes/effects/state differs".into());
        }
        let goal = terms::build(&trace)?;
        if packet.goal_sha256 != digest(&goal.goal)? {
            return Err("callee frame original goal differs".into());
        }
        let proof = decode_clean_expr_dag_v2(&packet.proof).map_err(|error| error.to_string())?;
        let accepted =
            self.kernel.check_closed_term(&goal.goal, &proof).map_err(|error| error.to_string())?;
        Ok(CheckedSeparateCalleeFrame { packet: packet.clone(), _accepted: accepted })
    }
}

#[cfg(test)]
mod tests;
