// Copyright 2026 Andrew Yates | Apache-2.0
//! Conditional, source/object-bound save/call/restore evidence. The physical
//! call agreement and canonical entry/post representations remain unsupplied
//! premises. No function/source/ABI/SourceNoUB/shipping grade is constructed.
//! The decoded site is bound to object bytes, but equality to a live fetched
//! PC, entry-heap/OS custody, source execution and callee rely remain unproved.
use std::path::Path;

use clean_kernel::ReferenceKernel;
use trust_ir::proof::{decode_clean_expr_dag_v2, encode_clean_expr_dag_v2};

use super::*;

mod binding;
mod callee;
mod terms;
pub use callee::{CalleeFrameEnvironment, CheckedSeparateCalleeFrame, SeparateCalleeFramePacket};
const MANIFEST: &str = include_str!("caller/cohort.json");
const ROOT: &str = "SemRFrameCaller";
const THEOREM: &str = "SemR.MemoryEmbedding.FrameCaller.save_call_restore";
const ENCODING: &str = "clean.expr.lossless-dag.v2";

pub struct CallerFrameEnvironment {
    kernel: ReferenceKernel,
    cohort: String,
}
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ConditionalCallerFramePacket {
    version: u32,
    encoding: String,
    subject: binding::CallerSubject,
    cohort_sha256: String,
    environment_sha256: String,
    goal_sha256: String,
    proof_sha256: String,
    proof: Vec<u8>,
}
/// Constructed only by exact original-goal reference checking. This is a
/// conditional frame component and has no conversion to a function grade.
pub struct CheckedConditionalCallerFrame {
    packet: ConditionalCallerFramePacket,
    _accepted: ReferenceAccepted,
}
impl CheckedConditionalCallerFrame {
    pub fn packet(&self) -> &ConditionalCallerFramePacket {
        &self.packet
    }
}
impl ConditionalCallerFramePacket {
    pub fn to_bytes(&self) -> Result<Vec<u8>, String> {
        let _ = digest(self)?;
        serde_json::to_vec(self).map_err(|e| e.to_string())
    }
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, String> {
        if bytes.len() > WIRE_BYTES {
            return Err("caller frame wire byte bound".into());
        }
        serde_json::from_slice(bytes).map_err(|e| e.to_string())
    }
}
impl CallerFrameEnvironment {
    pub fn open(directory: &Path) -> Result<Self, String> {
        let (kernel, cohort) = super::cohort::open_unit(directory, MANIFEST, ROOT, THEOREM)?;
        Ok(Self { kernel, cohort })
    }
    pub fn cohort_digest(&self) -> &str {
        &self.cohort
    }
    pub fn prove_conditional_frame(
        &self,
        input: &CerInput<'_>,
        symbol: &str,
    ) -> Result<CheckedConditionalCallerFrame, String> {
        let report = crate::call_event::observe_compiled_module_for_frame(input)
            .map_err(|e| e.to_string())?;
        let certificate = report
            .certificates
            .iter()
            .find(|row| row.symbol == symbol)
            .ok_or("actual framed caller is absent")?;
        let trace = binding::bind(input, certificate)?;
        let goal = terms::build(&trace)?;
        let proof = goal.produce()?;
        let accepted =
            self.kernel.check_closed_term(&goal.goal, &proof).map_err(|e| e.to_string())?;
        let proof = encode_clean_expr_dag_v2(&proof).map_err(|e| e.to_string())?;
        if proof.len() > PROOF_BYTES {
            return Err("caller frame proof byte bound".into());
        }
        let packet = ConditionalCallerFramePacket {
            version: 1,
            encoding: ENCODING.into(),
            subject: trace.subject,
            cohort_sha256: self.cohort.clone(),
            environment_sha256: super::cohort::hash(&self.kernel.env_digest().0),
            goal_sha256: digest(&goal.goal)?,
            proof_sha256: super::cohort::hash(&proof),
            proof,
        };
        let _ = packet.to_bytes()?;
        Ok(CheckedConditionalCallerFrame { packet, _accepted: accepted })
    }
    /// Reconstruct actual source/P/spec/callbacks, exact byte/effect/state goals
    /// and check only retained DAG proof data. No proof producer/solver is called.
    pub fn replay_conditional_frame(
        &self,
        packet: &ConditionalCallerFramePacket,
        input: &CerInput<'_>,
    ) -> Result<CheckedConditionalCallerFrame, String> {
        if packet.version != 1
            || packet.encoding != ENCODING
            || packet.proof.len() > PROOF_BYTES
            || packet.proof_sha256 != super::cohort::hash(&packet.proof)
            || packet.cohort_sha256 != self.cohort
            || packet.environment_sha256 != super::cohort::hash(&self.kernel.env_digest().0)
        {
            return Err("caller frame proof/cohort/environment/encoding differs".into());
        }
        let report = crate::call_event::observe_compiled_module_for_frame(input)
            .map_err(|e| e.to_string())?;
        let certificate = report
            .certificates
            .iter()
            .find(|row| row.symbol == packet.subject.symbol)
            .ok_or("fresh actual framed caller is absent")?;
        let trace = binding::bind(input, certificate)?;
        if trace.subject != packet.subject {
            return Err("caller/callee/object/source/P/state/census subject differs".into());
        }
        let goal = terms::build(&trace)?;
        if packet.goal_sha256 != digest(&goal.goal)? {
            return Err("caller frame original goal differs".into());
        }
        let proof = decode_clean_expr_dag_v2(&packet.proof).map_err(|e| e.to_string())?;
        let accepted =
            self.kernel.check_closed_term(&goal.goal, &proof).map_err(|e| e.to_string())?;
        Ok(CheckedConditionalCallerFrame { packet: packet.clone(), _accepted: accepted })
    }
}
#[cfg(test)]
mod tests;
