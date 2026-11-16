// Copyright 2026 Andrew Yates | Apache-2.0
//! Conditional entry-step evidence, independently replayed by Clean.
//!
//! No value of this module is a function/output grade. A successful check is
//! conditional on the full canonical allocation and raw-memory image inputs;
//! it does not establish those inputs, instruction-PC equality or a call rely.

use std::io::{self, Write};

use clean_kernel::{Expr, ReferenceAccepted};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use trust_machine_sem::{MachineState, frame_pair};
use trust_types::Formula;

use crate::call_event::{CerInput, FunctionCertificate};
use crate::cer_memory_machine::BoundFunction;
use crate::original_conjunction_certificate::SubjectBinding;

mod caller;
pub(crate) mod cohort;
mod terms;
pub use caller::{
    CalleeFrameEnvironment, CallerFrameEnvironment, CheckedConditionalCallerFrame,
    CheckedSeparateCalleeFrame, ConditionalCallerFramePacket, SeparateCalleeFramePacket,
};
pub use cohort::FrameTheoremEnvironment;

const VERSION: u32 = 1;
const PROOF_BYTES: usize = 1 << 20;
const WIRE_BYTES: usize = 3 << 20;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct StepSubject {
    source: SubjectBinding,
    symbol: String,
    pc: u64,
    instruction: [u8; 4],
    state_sha256: String,
}
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ConditionalFramePacket {
    version: u32,
    subject: StepSubject,
    cohort_sha256: String,
    environment_sha256: String,
    goal_sha256: String,
    proof_sha256: String,
    proof: String,
}
pub struct CheckedConditionalFrameStep {
    packet: ConditionalFramePacket,
    _accepted: ReferenceAccepted,
}
impl CheckedConditionalFrameStep {
    pub fn packet(&self) -> &ConditionalFramePacket {
        &self.packet
    }
}

struct DigestWriter {
    hash: Sha256,
    count: usize,
}
impl Write for DigestWriter {
    fn write(&mut self, data: &[u8]) -> io::Result<usize> {
        self.count = self
            .count
            .checked_add(data.len())
            .filter(|n| *n <= WIRE_BYTES)
            .ok_or_else(|| io::Error::other("frame proof data bound"))?;
        self.hash.update(data);
        Ok(data.len())
    }
    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}
fn digest<T: Serialize + ?Sized>(value: &T) -> Result<String, String> {
    let mut w = DigestWriter { hash: Sha256::new(), count: 0 };
    serde_json::to_writer(&mut w, value).map_err(|e| e.to_string())?;
    Ok(format!("{:x}", w.hash.finalize()))
}
#[derive(Serialize)]
struct StateImage<'a> {
    gpr: &'a [Formula; 31],
    fpr: &'a [Formula; 32],
    sp: &'a Formula,
    pc: &'a Formula,
    memory: &'a Formula,
    flags: [&'a Formula; 4],
}
impl<'a> From<&'a MachineState> for StateImage<'a> {
    fn from(s: &'a MachineState) -> Self {
        Self {
            gpr: &s.gpr,
            fpr: &s.fpr,
            sp: &s.sp,
            pc: &s.pc,
            memory: &s.memory,
            flags: [&s.flags.n, &s.flags.z, &s.flags.c, &s.flags.v],
        }
    }
}

fn actual_step<'a>(
    input: &CerInput<'_>,
    certificate: &'a FunctionCertificate,
) -> Result<(frame_pair::CheckedPairEffects<'a>, StepSubject), String> {
    let pending =
        certificate.frame_execution.as_ref().ok_or("no actual CER memory observation retained")?;
    let source = SubjectBinding::from_input(input, certificate)?;
    if certificate.frame_step_subject.as_ref() != Some(&source) {
        return Err("actual CER frame entry source/P custody differs".into());
    }
    let bound =
        BoundFunction::bind(input.object, input.m_cg, &certificate.symbol, input.relocation_model)?;
    if digest(pending.binding())? != digest(bound.binding())?
        || certificate.extent != (bound.window().start, bound.window().end)
        || certificate.text_sha256 != bound.window().text_sha256()
    {
        return Err("frame step object/function binding differs".into());
    }
    let first = pending.steps().first().ok_or("no actual first instruction")?;
    if first.pc != bound.window().start
        || first.pc % 4 != 0
        || first.path != Formula::Bool(true)
        || bound.window().code.get(..4) != Some(first.instruction.as_slice())
        || first.memory_before != pending.entry().memory
        || first.pre_sp != pending.entry().sp
    {
        return Err("frame entry observation differs from actual bound entry".into());
    }
    let step = frame_pair::bind(first.instruction, first.pc, pending.entry())?;
    if step.effects() != first.effects.as_slice() || step.post().memory != first.memory_after {
        return Err("actual step effects or output memory differ".into());
    }
    let state_sha256 =
        digest(&(StateImage::from(step.pre()), StateImage::from(step.post()), &first.path))?;
    let subject = StepSubject {
        source,
        symbol: certificate.symbol.clone(),
        pc: first.pc,
        instruction: first.instruction,
        state_sha256,
    };
    Ok((step, subject))
}

impl FrameTheoremEnvironment {
    pub fn prove_entry_step(
        &self,
        input: &CerInput<'_>,
        certificate: &FunctionCertificate,
    ) -> Result<CheckedConditionalFrameStep, String> {
        let (step, subject) = actual_step(input, certificate)?;
        let goal = terms::build(&step)?;
        let proof = goal.produce();
        let accepted =
            self.kernel.check_closed_term(&goal.goal, &proof).map_err(|e| e.to_string())?;
        let encoded = serde_json::to_string(&proof).map_err(|e| e.to_string())?;
        if encoded.len() > PROOF_BYTES {
            return Err("frame proof exceeds transport bound".into());
        }
        let packet = ConditionalFramePacket {
            version: VERSION,
            subject,
            cohort_sha256: self.cohort.clone(),
            environment_sha256: cohort::hash(&self.kernel.env_digest().0),
            goal_sha256: digest(&goal.goal)?,
            proof_sha256: cohort::hash(encoded.as_bytes()),
            proof: encoded,
        };
        Ok(CheckedConditionalFrameStep { packet, _accepted: accepted })
    }
    /// Rebuild the exact expected object/state goal and check only the retained
    /// proof. No solver, code generator or proof-production entry is invoked.
    pub fn replay_entry_step(
        &self,
        packet: &ConditionalFramePacket,
        input: &CerInput<'_>,
    ) -> Result<CheckedConditionalFrameStep, String> {
        let observed = crate::call_event::observe_compiled_module_for_frame(input)
            .map_err(|e| e.to_string())?;
        let certificate = observed
            .certificates
            .iter()
            .find(|row| row.symbol == packet.subject.symbol)
            .ok_or("conditional frame packet symbol has no fresh actual observation")?;
        let (step, subject) = actual_step(input, certificate)?;
        if packet.version != VERSION
            || packet.subject != subject
            || packet.cohort_sha256 != self.cohort
            || packet.environment_sha256 != cohort::hash(&self.kernel.env_digest().0)
            || packet.proof.len() > PROOF_BYTES
            || packet.proof_sha256 != cohort::hash(packet.proof.as_bytes())
        {
            return Err("frame packet context/environment/proof binding differs".into());
        }
        let goal = terms::build(&step)?;
        if packet.goal_sha256 != digest(&goal.goal)? {
            return Err("frame packet original goal differs".into());
        }
        let proof: Expr = serde_json::from_str(&packet.proof).map_err(|e| e.to_string())?;
        let accepted =
            self.kernel.check_closed_term(&goal.goal, &proof).map_err(|e| e.to_string())?;
        Ok(CheckedConditionalFrameStep { packet: packet.clone(), _accepted: accepted })
    }
}
impl ConditionalFramePacket {
    pub fn to_bytes(&self) -> Result<Vec<u8>, String> {
        let _ = digest(self)?;
        serde_json::to_vec(self).map_err(|e| e.to_string())
    }
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, String> {
        if bytes.len() > WIRE_BYTES {
            return Err("frame packet exceeds byte bound".into());
        }
        serde_json::from_slice(bytes).map_err(|e| e.to_string())
    }
}

#[cfg(test)]
mod tests;
