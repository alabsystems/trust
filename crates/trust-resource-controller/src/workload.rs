//! Closed native workload service data, separate from host admission.
//!
//! Decoding an invocation/continuation creates no root, output owner, resource
//! grant, proof authority or positive readiness. Existing request roles remain
//! closed; host-owned workload query/phase/member envelopes use another range.
use std::io;

use crate::wire::{Encoder, header, invalid};

pub mod budget;
pub mod host;
pub mod service;

pub const WORKLOAD_STARTUP_ARGUMENT: &str = "--resource-workload-v1";
/// Protocol spelling only. A live original host/root/SDK/output owner is still
/// required before any positive readiness or project/config/compiler work.
pub const WORKLOAD_CAPABILITY: &str = "sealed-workload-v1";
pub const WORKLOAD_READY_ROLE: &str = "native-workload-ready-v1";
pub const WORKLOAD_MEMBER_CAPABILITY: &str = "sealed-workload-member-v1";
/// Fixed support data only. The same held executable, live original host,
/// actually inherited lease set, SDK and output owners remain mandatory.
pub const WORKLOAD_PROTOCOL_MARKER: [u8; 64] =
    protocol_marker(*b"TRUSTWORKLOAD001", [3, 6, 7, 40, 48, 1]);
/// Additive protocol-support DATA only, never a grant or installed SDK receipt.
/// V1 all-domain startup/phase declarations remain unchanged.
pub const PARTIAL_CPU_PROTOCOL_MARKER: [u8; 64] =
    protocol_marker(*b"TRUSTPARTIAL0001", [3, 2, 51, 53, 1, 1]);
/// Distinct initial-pair support DATA. No Targo image may emit this until its
/// whole initial/current-share phase consumer is implemented and qualified.
pub const INITIAL_CPU_PROTOCOL_MARKER: [u8; 64] =
    protocol_marker(*b"TRUSTPARTINIT001", [3, 5, 48, 49, 2, 3]);
/// Compiler member-v2 includes original/bank/return support and direct linker
/// request56/preparation57/owning-wait58. Legacy helper-only members refuse.
/// This declaration grants no registered membership, custody or execution.
pub const WORKLOAD_MEMBER_PROTOCOL_MARKER: [u8; 64] =
    protocol_marker(*b"TRUSTMEMBER00002", [3, 2, 50, 56, 57, 58]);
const fn protocol_marker(magic: [u8; 16], fields: [u64; 6]) -> [u8; 64] {
    let mut output = [0; 64];
    let mut index = 0;
    while index < magic.len() {
        output[index] = magic[index];
        index += 1;
    }
    let mut field = 0;
    while field < fields.len() {
        let bytes = fields[field].to_be_bytes();
        let mut byte = 0;
        while byte < 8 {
            output[16 + field * 8 + byte] = bytes[byte];
            byte += 1;
        }
        field += 1;
    }
    output
}
pub const WORKLOAD_MAX_REPETITIONS: u32 = 32;
pub const WORKLOAD_MAX_CHECKPOINTS: u64 = 1 + 2 + 2 * WORKLOAD_MAX_REPETITIONS as u64;

fn path(value: &[u8]) -> bool {
    value.len() > 1
        && value.len() <= 4096
        && value.starts_with(b"/")
        && !value.contains(&0)
        && value[1..]
            .split(|byte| *byte == b'/')
            .all(|part| !part.is_empty() && part != b"." && part != b"..")
}
fn contains(root: &[u8], other: &[u8]) -> bool {
    other == root || (other.starts_with(root) && other.get(root.len()) == Some(&b'/'))
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InputFile {
    pub path: Vec<u8>,
    pub sha256: [u8; 32],
}

/// Fixed compiler selection: trust-vc-core's two realbody integration targets,
/// one normal unverified locked/offline compilation graph, complete discovery,
/// and the declared repeated samples. There is no arbitrary command/target,
/// requested CPU pool, output eligibility or serialized execution capability.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WorkloadInvocation {
    pub invocation: [u8; 16],
    /// Observed locator/equality data only. It must never select the host,
    /// manager store or SDK authority; those come from independent trusted
    /// startup configuration and the original selected SDK keeper.
    pub observed_host_store: Option<Vec<u8>>,
    pub root: Vec<u8>,
    pub program: InputFile,
    pub compiler: InputFile,
    pub cwd: Vec<u8>,
    pub cargo_home: Vec<u8>,
    pub output_root: Vec<u8>,
    pub refutation_step: InputFile,
    pub refutation_loop: InputFile,
    pub trust_spec_source: InputFile,
    pub repetitions: u32,
    pub timeout_ns: u64,
}
impl WorkloadInvocation {
    pub fn validate(&self) -> io::Result<()> {
        let mut program = self.root.clone();
        program.extend_from_slice(b"/bin/targo");
        let mut compiler = self.root.clone();
        compiler.extend_from_slice(b"/bin/trustc");
        if self.invocation == [0; 16]
            || !path(&self.root)
            || !path(&self.cwd)
            || !path(&self.cargo_home)
            || !path(&self.output_root)
            || self.observed_host_store.as_deref().is_some_and(|p| !path(p))
            || self.program.path != program
            || self.compiler.path != compiler
            || [&self.refutation_step, &self.refutation_loop, &self.trust_spec_source]
                .iter()
                .any(|input| !path(&input.path))
            || self.refutation_step.path == self.refutation_loop.path
            || !(1..=WORKLOAD_MAX_REPETITIONS).contains(&self.repetitions)
            || self.timeout_ns == 0
            || [&self.root, &self.cwd, &self.cargo_home].iter().any(|input| {
                contains(input, &self.output_root) || contains(&self.output_root, input)
            })
        {
            return Err(invalid());
        }
        Ok(())
    }
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        self.validate()?;
        let mut e = Encoder::new(40);
        e.number(1);
        e.0.extend(self.invocation);
        match &self.observed_host_store {
            None => e.number(0),
            Some(path) => {
                e.number(1);
                e.bytes(path)?;
            }
        }
        e.bytes(&self.root)?;
        for input in [&self.program, &self.compiler] {
            e.bytes(&input.path)?;
            e.0.extend(input.sha256);
        }
        e.bytes(&self.cwd)?;
        e.bytes(&self.cargo_home)?;
        e.bytes(&self.output_root)?;
        for input in [&self.refutation_step, &self.refutation_loop, &self.trust_spec_source] {
            e.bytes(&input.path)?;
            e.0.extend(input.sha256);
        }
        e.number(self.repetitions.into());
        e.number(self.timeout_ns);
        e.finish()
    }
    pub fn decode(bytes: &[u8]) -> io::Result<Self> {
        let mut d = header(bytes, 40)?;
        if d.number()? != 1 {
            return Err(invalid());
        }
        let invocation = d.array()?;
        let observed_host_store = match d.number()? {
            0 => None,
            1 => Some(d.bytes()?),
            _ => return Err(invalid()),
        };
        let root = d.bytes()?;
        let program = InputFile { path: d.bytes()?, sha256: d.array()? };
        let compiler = InputFile { path: d.bytes()?, sha256: d.array()? };
        let cwd = d.bytes()?;
        let cargo_home = d.bytes()?;
        let output_root = d.bytes()?;
        let refutation_step = InputFile { path: d.bytes()?, sha256: d.array()? };
        let refutation_loop = InputFile { path: d.bytes()?, sha256: d.array()? };
        let trust_spec_source = InputFile { path: d.bytes()?, sha256: d.array()? };
        let value = Self {
            invocation,
            observed_host_store,
            root,
            program,
            compiler,
            cwd,
            cargo_home,
            output_root,
            refutation_step,
            refutation_loop,
            trust_spec_source,
            repetitions: d.narrow()?,
            timeout_ns: d.number()?,
        };
        d.done()?;
        value.validate()?;
        Ok(value)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Decision {
    Continue,
    Stop,
}
/// Byte binding for one continuation of the SAME live root/graph. Matching this
/// data never creates a root/output owner or authorizes a produced program.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Continuation {
    pub invocation_sha256: [u8; 32],
    pub root_attempt: [u8; 16],
    pub checkpoint: u64,
    pub checkpoint_sha256: [u8; 32],
    pub decision: Decision,
}
impl Continuation {
    pub fn validate(&self) -> io::Result<()> {
        if self.root_attempt == [0; 16]
            || !(1..=WORKLOAD_MAX_CHECKPOINTS).contains(&self.checkpoint)
        {
            return Err(invalid());
        }
        Ok(())
    }
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        self.validate()?;
        let mut e = Encoder::new(43);
        e.number(1);
        e.0.extend(self.invocation_sha256);
        e.0.extend(self.root_attempt);
        e.number(self.checkpoint);
        e.0.extend(self.checkpoint_sha256);
        e.number(match self.decision {
            Decision::Continue => 1,
            Decision::Stop => 2,
        });
        e.finish()
    }
    pub fn decode(bytes: &[u8]) -> io::Result<Self> {
        let mut d = header(bytes, 43)?;
        if d.number()? != 1 {
            return Err(invalid());
        }
        let value = Self {
            invocation_sha256: d.array()?,
            root_attempt: d.array()?,
            checkpoint: d.number()?,
            checkpoint_sha256: d.array()?,
            decision: match d.number()? {
                1 => Decision::Continue,
                2 => Decision::Stop,
                _ => return Err(invalid()),
            },
        };
        d.done()?;
        value.validate()?;
        Ok(value)
    }
    pub fn check_binding(
        &self,
        invocation_sha256: [u8; 32],
        root_attempt: [u8; 16],
        checkpoint: u64,
        checkpoint_sha256: [u8; 32],
    ) -> io::Result<()> {
        self.validate()?;
        if self.invocation_sha256 != invocation_sha256
            || self.root_attempt != root_attempt
            || self.checkpoint != checkpoint
            || self.checkpoint_sha256 != checkpoint_sha256
        {
            return Err(invalid());
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests;
