// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates
//! Closed non-producing compiler query for the entire native job. Equality
//! data cannot establish its actual Root, bank or SDK custody.
use crate::wire::{Encoder, header, invalid};
use crate::{Request, Role};
use std::io;
pub const QUERY_PURPOSE: &str = "sealed-native-job-query-v1";
#[derive(Clone, PartialEq, Eq)]
pub struct CompilerQuery {
    pub member: Request,
    /// Equality to the whole original106 preimage retained by the live Host.
    /// Compactness permits sharing a graph without cloning it for each query.
    pub plan_sha256: [u8; 32],
    pub sdk_root: Vec<u8>,
    pub compiler: crate::workload::InputFile,
}
impl CompilerQuery {
    pub fn validate(&self) -> io::Result<()> {
        self.member.validate()?;
        if self.member.role != Role::WorkloadQuery
            || self.plan_sha256 == [0; 32]
            || !super::path(&self.sdk_root)
            || self.compiler.path != [self.sdk_root.as_slice(), b"/bin/trustc"].concat()
            || self.compiler.sha256 == [0; 32]
            || self.member.command.program != self.compiler.path
        {
            return Err(invalid());
        }
        crate::resolver::classify_resolver_query(&self.member.command.args)?;
        Ok(())
    }
    pub fn hello(&self) -> io::Result<Vec<u8>> {
        self.validate()?;
        let attempt = self
            .member
            .binding
            .root_attempt
            .iter()
            .map(|byte| format!("{byte:02x}"))
            .collect::<String>();
        Ok(format!("{{\"version\":3,\"role\":\"{QUERY_PURPOSE}\",\"session\":\"{}\",\"attempt\":\"{attempt}\"}}",self.member.binding.session).into_bytes())
    }
    pub fn validate_prepared(&self, prepared: &crate::MetadataPrepared) -> io::Result<()> {
        prepared.validate_for_native_job_query(self)
    }
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        self.validate()?;
        let mut e = Encoder::new(107);
        e.number(1);
        e.frame_bytes(&self.member.encode()?)?;
        e.0.extend(self.plan_sha256);
        e.bytes(&self.sdk_root)?;
        super::write_file(&self.compiler, &mut e)?;
        e.finish()
    }
    pub fn decode(bytes: &[u8]) -> io::Result<Self> {
        let mut d = header(bytes, 107)?;
        if d.number()? != 1 {
            return Err(invalid());
        }
        let value = Self {
            member: Request::decode(&d.frame_bytes()?)?,
            plan_sha256: d.array()?,
            sdk_root: d.bytes()?,
            compiler: super::read_file(&mut d)?,
        };
        d.done()?;
        value.validate()?;
        Ok(value)
    }
}

/// Exact native-job query retirement and owning-wait measurements. Optional
/// measurements remain optional; the digest grants no resource or proof right.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Completion {
    pub invocation_sha256: [u8; 32],
    pub completed: crate::MetadataCompletion,
    pub observation: crate::accounting::Observation,
}
impl Completion {
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        if self.invocation_sha256 == [0; 32] {
            return Err(invalid());
        }
        let mut e = Encoder::new(55);
        e.number(3);
        e.0.extend(self.invocation_sha256);
        e.frame_bytes(&self.completed.encode()?)?;
        e.frame_bytes(&self.observation.encode()?)?;
        e.finish()
    }
    /// Expected digest must be computed from the ORIGINAL authenticated full106
    /// preimage, never taken from this completion or the other protocol subplan.
    pub fn decode(bytes: &[u8], query: &CompilerQuery, expected: [u8; 32]) -> io::Result<Self> {
        query.validate()?;
        let mut d = header(bytes, 55)?;
        if d.number()? != 3 || expected == [0; 32] || expected != query.plan_sha256 {
            return Err(invalid());
        }
        let invocation_sha256 = d.array()?;
        if invocation_sha256 != expected {
            return Err(invalid());
        }
        let value = Self {
            invocation_sha256,
            completed: crate::MetadataCompletion::decode(
                &d.frame_bytes()?,
                query.member.binding.root_attempt,
                query.member.member_attempt,
            )?,
            observation: crate::accounting::Observation::decode(&d.frame_bytes()?)?,
        };
        d.done()?;
        value.encode()?;
        Ok(value)
    }
}
