// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Non-producing compiler queries for the distinct paired purpose. Full60 is
//! equality data; only the live original owner can authenticate and admit it.
use std::io;

use super::PairedInvocation;
use crate::wire::{Encoder, header, invalid};
pub use crate::workload::host::{MAX_QUERIES, MAX_QUERY_NS, MAX_QUERY_OUTPUT};
use crate::{GnuTransport, MetadataPrepared, Request};

pub const QUERY_PURPOSE: &str = "sealed-paired-qualification-query-v1";

/// Actual observed command and the complete plan authenticated at Ready49/v2.
/// The existing role6/env6 codec cannot decode this distinct 50/v2 envelope.
#[derive(Clone, PartialEq, Eq)]
pub struct CompilerQuery {
    pub member: Request,
    pub invocation: PairedInvocation,
}

fn tool_suffix(key: &[u8]) -> Option<&'static [u8]> {
    match key {
        b"CC_x86_64_unknown_linux_musl" => Some(b"/scripts/zig-cc-x86_64-linux-musl.sh"),
        b"CXX_x86_64_unknown_linux_musl" => Some(b"/scripts/zig-cxx-x86_64-linux-musl.sh"),
        b"AR_x86_64_unknown_linux_musl" => Some(b"/scripts/zig-ar.sh"),
        b"RANLIB_x86_64_unknown_linux_musl" => Some(b"/scripts/zig-ranlib.sh"),
        _ => None,
    }
}
fn base_key(key: &[u8]) -> bool {
    matches!(
        key,
        b"LANG" | b"LC_ALL" | b"CARGO" | b"RUSTC" | b"CARGO_HOME" | b"CARGO_CACHE_RUSTC_INFO"
    )
}
pub(crate) fn validate_member(member: &Request) -> io::Result<()> {
    crate::resolver::classify_resolver_query(&member.command.args)?;
    if !matches!(member.timeout_ns, Some(1..=MAX_QUERY_NS))
        || member.command.arg0.is_some()
        || member.delegations.cpu.is_none()
        || !matches!(member.delegations.gnu, GnuTransport::None)
        || !member.delegations.fences.is_empty()
        || !(6..=11).contains(&member.command.environment.len())
        || member.command.environment.iter().filter(|(name, _)| base_key(name)).count() != 6
        || member.command.environment.iter().any(|(key, _)| {
            !base_key(key) && key != b"SCCACHE_CACHE_SIZE" && tool_suffix(key).is_none()
        })
    {
        return Err(invalid());
    }
    Ok(())
}
/// Shared finite environment policy for actual ProcessBuilder observation.
/// This validates DATA only; it constructs no Request, CPU description, SDK
/// keeper or permission to execute. Callers retain native runtime checks.
pub fn validate_environment(
    invocation: &PairedInvocation,
    environment: &[(Vec<u8>, Vec<u8>)],
) -> io::Result<()> {
    invocation.validate()?;
    let consumer = &invocation.consumer;
    let mut names = std::collections::BTreeSet::new();
    if !(6..=11).contains(&environment.len())
        || environment.iter().filter(|(name, _)| base_key(name)).count() != 6
        || environment.iter().any(|(name, value)| {
            name.is_empty()
                || name.len() > crate::MAX_FIELD
                || name.contains(&0)
                || value.len() > crate::MAX_FIELD
                || value.contains(&0)
                || !names.insert(name)
        })
        || environment.iter().any(|(key, value)| match key.as_slice() {
            b"LANG" | b"LC_ALL" => value != b"C",
            b"CARGO" => value != &consumer.program.path,
            b"RUSTC" => value != &consumer.compiler.path,
            b"CARGO_HOME" => value != &consumer.cargo_home,
            b"CARGO_CACHE_RUSTC_INFO" => value != b"0",
            // Ordinary bounded config data, never a policy/loader key.
            b"SCCACHE_CACHE_SIZE" => {
                value.is_empty()
                    || value.len() > 64
                    || !value.iter().all(|b| b.is_ascii_alphanumeric() || *b == b'.')
            }
            _ => {
                let Some(suffix) = tool_suffix(key) else { return true };
                let mut expected = invocation.ay.root.clone();
                expected.extend_from_slice(suffix);
                value != &expected
            }
        })
    {
        return Err(invalid());
    }
    Ok(())
}
impl CompilerQuery {
    pub fn validate(&self) -> io::Result<()> {
        validate_environment(&self.invocation, &self.member.command.environment)?;
        self.member.validate_paired_query()?;
        let consumer = &self.invocation.consumer;
        let command = &self.member.command;
        if command.program != consumer.compiler.path
            || (command.cwd != consumer.cwd && command.cwd != self.invocation.ay.root)
        {
            return Err(invalid());
        }
        Ok(())
    }
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        self.validate()?;
        let mut e = Encoder::new(50);
        e.number(2);
        e.frame_bytes(&self.member.encode_paired_query()?)?;
        e.frame_bytes(&self.invocation.encode()?)?;
        e.finish()
    }
    pub fn decode(bytes: &[u8]) -> io::Result<Self> {
        let mut d = header(bytes, 50)?;
        if d.number()? != 2 {
            return Err(invalid());
        }
        let value = Self {
            member: Request::decode_paired_query(&d.frame_bytes()?)?,
            invocation: PairedInvocation::decode(&d.frame_bytes()?)?,
        };
        d.done()?;
        value.validate()?;
        Ok(value)
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
        Ok(format!(
            "{{\"version\":3,\"role\":\"{QUERY_PURPOSE}\",\"session\":\"{}\",\"attempt\":\"{attempt}\"}}",
            self.member.binding.session,
        ).into_bytes())
    }
    pub fn validate_prepared(&self, prepared: &MetadataPrepared) -> io::Result<()> {
        prepared.validate_for_paired_query(self)
    }
}

/// Exact paired query retirement and owning-wait measurements. Optional
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
        e.number(2);
        e.0.extend(self.invocation_sha256);
        e.frame_bytes(&self.completed.encode()?)?;
        e.frame_bytes(&self.observation.encode()?)?;
        e.finish()
    }
    /// Expected digest must be computed from the ORIGINAL authenticated full60
    /// preimage, never taken from this completion or the consumer40 subplan.
    pub fn decode(bytes: &[u8], query: &CompilerQuery, expected: [u8; 32]) -> io::Result<Self> {
        query.validate()?;
        let mut d = header(bytes, 55)?;
        if d.number()? != 2 || expected == [0; 32] {
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

#[cfg(test)]
pub(crate) mod tests;
