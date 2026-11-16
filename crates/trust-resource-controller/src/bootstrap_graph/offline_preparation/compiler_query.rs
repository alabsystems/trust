// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Nested ordinary fetch compiler-query DATA, distinct from the control SDK's
//! narrow Bootstrap queries. The actual resident must authenticate the SAME
//! private Targo child, retain its parent phase and original input bundle, and
//! independently own a supplementary GNU loan, NoFork, reap and physical EOF.
//! No decoded command, sequence or successful output constructs those owners.

use super::{Request, environment_entries};
use crate::CommandSpec;
use crate::bootstrap_graph::query::{MAX_QUERY_NS, OperationKey};
use crate::resolver::classify_resolver_query;
use crate::wire::{Encoder, header, invalid};
use std::io;

/// Complete effective command observed by the actual private fetch child,
/// after its ordinary Cargo configuration. Configuration may change semantic
/// environment bytes; retain them exactly instead of substituting env6 or the
/// parent's pre-configuration environment. Native runtime overrides must still
/// match the SAME independently held compiler before any GO.
#[derive(Clone, PartialEq, Eq)]
pub struct CompilerQuery {
    pub sequence: u64,
    pub command: CommandSpec,
    /// Restricts the SAME original endpoint; receipt never starts a new timer.
    pub timeout_ns: u64,
}
impl CompilerQuery {
    pub fn validate_for(&self, original: &Request) -> io::Result<()> {
        original.validate()?;
        let command = &self.command;
        if self.sequence == 0
            || command.program != original.configured_compiler
            || command.cwd != original.source_root
            || command.arg0.is_some()
            || self.timeout_ns == 0
            || self.timeout_ns > MAX_QUERY_NS.min(original.budget_ns)
        {
            return Err(invalid());
        }
        // Reuse the maintained exact ordinary resolver grammar. It admits no
        // producing source, argfile, target JSON, backend or arbitrary argv.
        classify_resolver_query(&command.args)?;
        environment_entries(&command.environment)?;
        for (name, value) in &command.environment {
            let expected = match name.as_slice() {
                b"CARGO" => Some(&original.configured_targo),
                b"RUSTC" => Some(&original.configured_compiler),
                b"CARGO_HOME" => Some(&original.cargo_home),
                _ => None,
            };
            if expected.is_some_and(|expected| value != expected) {
                return Err(invalid());
            }
        }
        Ok(())
    }

    pub fn encode(&self, original: &Request, request_sha256: [u8; 32]) -> io::Result<Vec<u8>> {
        self.validate_for(original)?;
        let mut e = Encoder::new(116);
        e.number(1);
        original.key.write(&mut e)?;
        e.0.extend(request_sha256);
        e.number(self.sequence);
        e.bytes(&self.command.program)?;
        e.bytes(&self.command.cwd)?;
        e.number(self.command.args.len() as u64);
        for argument in &self.command.args {
            e.bytes(argument)?;
        }
        e.number(self.command.environment.len() as u64);
        for (name, value) in &self.command.environment {
            e.bytes(name)?;
            e.bytes(value)?;
        }
        e.number(self.timeout_ns);
        e.finish()
    }

    pub fn decode(bytes: &[u8], original: &Request, request_sha256: [u8; 32]) -> io::Result<Self> {
        original.validate()?;
        let mut d = header(bytes, 116)?;
        if d.number()? != 1
            || OperationKey::read(&mut d)? != original.key
            || d.array::<32>()? != request_sha256
        {
            return Err(invalid());
        }
        let sequence = d.number()?;
        let program = d.bytes()?;
        let cwd = d.bytes()?;
        let mut args = Vec::new();
        for _ in 0..d.count(32)? {
            args.push(d.bytes()?);
        }
        let mut environment = Vec::new();
        for _ in 0..d.count(crate::MAX_ITEMS)? {
            environment.push((d.bytes()?, d.bytes()?));
        }
        let timeout_ns = d.number()?;
        d.done()?;
        let value = Self {
            sequence,
            command: CommandSpec {
                program,
                arg0: None,
                args,
                environment,
                cwd,
            },
            timeout_ns,
        };
        value.validate_for(original)?;
        Ok(value)
    }
}

#[cfg(test)]
mod tests;
