// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Initial selector DATA pulled from the SAME admitted Host job. The dedicated
//! native submission retains these selectors before dispatch; neither this
//! frame nor its carrier ACK creates any source/config/output/materialization
//! owner. Request114 is finalized only after their actual native offers.
use super::*;
use crate::bootstrap_graph::Key;
use crate::wire::Decoder;

pub const INTENT_PURPOSE: &str = "native-bootstrap-offline-intent-v1";

mod configured;
pub use configured::{ConfigurationSelection, ConfiguredIntentSelection};

#[derive(Clone, PartialEq, Eq)]
pub struct IntentQuery {
    pub key: Key,
}
impl IntentQuery {
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        let mut e = Encoder::new(124);
        self.key.write(&mut e)?;
        e.finish()
    }
    pub fn decode(bytes: &[u8]) -> io::Result<Self> {
        let mut d = header(bytes, 124)?;
        let value = Self { key: Key::read(&mut d)? };
        d.done()?;
        Ok(value)
    }
    pub fn hello(&self) -> io::Result<Vec<u8>> {
        self.key.hello(INTENT_PURPOSE)
    }
}

/// Initial pre-dispatch selectors only: the Root's support/graph nonces do
/// not exist yet. The Host must bind this DATA to the actual authorized
/// submission's cwd, complete environment, root attempt and original endpoint.
/// Never print the private caller environment. No owner is decoded here.
#[derive(Clone, PartialEq, Eq)]
pub struct IntentSelection {
    pub source_root: Vec<u8>,
    pub output_root: Vec<u8>,
    pub configured_targo: Vec<u8>,
    pub configured_compiler: Vec<u8>,
    pub environment: Vec<(Vec<u8>, Vec<u8>)>,
    pub budget_ns: u64,
}
impl IntentSelection {
    pub fn validate(&self) -> io::Result<()> {
        environment(&self.environment)?;
        for path in [
            &self.source_root,
            &self.output_root,
            &self.configured_targo,
            &self.configured_compiler,
        ] {
            if !absolute(path) {
                return Err(invalid());
            }
        }
        if self.source_root == self.output_root || !matches!(self.budget_ns, 1..=MAX_BUDGET_NS) {
            return Err(invalid());
        }
        Ok(())
    }
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        let mut e = Encoder::new(126);
        self.write(&mut e)?;
        e.finish()
    }
    pub fn decode(bytes: &[u8]) -> io::Result<Self> {
        let mut d = header(bytes, 126)?;
        let value = Self::read(&mut d)?;
        d.done()?;
        Ok(value)
    }
    fn write(&self, e: &mut Encoder) -> io::Result<()> {
        self.validate()?;
        e.bytes(&self.source_root)?;
        e.bytes(&self.output_root)?;
        e.bytes(&self.configured_targo)?;
        e.bytes(&self.configured_compiler)?;
        e.number(self.environment.len() as u64);
        for (name, value) in &self.environment {
            e.bytes(name)?;
            e.bytes(value)?;
        }
        e.number(self.budget_ns);
        Ok(())
    }
    fn read(d: &mut Decoder<'_>) -> io::Result<Self> {
        let source_root = d.bytes()?;
        let output_root = d.bytes()?;
        let configured_targo = d.bytes()?;
        let configured_compiler = d.bytes()?;
        let count = d.count(MAX_ITEMS)?;
        let mut environment = Vec::with_capacity(count);
        for _ in 0..count {
            environment.push((d.bytes()?, d.bytes()?));
        }
        let value = Self {
            source_root,
            output_root,
            configured_targo,
            configured_compiler,
            environment,
            budget_ns: d.number()?,
        };
        value.validate()?;
        Ok(value)
    }
}

/// The same submitted selectors bound only AFTER actual Root authentication
/// to its original support Key. This remains DATA, never a source/SDK owner.
#[derive(Clone, PartialEq, Eq)]
pub struct Intent {
    pub key: OperationKey,
    pub selection: IntentSelection,
}
impl Intent {
    pub fn validate(&self) -> io::Result<()> {
        self.key.validate()?;
        self.selection.validate()?;
        if self.key.sequence != 1 {
            return Err(invalid());
        }
        Ok(())
    }
    /// Equality/restriction only. A match does not authenticate Request's file
    /// identities, caches, GNU, SDK or actual enrolled original owners.
    pub fn matches_request(&self, request: &Request) -> io::Result<()> {
        self.validate()?;
        request.validate()?;
        let selected = &self.selection;
        if self.key != request.key
            || selected.source_root != request.source_root
            || selected.output_root != request.output_root
            || selected.configured_targo != request.configured_targo
            || selected.configured_compiler != request.configured_compiler
            || selected.environment != request.environment
            || request.budget_ns > selected.budget_ns
        {
            return Err(invalid());
        }
        Ok(())
    }
    fn write(&self, e: &mut Encoder) -> io::Result<()> {
        self.validate()?;
        self.key.write(e)?;
        self.selection.write(e)
    }
    fn read(d: &mut Decoder<'_>) -> io::Result<Self> {
        let value = Self { key: OperationKey::read(d)?, selection: IntentSelection::read(d)? };
        value.validate()?;
        Ok(value)
    }
}

/// Remaining time is an observation of the original Root endpoint, never a new
/// timer. A reconnect may reduce it but must return the SAME immutable intent.
#[derive(Clone, PartialEq, Eq)]
pub struct IntentReply {
    pub query: IntentQuery,
    pub intent: Intent,
    pub remaining_root_ns: u64,
}
impl IntentReply {
    fn validate(&self, query: &IntentQuery) -> io::Result<()> {
        self.query.key.validate()?;
        self.intent.validate()?;
        if &self.query != query
            || self.intent.key.graph != query.key
            || !matches!(self.remaining_root_ns, 1..=MAX_BUDGET_NS)
        {
            return Err(invalid());
        }
        Ok(())
    }
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        self.validate(&self.query)?;
        let mut e = Encoder::new(125);
        e.frame_bytes(&self.query.encode()?)?;
        self.intent.write(&mut e)?;
        e.number(self.remaining_root_ns);
        e.finish()
    }
    pub fn decode(bytes: &[u8], query: &IntentQuery) -> io::Result<Self> {
        let mut d = header(bytes, 125)?;
        let value = Self {
            query: IntentQuery::decode(&d.frame_bytes()?)?,
            intent: Intent::read(&mut d)?,
            remaining_root_ns: d.number()?,
        };
        d.done()?;
        value.validate(query)?;
        Ok(value)
    }
}

#[cfg(test)]
mod tests;
