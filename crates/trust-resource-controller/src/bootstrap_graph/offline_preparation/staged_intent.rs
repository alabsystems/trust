// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Distinct staged selector DATA: final programs follow actual native reservation.
//! These frames create no source, workspace, producer, Seed, SDK, execution or
//! deadline owner. The Host must bind the same authenticated Root and attempt,
//! retain its actual reserved namespace, and finalize selectors once before
//! configuration. Existing complete frame126 remains a separate contract.
use super::*;
use crate::bootstrap_graph::Key;
use crate::wire::Decoder;

pub const STAGED_INTENT_PURPOSE: &str = "native-bootstrap-offline-staged-intent-v1";
pub const PROGRAM_PURPOSE: &str = "native-bootstrap-offline-programs-v1";

fn operation(key: &OperationKey) -> io::Result<()> {
    key.validate()?;
    if key.sequence != 1 {
        return Err(invalid());
    }
    Ok(())
}

fn remaining(value: u64) -> io::Result<()> {
    if !matches!(value, 1..=MAX_BUDGET_NS) {
        return Err(invalid());
    }
    Ok(())
}

/// Initial source/output/policy restrictions only. Program names are not yet
/// selected. This DATA cannot reserve a namespace or reconstruct an owner.
#[derive(Clone, PartialEq, Eq)]
pub struct StagedSelection {
    pub source_root: Vec<u8>,
    pub output_root: Vec<u8>,
    pub environment: Vec<(Vec<u8>, Vec<u8>)>,
    pub budget_ns: u64,
}
impl StagedSelection {
    pub fn validate(&self) -> io::Result<()> {
        environment(&self.environment)?;
        if !absolute(&self.source_root)
            || !absolute(&self.output_root)
            || self.source_root == self.output_root
        {
            return Err(invalid());
        }
        remaining(self.budget_ns)
    }
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        let mut e = Encoder::new(128);
        self.write(&mut e)?;
        e.finish()
    }
    pub fn decode(bytes: &[u8]) -> io::Result<Self> {
        let mut d = header(bytes, 128)?;
        let value = Self::read(&mut d)?;
        d.done()?;
        Ok(value)
    }
    fn write(&self, e: &mut Encoder) -> io::Result<()> {
        self.validate()?;
        e.bytes(&self.source_root)?;
        e.bytes(&self.output_root)?;
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
        let count = d.count(MAX_ITEMS)?;
        let mut environment = Vec::with_capacity(count);
        for _ in 0..count {
            environment.push((d.bytes()?, d.bytes()?));
        }
        let value = Self { source_root, output_root, environment, budget_ns: d.number()? };
        value.validate()?;
        Ok(value)
    }
}

#[derive(Clone, PartialEq, Eq)]
pub struct StagedIntentQuery {
    pub key: Key,
}
impl StagedIntentQuery {
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        let mut e = Encoder::new(129);
        self.key.write(&mut e)?;
        e.finish()
    }
    pub fn decode(bytes: &[u8]) -> io::Result<Self> {
        let mut d = header(bytes, 129)?;
        let value = Self { key: Key::read(&mut d)? };
        d.done()?;
        Ok(value)
    }
    pub fn hello(&self) -> io::Result<Vec<u8>> {
        self.key.hello(STAGED_INTENT_PURPOSE)
    }
}

/// Same sequence-one attempt, bound by the Host only after actual Root checks.
/// Final program equality remains a separate required restriction.
#[derive(Clone, PartialEq, Eq)]
pub struct StagedIntent {
    pub key: OperationKey,
    pub selection: StagedSelection,
}
impl StagedIntent {
    pub fn validate(&self) -> io::Result<()> {
        operation(&self.key)?;
        self.selection.validate()
    }
    pub fn matches_request(&self, request: &Request) -> io::Result<()> {
        self.validate()?;
        request.validate()?;
        if self.key != request.key
            || self.selection.source_root != request.source_root
            || self.selection.output_root != request.output_root
            || self.selection.environment != request.environment
            || request.budget_ns > self.selection.budget_ns
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
        let value = Self { key: OperationKey::read(d)?, selection: StagedSelection::read(d)? };
        value.validate()?;
        Ok(value)
    }
}

/// Remaining time restricts the original endpoint; it never starts a new one.
#[derive(Clone, PartialEq, Eq)]
pub struct StagedIntentReply {
    pub query: StagedIntentQuery,
    pub intent: StagedIntent,
    pub remaining_root_ns: u64,
}
impl StagedIntentReply {
    fn validate(&self, query: &StagedIntentQuery) -> io::Result<()> {
        query.key.validate()?;
        self.intent.validate()?;
        remaining(self.remaining_root_ns)?;
        if &self.query != query
            || self.intent.key.graph != query.key
            || self.remaining_root_ns > self.intent.selection.budget_ns
        {
            return Err(invalid());
        }
        Ok(())
    }
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        self.validate(&self.query)?;
        let mut e = Encoder::new(130);
        e.frame_bytes(&self.query.encode()?)?;
        self.intent.write(&mut e)?;
        e.number(self.remaining_root_ns);
        e.finish()
    }
    pub fn decode(bytes: &[u8], query: &StagedIntentQuery) -> io::Result<Self> {
        let mut d = header(bytes, 130)?;
        let value = Self {
            query: StagedIntentQuery::decode(&d.frame_bytes()?)?,
            intent: StagedIntent::read(&mut d)?,
            remaining_root_ns: d.number()?,
        };
        d.done()?;
        value.validate(query)?;
        Ok(value)
    }
}

/// Exact final program spelling DATA. The Host authenticates its own actual
/// reservation and performs the one-use transition; decoding does neither.
#[derive(Clone, PartialEq, Eq)]
pub struct ProgramSelection {
    pub key: OperationKey,
    pub configured_targo: Vec<u8>,
    pub configured_compiler: Vec<u8>,
}
impl ProgramSelection {
    pub fn validate(&self) -> io::Result<()> {
        operation(&self.key)?;
        if !absolute(&self.configured_targo) || !absolute(&self.configured_compiler) {
            return Err(invalid());
        }
        Ok(())
    }
    pub fn matches_request(&self, request: &Request) -> io::Result<()> {
        self.validate()?;
        request.validate()?;
        if self.key != request.key
            || self.configured_targo != request.configured_targo
            || self.configured_compiler != request.configured_compiler
        {
            return Err(invalid());
        }
        Ok(())
    }
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        self.validate()?;
        let mut e = Encoder::new(131);
        self.key.write(&mut e)?;
        e.bytes(&self.configured_targo)?;
        e.bytes(&self.configured_compiler)?;
        e.finish()
    }
    pub fn decode(bytes: &[u8]) -> io::Result<Self> {
        let mut d = header(bytes, 131)?;
        let value = Self {
            key: OperationKey::read(&mut d)?,
            configured_targo: d.bytes()?,
            configured_compiler: d.bytes()?,
        };
        d.done()?;
        value.validate()?;
        Ok(value)
    }
    pub fn hello(&self) -> io::Result<Vec<u8>> {
        self.validate()?;
        self.key.graph.hello(PROGRAM_PURPOSE)
    }
}

fn program_namespace(selection: &ProgramSelection, namespace: &[u8]) -> io::Result<()> {
    selection.validate()?;
    if !absolute(namespace) {
        return Err(invalid());
    }
    let prefix = joined(namespace, b"bin/");
    for program in [&selection.configured_targo, &selection.configured_compiler] {
        let Some(leaf) = program.strip_prefix(prefix.as_slice()) else {
            return Err(invalid());
        };
        if leaf.is_empty() || leaf.contains(&b'/') {
            return Err(invalid());
        }
    }
    Ok(())
}

#[derive(Clone, PartialEq, Eq)]
pub struct ProgramSelectionReply {
    pub selection: ProgramSelection,
    pub namespace: Vec<u8>,
    pub remaining_root_ns: u64,
}
impl ProgramSelectionReply {
    fn validate(&self, selection: &ProgramSelection) -> io::Result<()> {
        selection.validate()?;
        program_namespace(&self.selection, &self.namespace)?;
        remaining(self.remaining_root_ns)?;
        if &self.selection != selection {
            return Err(invalid());
        }
        Ok(())
    }
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        self.validate(&self.selection)?;
        let mut e = Encoder::new(132);
        e.frame_bytes(&self.selection.encode()?)?;
        e.bytes(&self.namespace)?;
        e.number(self.remaining_root_ns);
        e.finish()
    }
    pub fn decode(bytes: &[u8], selection: &ProgramSelection) -> io::Result<Self> {
        let mut d = header(bytes, 132)?;
        let value = Self {
            selection: ProgramSelection::decode(&d.frame_bytes()?)?,
            namespace: d.bytes()?,
            remaining_root_ns: d.number()?,
        };
        d.done()?;
        value.validate(selection)?;
        Ok(value)
    }
}

/// Ask the same native attempt to reserve its actual child namespace once.
/// This frame is not a reservation, producer or source owner.
#[derive(Clone, PartialEq, Eq)]
pub struct ProgramSelectionQuery {
    pub key: OperationKey,
}
impl ProgramSelectionQuery {
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        operation(&self.key)?;
        let mut e = Encoder::new(133);
        self.key.write(&mut e)?;
        e.finish()
    }
    pub fn decode(bytes: &[u8]) -> io::Result<Self> {
        let mut d = header(bytes, 133)?;
        let value = Self { key: OperationKey::read(&mut d)? };
        d.done()?;
        operation(&value.key)?;
        Ok(value)
    }
    pub fn hello(&self) -> io::Result<Vec<u8>> {
        operation(&self.key)?;
        self.key.graph.hello(PROGRAM_PURPOSE)
    }
}

/// The Host's actual namespace/time observation DATA, never an owner decoder.
#[derive(Clone, PartialEq, Eq)]
pub struct ReservedPrograms {
    pub query: ProgramSelectionQuery,
    pub namespace: Vec<u8>,
    pub remaining_root_ns: u64,
}
impl ReservedPrograms {
    fn validate(&self, query: &ProgramSelectionQuery) -> io::Result<()> {
        operation(&query.key)?;
        operation(&self.query.key)?;
        remaining(self.remaining_root_ns)?;
        if &self.query != query || !absolute(&self.namespace) {
            return Err(invalid());
        }
        Ok(())
    }
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        self.validate(&self.query)?;
        let mut e = Encoder::new(134);
        e.frame_bytes(&self.query.encode()?)?;
        e.bytes(&self.namespace)?;
        e.number(self.remaining_root_ns);
        e.finish()
    }
    pub fn decode(bytes: &[u8], query: &ProgramSelectionQuery) -> io::Result<Self> {
        let mut d = header(bytes, 134)?;
        let value = Self {
            query: ProgramSelectionQuery::decode(&d.frame_bytes()?)?,
            namespace: d.bytes()?,
            remaining_root_ns: d.number()?,
        };
        d.done()?;
        value.validate(query)?;
        Ok(value)
    }
}

#[cfg(test)]
mod tests;
