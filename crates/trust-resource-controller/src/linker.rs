// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Direct parent-unit linker loans. These are bounded transport observations,
//! never constructors of CPU, GNU, memory, SDK or quiescence authority.
use std::collections::BTreeSet;
use std::io;

use crate::wire::{Decoder, Encoder, header, invalid};
use crate::{BirthKind, Identity, Loan, MetadataCompletion, MetadataFile, Role};

pub const CAPABILITY: &str = "native-linker-loan-v1";
pub const REQUEST_TAG: u64 = 56;
pub const PREPARED_TAG: u64 = 57;
pub const COMPLETION_TAG: u64 = 58;
pub const MAX_OUTPUT: usize = 8 << 20;
const MAX_IMAGES: usize = 128;
const MAX_PATH: usize = 4096;
const MAX_TOTAL: u64 = 4 * 1024 * 1024 * 1024;

/// Shared restriction for direct native linker profiles. This validates
/// argument DATA only; no ordinary loan, CPU descriptor or runtime is minted.
///
/// # Errors
/// Refuses runtime plugin loading and opaque LLVM argument forwarding.
pub fn validate_arguments(arguments: &[Vec<u8>]) -> io::Result<()> {
    if arguments.iter().any(|arg| {
        let option = arg.strip_prefix(b"--").or_else(|| arg.strip_prefix(b"-"));
        option.is_some_and(|option| {
            option == b"load-pass-plugin"
                || option.starts_with(b"load-pass-plugin=")
                || option == b"mllvm"
                || option.starts_with(b"mllvm=")
        })
    }) {
        return Err(invalid());
    }
    Ok(())
}

/// Existing registered compiler continuation. The host must independently
/// authenticate that compiler, original primary and same SDK before admission.
#[derive(Clone, PartialEq, Eq)]
pub struct Request {
    pub member: crate::Request,
    pub root: Vec<u8>,
}
impl Request {
    pub fn loan(&self) -> io::Result<Loan> {
        match self.member.role {
            Role::MachOLinker(loan) => Ok(loan),
            _ => Err(invalid()),
        }
    }
    pub fn validate(&self) -> io::Result<()> {
        self.member.validate()?;
        self.loan()?;
        validate_arguments(&self.member.command.args)?;
        if self.root.len() > MAX_PATH
            || !crate::sealed_metadata::canonical_absolute(&self.root)
            || self.root == b"/"
            || self.member.command.program != [self.root.as_slice(), b"/bin/rust-lld"].concat()
            || self.member.command.arg0.is_some()
            || self.member.delegations.cpu.is_none_or(|fd| fd.target != 5)
        {
            return Err(invalid());
        }
        Ok(())
    }
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        self.validate()?;
        let mut e = Encoder::new(REQUEST_TAG);
        e.number(1);
        e.bytes(&self.root)?;
        e.frame_bytes(&self.member.encode()?)?;
        e.finish()
    }
    pub fn decode(bytes: &[u8]) -> io::Result<Self> {
        let mut d = header(bytes, REQUEST_TAG)?;
        if d.number()? != 1 {
            return Err(invalid());
        }
        let result = Self { root: d.bytes()?, member: crate::Request::decode(&d.frame_bytes()?)? };
        d.done()?;
        result.validate()?;
        Ok(result)
    }
    pub fn hello(&self) -> io::Result<Vec<u8>> {
        self.validate()?;
        Ok(format!(
            "{{\"version\":3,\"role\":\"{CAPABILITY}\",\"session\":\"{}\"}}",
            self.member.binding.session
        )
        .into_bytes())
    }
}

/// Actual suspended linker and held SDK images before GO. This is its own
/// versioned purpose; it cannot be decoded as metadata preparation 13.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Prepared {
    pub root_attempt: [u8; 16],
    pub member_attempt: [u8; 16],
    pub loan: Loan,
    pub identity: Identity,
    pub root: Vec<u8>,
    pub policy: String,
    pub scope: String,
    pub executable: MetadataFile,
    pub runtime: Vec<MetadataFile>,
    pub loader_paths: Vec<Vec<u8>>,
    pub system_dependencies: Vec<String>,
    pub host: String,
    pub boot: String,
}
fn text(value: &str, bound: usize) -> bool {
    !value.is_empty() && value.len() <= bound && !value.chars().any(char::is_control)
}
fn loan_valid(loan: Loan, root: [u8; 16], member: [u8; 16]) -> bool {
    root != [0; 16]
        && member != [0; 16]
        && root != member
        && loan.parent_attempt != [0; 16]
        && loan.parent_attempt != root
        && loan.parent_attempt != member
        && loan.nonce != [0; 16]
}
fn encode_loan(e: &mut Encoder, loan: Loan) {
    e.0.extend(loan.parent_attempt);
    e.0.extend(loan.nonce);
    e.number(loan.cpu_slot.into());
}
fn decode_loan(d: &mut Decoder<'_>) -> io::Result<Loan> {
    Ok(Loan { parent_attempt: d.array()?, nonce: d.array()?, cpu_slot: d.narrow()? })
}
impl Prepared {
    fn validate(&self) -> io::Result<()> {
        if !loan_valid(self.loan, self.root_attempt, self.member_attempt)
            || self.identity.pid == 0
            || self.identity.birth == 0
            || self.root.len() > MAX_PATH
            || !crate::sealed_metadata::canonical_absolute(&self.root)
            || self.root == b"/"
            || !text(&self.policy, 256)
            || !text(&self.scope, 4096)
            || !text(&self.host, 256)
            || !text(&self.boot, 128)
            || self.runtime.len() > MAX_IMAGES
            || self.loader_paths.len() > 2
            || self.system_dependencies.len() > MAX_IMAGES
            || self.executable.path != [self.root.as_slice(), b"/bin/rust-lld"].concat()
        {
            return Err(invalid());
        }
        let mut paths = BTreeSet::new();
        let mut objects = BTreeSet::new();
        let mut bytes = 0u64;
        for file in std::iter::once(&self.executable).chain(&self.runtime) {
            file.validate(&self.root)?;
            bytes = bytes.checked_add(file.bytes).ok_or_else(invalid)?;
            if !paths.insert(&file.path)
                || !objects.insert((file.device, file.inode))
                || bytes > MAX_TOTAL
            {
                return Err(invalid());
            }
        }
        let mut paths = BTreeSet::new();
        for path in &self.loader_paths {
            if !crate::sealed_metadata::canonical_absolute(path)
                || path.len() > MAX_PATH
                || !path.starts_with(&self.root)
                || path.get(self.root.len()) != Some(&b'/')
                || !paths.insert(path)
            {
                return Err(invalid());
            }
        }
        let mut libraries = BTreeSet::new();
        for path in &self.system_dependencies {
            if !text(path, MAX_PATH)
                || !crate::sealed_metadata::canonical_absolute(path.as_bytes())
                || !libraries.insert(path)
            {
                return Err(invalid());
            }
        }
        Ok(())
    }
    pub fn validate_for(&self, request: &Request) -> io::Result<()> {
        self.validate()?;
        request.validate()?;
        if self.root_attempt != request.member.binding.root_attempt
            || self.member_attempt != request.member.member_attempt
            || self.loan != request.loan()?
            || self.root != request.root
            || self.executable.path != request.member.command.program
        {
            return Err(invalid());
        }
        Ok(())
    }
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        self.validate()?;
        let mut e = Encoder::new(PREPARED_TAG);
        e.number(1);
        e.0.extend(self.root_attempt);
        e.0.extend(self.member_attempt);
        encode_loan(&mut e, self.loan);
        e.number(self.identity.pid.into());
        e.number(self.identity.birth);
        e.number(match self.identity.birth_kind {
            BirthKind::MacosWallMicroseconds => 1,
            BirthKind::LinuxStartTicks => 2,
        });
        for value in [
            self.root.as_slice(),
            self.policy.as_bytes(),
            self.scope.as_bytes(),
            self.host.as_bytes(),
            self.boot.as_bytes(),
        ] {
            e.bytes(value)?;
        }
        self.executable.encode(&mut e)?;
        e.number(self.runtime.len() as u64);
        for file in &self.runtime {
            file.encode(&mut e)?;
        }
        e.number(self.loader_paths.len() as u64);
        for path in &self.loader_paths {
            e.bytes(path)?;
        }
        e.number(self.system_dependencies.len() as u64);
        for path in &self.system_dependencies {
            e.bytes(path.as_bytes())?;
        }
        e.finish()
    }
    pub fn decode(bytes: &[u8], request: &Request) -> io::Result<Self> {
        let mut d = header(bytes, PREPARED_TAG)?;
        if d.number()? != 1 {
            return Err(invalid());
        }
        let root_attempt = d.array()?;
        let member_attempt = d.array()?;
        let loan = decode_loan(&mut d)?;
        let identity = Identity {
            pid: d.narrow()?,
            birth: d.number()?,
            birth_kind: match d.number()? {
                1 => BirthKind::MacosWallMicroseconds,
                2 => BirthKind::LinuxStartTicks,
                _ => return Err(invalid()),
            },
        };
        let root = d.bytes()?;
        let policy = d.text()?;
        let scope = d.text()?;
        let host = d.text()?;
        let boot = d.text()?;
        let executable = MetadataFile::decode(&mut d)?;
        let mut runtime = Vec::new();
        for _ in 0..d.count(MAX_IMAGES)? {
            runtime.push(MetadataFile::decode(&mut d)?);
        }
        let mut loader_paths = Vec::new();
        for _ in 0..d.count(2)? {
            loader_paths.push(d.bytes()?);
        }
        let mut system_dependencies = Vec::new();
        for _ in 0..d.count(MAX_IMAGES)? {
            system_dependencies.push(d.text()?);
        }
        d.done()?;
        let result = Self {
            root_attempt,
            member_attempt,
            loan,
            identity,
            root,
            policy,
            scope,
            executable,
            runtime,
            loader_paths,
            system_dependencies,
            host,
            boot,
        };
        result.validate_for(request)?;
        Ok(result)
    }
}

/// Original owning wait after actual loan retirement. Missing CPU/RSS samples
/// remain absent; decoding this record cannot retire a loan or mint a grant.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Completion {
    pub loan: Loan,
    pub completed: MetadataCompletion,
    pub observation: crate::accounting::Observation,
}
impl Completion {
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        let frame = &self.completed.finished;
        if !loan_valid(self.loan, frame.root_attempt, frame.member_attempt) {
            return Err(invalid());
        }
        let mut e = Encoder::new(COMPLETION_TAG);
        e.number(1);
        encode_loan(&mut e, self.loan);
        e.frame_bytes(&self.completed.encode()?)?;
        e.frame_bytes(&self.observation.encode()?)?;
        e.finish()
    }
    pub fn decode(bytes: &[u8], request: &Request) -> io::Result<Self> {
        request.validate()?;
        let mut d = header(bytes, COMPLETION_TAG)?;
        if d.number()? != 1 {
            return Err(invalid());
        }
        let loan = decode_loan(&mut d)?;
        let completed = MetadataCompletion::decode(
            &d.frame_bytes()?,
            request.member.binding.root_attempt,
            request.member.member_attempt,
        )?;
        let observation = crate::accounting::Observation::decode(&d.frame_bytes()?)?;
        d.done()?;
        if loan != request.loan()? {
            return Err(invalid());
        }
        let result = Self { loan, completed, observation };
        result.encode()?;
        Ok(result)
    }
}

#[cfg(test)]
pub(crate) mod tests;
