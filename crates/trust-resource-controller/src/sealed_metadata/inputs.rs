use std::collections::BTreeSet;

use super::*;
use crate::{Status, StatusFrame};

const MAX_IMAGES: usize = 128;
const MAX_PATH_BYTES: usize = 4096;
const MAX_IMAGE_BYTES: u64 = 1024 * 1024 * 1024;
const MAX_TOTAL_BYTES: u64 = 4 * MAX_IMAGE_BYTES;

/// Data observed from original held bytes. These IDs/hashes confer no image,
/// admission, source/writer or proof authority when decoded.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MetadataFile {
    pub path: Vec<u8>,
    pub sha256: [u8; 32],
    pub bytes: u64,
    pub device: u64,
    pub inode: u64,
}

/// One pre-GO input inventory. `root` is the program/SDK root, distinct from
/// the original resource-root attempt. A later real Started event is mandatory.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MetadataPrepared {
    pub root_attempt: [u8; 16],
    pub member_attempt: [u8; 16],
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

/// Known process outcome after real scope retirement and the original input
/// recheck. Changed inputs invalidate the diagnostic comparison, preserving
/// the target's actual exit/signal/runtime and the independent retirement fact.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MetadataCompletion {
    pub finished: StatusFrame,
    pub inputs_unchanged: Result<(), String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MetadataEvent {
    Prepared(MetadataPrepared),
    Status(StatusFrame),
    Completed(MetadataCompletion),
}

fn attempts(root: [u8; 16], member: [u8; 16]) -> io::Result<()> {
    if root == [0; 16] || member == [0; 16] || root == member {
        Err(invalid())
    } else {
        Ok(())
    }
}
fn field(text: &str, maximum: usize) -> bool {
    !text.is_empty() && text.len() <= maximum && !text.chars().any(char::is_control)
}
fn path(bytes: &[u8], root: &[u8]) -> bool {
    bytes.len() <= MAX_PATH_BYTES
        && canonical_absolute(bytes)
        && bytes.starts_with(root)
        && bytes.get(root.len()) == Some(&b'/')
}
impl MetadataFile {
    pub(crate) fn validate(&self, root: &[u8]) -> io::Result<()> {
        if !path(&self.path, root)
            || self.bytes == 0
            || self.bytes > MAX_IMAGE_BYTES
            || self.inode == 0
        {
            return Err(invalid());
        }
        Ok(())
    }
    pub(crate) fn encode(&self, e: &mut Encoder) -> io::Result<()> {
        e.bytes(&self.path)?;
        e.0.extend(self.sha256);
        e.number(self.bytes);
        e.number(self.device);
        e.number(self.inode);
        Ok(())
    }
    pub(crate) fn decode(d: &mut crate::wire::Decoder<'_>) -> io::Result<Self> {
        Ok(Self {
            path: d.bytes()?,
            sha256: d.array()?,
            bytes: d.number()?,
            device: d.number()?,
            inode: d.number()?,
        })
    }
}
impl MetadataPrepared {
    fn validate(&self) -> io::Result<()> {
        attempts(self.root_attempt, self.member_attempt)?;
        if self.root.len() > MAX_PATH_BYTES
            || !canonical_absolute(&self.root)
            || !field(&self.policy, 256)
            || !field(&self.scope, 4096)
            || !field(&self.host, 256)
            || !field(&self.boot, 128)
            || self.runtime.len() > MAX_IMAGES
            || self.loader_paths.len() > 2
            || self.system_dependencies.len() > MAX_IMAGES
        {
            return Err(invalid());
        }
        let mut files = BTreeSet::new();
        let mut bytes = 0u64;
        for file in std::iter::once(&self.executable).chain(&self.runtime) {
            file.validate(&self.root)?;
            bytes = bytes.checked_add(file.bytes).ok_or_else(invalid)?;
            if !files.insert(&file.path) || bytes > MAX_TOTAL_BYTES {
                return Err(invalid());
            }
        }
        let mut paths = BTreeSet::new();
        for candidate in &self.loader_paths {
            if !path(candidate, &self.root) || !paths.insert(candidate) {
                return Err(invalid());
            }
        }
        let mut system = BTreeSet::new();
        for dependency in &self.system_dependencies {
            if !field(dependency, MAX_PATH_BYTES)
                || !canonical_absolute(dependency.as_bytes())
                || !system.insert(dependency)
            {
                return Err(invalid());
            }
        }
        Ok(())
    }
    pub fn validate_for(&self, request: &SealedMetadataRequest) -> io::Result<()> {
        self.validate()?;
        request.validate()?;
        if self.root_attempt != request.member.binding.root_attempt
            || self.member_attempt != request.member.member_attempt
            || self.root != request.root
            || self.executable.path != request.member.command.program
            || self.executable.sha256 != request.program_sha256
        {
            return Err(invalid());
        }
        Ok(())
    }
    /// Same actual input observation under the NEW resolver-query purpose.
    /// No role3 request is synthesized or accepted as a resolver member.
    pub fn validate_for_resolver(
        &self,
        request: &crate::resolver::SealedResolverQueryRequest,
    ) -> io::Result<()> {
        self.validate()?;
        request.validate()?;
        if self.root_attempt != request.member.binding.root_attempt
            || self.member_attempt != request.member.member_attempt
            || self.root != request.root
            || self.executable.path != request.member.command.program
            || self.executable.sha256 != request.program_sha256
        {
            return Err(invalid());
        }
        Ok(())
    }
    pub fn validate_for_workload_query(
        &self,
        request: &crate::workload::host::CompilerQuery,
    ) -> io::Result<()> {
        self.validate()?;
        request.validate()?;
        if self.root_attempt != request.member.binding.root_attempt
            || self.member_attempt != request.member.member_attempt
            || self.root != request.root
            || self.executable.path != request.member.command.program
            || self.executable.sha256 != request.program_sha256
        {
            return Err(invalid());
        }
        Ok(())
    }
    /// Paired query50/v2 binds the actual compiler in the complete plan. It
    /// never constructs an old query50/v1 or drops configured environment.
    pub fn validate_for_paired_query(
        &self,
        request: &crate::paired_qualification::query::CompilerQuery,
    ) -> io::Result<()> {
        self.validate()?;
        request.validate()?;
        let compiler = &request.invocation.consumer.compiler;
        if self.root_attempt != request.member.binding.root_attempt
            || self.member_attempt != request.member.member_attempt
            || self.root != request.invocation.consumer.root
            || self.executable.path != compiler.path
            || self.executable.sha256 != compiler.sha256
        {
            return Err(invalid());
        }
        Ok(())
    }
    /// Native107 query retains a distinct whole-job binding. This validates
    /// preparation DATA only; native owner/member/Root checks remain separate.
    pub fn validate_for_native_job_query(
        &self,
        request: &crate::native_job::query::CompilerQuery,
    ) -> io::Result<()> {
        self.validate()?;
        request.validate()?;
        if self.root_attempt != request.member.binding.root_attempt
            || self.member_attempt != request.member.member_attempt
            || self.root != request.sdk_root
            || self.executable.path != request.compiler.path
            || self.executable.sha256 != request.compiler.sha256
        {
            return Err(invalid());
        }
        Ok(())
    }
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        self.validate()?;
        let mut e = Encoder::new(13);
        e.0.extend(self.root_attempt);
        e.0.extend(self.member_attempt);
        for bytes in [
            &self.root[..],
            self.policy.as_bytes(),
            self.scope.as_bytes(),
            self.host.as_bytes(),
            self.boot.as_bytes(),
        ] {
            e.bytes(bytes)?;
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
        for dependency in &self.system_dependencies {
            e.bytes(dependency.as_bytes())?;
        }
        e.finish()
    }
    pub fn decode(bytes: &[u8], root: [u8; 16], member: [u8; 16]) -> io::Result<Self> {
        let mut d = header(bytes, 13)?;
        let root_attempt = d.array()?;
        let member_attempt = d.array()?;
        if root_attempt != root || member_attempt != member {
            return Err(invalid());
        }
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
        let value = Self {
            root_attempt,
            member_attempt,
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
        value.validate()?;
        Ok(value)
    }
}

impl MetadataCompletion {
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        if !matches!(self.finished.status, Status::Finished { .. }) {
            return Err(invalid());
        }
        let mut e = Encoder::new(14);
        e.bytes(&self.finished.encode()?)?;
        match &self.inputs_unchanged {
            Ok(()) => e.number(0),
            Err(reason) if field(reason, 4096) => {
                e.number(1);
                e.bytes(reason.as_bytes())?;
            }
            Err(_) => return Err(invalid()),
        }
        e.finish()
    }
    pub fn decode(bytes: &[u8], root: [u8; 16], member: [u8; 16]) -> io::Result<Self> {
        let mut d = header(bytes, 14)?;
        let finished = StatusFrame::decode(&d.bytes()?, root, member)?;
        let inputs_unchanged = match d.number()? {
            0 => Ok(()),
            1 => Err(d.text()?),
            _ => return Err(invalid()),
        };
        d.done()?;
        let value = Self {
            finished,
            inputs_unchanged,
        };
        value.encode()?;
        Ok(value)
    }
}
impl MetadataEvent {
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        match self {
            Self::Prepared(value) => value.encode(),
            Self::Completed(value) => value.encode(),
            Self::Status(value) if !matches!(value.status, Status::Finished { .. }) => {
                value.encode()
            }
            Self::Status(_) => Err(invalid()),
        }
    }
    pub fn decode(bytes: &[u8], root: [u8; 16], member: [u8; 16]) -> io::Result<Self> {
        if header(bytes, 13).is_ok() {
            return MetadataPrepared::decode(bytes, root, member).map(Self::Prepared);
        }
        if header(bytes, 14).is_ok() {
            return MetadataCompletion::decode(bytes, root, member).map(Self::Completed);
        }
        let status = StatusFrame::decode(bytes, root, member)?;
        if matches!(status.status, Status::Finished { .. }) {
            return Err(invalid());
        }
        Ok(Self::Status(status))
    }
}

#[cfg(test)]
mod tests;
