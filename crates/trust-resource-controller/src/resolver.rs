//! Separately negotiated native dependency resolution. Existing metadata
//! purposes remain closed. Decoded plans and requests create no resource grant.

use std::io;

use crate::wire::{Encoder, header, invalid};
use crate::{GnuTransport, MAX_PAYLOAD, Request, Role};

mod profile;
mod report;
pub fn private_environment_channel(name: &[u8]) -> bool {
    report::is_private_environment(name)
}
pub use profile::{ResolverCrateType, ResolverQueryKind, classify_resolver_query};
pub use report::{RESOLVER_REPORT_MAX_BYTES, ResolverQueryObservation, ResolverReport};

pub const RESOLVER_STARTUP_ARGUMENT: &str = "--resource-resolver-v1";
pub const RESOLVER_READY_ROLE: &str = "native-resolver-ready-v1";
pub const RESOLVER_CAPABILITY: &str = "sealed-resolver-v1";
pub const RESOLVER_QUERY_CAPABILITY: &str = "sealed-resolver-query-v1";
pub const RESOLVER_QUERY_ENVIRONMENT: &str = "resolver-root-fixed-env4-v1";
pub const RESOLVER_QUERY_PROFILE: &str = "targo-metadata-host-queries-v1";
pub const RESOLVER_REQUEST_ROLE: u64 = 5;
pub const RESOLVER_MAX_QUERY_NS: u64 = 30_000_000_000;
pub const RESOLVER_MAX_QUERY_OUTPUT: usize = 64 * 1024;
pub const RESOLVER_MAX_QUERIES: usize = 16;
pub const RESOLVER_MAX_METADATA: usize = 64 * 1024 * 1024;
pub const RESOLVER_SEMANTIC_ARGUMENTS: &[&[u8]] =
    &[b"metadata", b"--locked", b"--offline", b"--format-version", b"1"];
/// Fixed negotiation data. A reply or a decoded count creates no SDK, CPU,
/// GNU, memory, execution or release authority.
pub const RESOLVER_CAPABILITIES_JSON: &str = r#"{"version":3,"sealed_resolver":"sealed-resolver-v1","resolver_argument":"--resource-resolver-v1","query_purpose":"sealed-resolver-query-v1","query_role":5,"query_profile":"targo-metadata-host-queries-v1","query_environment":"resolver-root-fixed-env4-v1","context_sdk":"inherited-sdk-keeper-v1","cpu_mode":"retained-fixed-one","gnu_custody":"host-owned-zero-supplemental","memory_custody":"host-owned-v3","max_query_runtime_ns":30000000000,"max_query_output_bytes":65536,"max_queries":16,"max_metadata_bytes":67108864,"program_profile":"native-metadata/macho-arm64-sysroot-rpath-v1","input_scope":"held-load-command-input-observations/local-same-uid-no-name-writers/system-runtime-tcb"}"#;

/// A native binary's fixed support declaration, never a resource grant.
pub const RESOLVER_PROTOCOL_MARKER: [u8; 64] = protocol_marker();
const fn protocol_marker() -> [u8; 64] {
    let mut bytes = [0; 64];
    let magic = *b"TRUSTRESOLVER001";
    let mut index = 0;
    while index < magic.len() {
        bytes[index] = magic[index];
        index += 1;
    }
    let fields = [3u64, RESOLVER_REQUEST_ROLE, 32, 33, 34, 1];
    let mut field = 0;
    while field < fields.len() {
        let value = fields[field].to_be_bytes();
        let mut byte = 0;
        while byte < value.len() {
            bytes[16 + field * 8 + byte] = value[byte];
            byte += 1;
        }
        field += 1;
    }
    bytes
}

fn path(value: &[u8]) -> bool {
    value.len() > 1
        && value.len() <= 4096
        && value.starts_with(b"/")
        && !value.contains(&0)
        && value[1..]
            .split(|byte| *byte == b'/')
            .all(|part| !part.is_empty() && part != b"." && part != b"..")
}

/// One exact sealed Targo's normal resolver. No caller-selectable command,
/// features, compiler flags, dependency omission or resource counts are stored.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResolverInvocation {
    pub host_store: Option<Vec<u8>>,
    pub root: Vec<u8>,
    pub program: Vec<u8>,
    pub program_sha256: [u8; 32],
    pub compiler: Vec<u8>,
    pub compiler_sha256: [u8; 32],
    pub cwd: Vec<u8>,
    pub cargo_home: Vec<u8>,
}

impl ResolverInvocation {
    pub fn validate(&self) -> io::Result<()> {
        let mut targo = self.root.clone();
        targo.extend_from_slice(b"/bin/targo");
        let mut compiler = self.root.clone();
        compiler.extend_from_slice(b"/bin/trustc");
        if !path(&self.root)
            || !path(&self.cwd)
            || !path(&self.cargo_home)
            || self.host_store.as_deref().is_some_and(|store| !path(store))
            || self.program != targo
            || self.compiler != compiler
        {
            return Err(invalid());
        }
        Ok(())
    }

    pub fn encode(&self) -> io::Result<Vec<u8>> {
        self.validate()?;
        let mut e = Encoder::new(32);
        match &self.host_store {
            None => e.number(0),
            Some(store) => {
                e.number(1);
                e.bytes(store)?;
            }
        }
        e.bytes(&self.root)?;
        e.bytes(&self.program)?;
        e.0.extend(self.program_sha256);
        e.bytes(&self.compiler)?;
        e.0.extend(self.compiler_sha256);
        e.bytes(&self.cwd)?;
        e.bytes(&self.cargo_home)?;
        e.finish()
    }

    pub fn decode(bytes: &[u8]) -> io::Result<Self> {
        let mut d = header(bytes, 32)?;
        let host_store = match d.number()? {
            0 => None,
            1 => Some(d.bytes()?),
            _ => return Err(invalid()),
        };
        let value = Self {
            host_store,
            root: d.bytes()?,
            program: d.bytes()?,
            program_sha256: d.array()?,
            compiler: d.bytes()?,
            compiler_sha256: d.array()?,
            cwd: d.bytes()?,
            cargo_home: d.bytes()?,
        };
        d.done()?;
        value.validate()?;
        Ok(value)
    }
}

/// Native fixed-one query member under an already-ready resolver root. The
/// host must check the actual original root/SDK/CPU/GNU/memory independently.
#[derive(Clone, PartialEq, Eq)]
pub struct SealedResolverQueryRequest {
    pub member: Request,
    pub root: Vec<u8>,
    pub program_sha256: [u8; 32],
}

pub(crate) fn validate_member(member: &Request) -> io::Result<()> {
    classify_resolver_query(&member.command.args)?;
    if !matches!(member.timeout_ns, Some(1..=RESOLVER_MAX_QUERY_NS))
        || member.command.arg0.is_some()
        || member.delegations.cpu.is_some()
        || !matches!(member.delegations.gnu, GnuTransport::NumericPipe { .. })
        || !member.delegations.fences.is_empty()
        || member.command.environment.len() != 6
        || member
            .command
            .environment
            .iter()
            .map(|(name, _)| name)
            .collect::<std::collections::BTreeSet<_>>()
            .len()
            != 6
        || member.command.environment.iter().any(|(name, value)| match name.as_slice() {
            b"LANG" | b"LC_ALL" => value != b"C",
            b"CARGO" => !path(value),
            b"RUSTC" => value != &member.command.program,
            b"CARGO_HOME" => !path(value),
            b"CARGO_CACHE_RUSTC_INFO" => value != b"0",
            _ => true,
        })
    {
        return Err(invalid());
    }
    Ok(())
}

impl SealedResolverQueryRequest {
    /// Bind actual held input observations without creating a legacy-role request.
    pub fn validate_prepared(&self, prepared: &crate::MetadataPrepared) -> io::Result<()> {
        prepared.validate_for_resolver(self)
    }
    pub fn validate(&self) -> io::Result<()> {
        self.member.validate()?;
        let mut compiler = self.root.clone();
        compiler.extend_from_slice(b"/bin/trustc");
        let mut targo = self.root.clone();
        targo.extend_from_slice(b"/bin/targo");
        if self.member.role != Role::ResolverQuery
            || !path(&self.root)
            || self.member.command.program != compiler
            || self
                .member
                .command
                .environment
                .iter()
                .any(|(name, value)| name == b"CARGO" && value != &targo)
        {
            return Err(invalid());
        }
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
        Ok(format!("{{\"version\":3,\"role\":\"{RESOLVER_QUERY_CAPABILITY}\",\"session\":\"{}\",\"attempt\":\"{attempt}\"}}",
            self.member.binding.session).into_bytes())
    }
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        self.validate()?;
        let member = self.member.encode()?;
        let mut e = Encoder::new(33);
        e.number(member.len() as u64);
        e.0.extend(member);
        e.bytes(&self.root)?;
        e.0.extend(self.program_sha256);
        e.finish()
    }
    pub fn decode(bytes: &[u8]) -> io::Result<Self> {
        let mut d = header(bytes, 33)?;
        let length = d.count(MAX_PAYLOAD)?;
        let member = Request::decode(d.take(length)?)?;
        let value = Self { member, root: d.bytes()?, program_sha256: d.array()? };
        d.done()?;
        value.validate()?;
        Ok(value)
    }
}

#[cfg(test)]
mod tests;
