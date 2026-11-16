// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Separate closed metadata purpose. These bounded bytes describe a request;
//! actual native peer/image, original CPU/GNU and retained-memory custody still
//! belong to the custodian. Older hosts must refuse the distinct negotiation.

use std::io;

use crate::wire::{Encoder, header, invalid};
use crate::{GnuTransport, MAX_FIELD, MAX_PAYLOAD, Request, Role};

mod inputs;
pub use inputs::{MetadataCompletion, MetadataEvent, MetadataFile, MetadataPrepared};
mod batch;
pub use batch::{
    MetadataBatch, MetadataBatchReport, MetadataProbe, MetadataProbeCommand, MetadataResult,
    MetadataRunnerObservation,
};
mod failure;
pub use failure::{METADATA_EVENT_PREFIX_MAX_BYTES, MetadataFailureObservation};
/// Finite report DATA, distinct from every 1 MiB native control/event frame.
/// Six bounded inventories plus runner/outputs and one failed-stream prefix.
pub const METADATA_REPORT_MAX_BYTES: usize = (batch::MAX_PROBES + 2) * MAX_PAYLOAD;

pub const METADATA_CAPABILITY: &str = "sealed-metadata-v1";
pub const METADATA_REQUEST_ROLE: u64 = 3;
pub const METADATA_READY_ROLE: &str = "native-metadata-ready-v1";
pub const CONTEXT_SDK_CAPABILITY: &str = "inherited-sdk-keeper-v1";
pub const CONTEXT_SDK_ROLE: &str = "native-context-sdk-v1";
pub const METADATA_STARTUP_ARGUMENT: &str = "--resource-metadata-v1";
pub const METADATA_CAPABILITY_QUERY: [&str; 2] =
    ["--resource-capabilities", "--sealed-metadata-v1"];
/// Negotiation data only. A frontend may advertise this only after its actual
/// native service owns the matching host-backed execution path. Neither this
/// string nor a response creates a root, CPU/GNU or memory grant.
pub const METADATA_CAPABILITIES_JSON: &str = r#"{"version":3,"sealed_metadata":"sealed-metadata-v1","metadata_argument":"--resource-metadata-v1","metadata_role":3,"context_sdk":"inherited-sdk-keeper-v1","cpu_mode":"retained-fixed-one","memory_custody":"host-owned-v3","gnu_custody":"host-owned-zero-supplemental","max_runtime_ns":30000000000,"max_output_bytes":65536,"program_profile":"native-metadata/macho-arm64-sysroot-rpath-v1","input_scope":"held-load-command-input-observations/local-same-uid-no-name-writers/system-runtime-tcb"}"#;
pub const METADATA_MAX_OUTPUT: usize = 64 * 1024;
pub const METADATA_MAX_TIMEOUT_NS: u64 = 30_000_000_000;

/// Borrowing mode only. The host must retain and validate the actual original
/// grant; this tag creates no CPU credit and carries no numeric entitlement.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MetadataCpu {
    SharedBorrow,
    FixedBorrow,
}

/// An expected native program inside one canonical input root. The host must
/// independently open, hash and retain the program and complete admitted
/// native runtime, match the suspended kernel-loaded image, and retain every
/// owner through actual scope retirement. This is never a seal-writer claim.
#[derive(Clone, PartialEq, Eq)]
pub struct SealedMetadataRequest {
    pub member: Request,
    pub cpu: MetadataCpu,
    pub root: Vec<u8>,
    pub program_sha256: [u8; 32],
}

pub(crate) fn canonical_absolute(bytes: &[u8]) -> bool {
    bytes.len() <= MAX_FIELD
        && bytes.starts_with(b"/")
        && !bytes.contains(&0)
        && bytes.len() > 1
        && bytes[1..]
            .split(|byte| *byte == b'/')
            .all(|part| !part.is_empty() && part != b"." && part != b"..")
}

pub(crate) fn validate_member(member: &Request) -> io::Result<()> {
    let args = &member.command.args;
    let supported = matches!(args.as_slice(), [word] if word == b"-vV")
        || matches!(args.as_slice(), [first, second]
            if first == b"--print" && second == b"sysroot"
                || first == b"--unverified" && second == b"--version");
    if !supported
        || !matches!(member.timeout_ns, Some(1..=METADATA_MAX_TIMEOUT_NS))
        || matches!(member.delegations.gnu, GnuTransport::None)
        || !member.delegations.fences.is_empty()
        || member.command.arg0.is_some()
        || member
            .command
            .environment
            .iter()
            .any(|(key, value)| !matches!(key.as_slice(), b"LANG" | b"LC_ALL") || value != b"C")
    {
        return Err(invalid());
    }
    Ok(())
}

impl SealedMetadataRequest {
    /// Route only to the separately negotiated member purpose. Capability
    /// bytes remain in the binary request, never in this diagnostic selector.
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
            "{{\"version\":3,\"role\":\"{METADATA_CAPABILITY}\",\"session\":\"{}\",\"attempt\":\"{attempt}\"}}",
            self.member.binding.session,
        ).into_bytes())
    }

    pub fn validate(&self) -> io::Result<()> {
        self.member.validate()?;
        if self.member.role != Role::SealedMetadata
            || self.member.delegations.cpu.is_some() != (self.cpu == MetadataCpu::SharedBorrow)
            || !canonical_absolute(&self.root)
            || !canonical_absolute(&self.member.command.program)
            || !self.member.command.program.starts_with(&self.root)
            || self.member.command.program.get(self.root.len()) != Some(&b'/')
        {
            return Err(invalid());
        }
        Ok(())
    }

    pub fn encode(&self) -> io::Result<Vec<u8>> {
        self.validate()?;
        let member = self.member.encode()?;
        let mut e = Encoder::new(12);
        e.number(match self.cpu {
            MetadataCpu::SharedBorrow => 0,
            MetadataCpu::FixedBorrow => 1,
        });
        e.number(member.len() as u64);
        e.0.extend(member);
        e.bytes(&self.root)?;
        e.0.extend(self.program_sha256);
        e.finish()
    }

    pub fn decode(bytes: &[u8]) -> io::Result<Self> {
        let mut d = header(bytes, 12)?;
        let cpu = match d.number()? {
            0 => MetadataCpu::SharedBorrow,
            1 => MetadataCpu::FixedBorrow,
            _ => return Err(invalid()),
        };
        let length = d.count(MAX_PAYLOAD)?;
        let member = Request::decode(d.take(length)?)?;
        let root = d.bytes()?;
        let program_sha256 = d.array()?;
        d.done()?;
        let request = Self { member, cpu, root, program_sha256 };
        request.validate()?;
        Ok(request)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{CommandSpec, Delegations, Descriptor, JobBinding};

    pub(super) fn request(args: &[&[u8]]) -> SealedMetadataRequest {
        SealedMetadataRequest {
            member: Request {
                binding: JobBinding {
                    session: "s-ab".into(),
                    root_attempt: [1; 16],
                    capability: [2; 32],
                },
                member_attempt: [3; 16],
                role: Role::SealedMetadata,
                command: CommandSpec {
                    program: b"/sealed/bin/program".to_vec(),
                    arg0: None,
                    args: args.iter().map(|arg| arg.to_vec()).collect(),
                    environment: vec![(b"LC_ALL".to_vec(), b"C".to_vec())],
                    cwd: b"/input".to_vec(),
                },
                delegations: Delegations {
                    cpu: Some(Descriptor { source: 5, target: 3 }),
                    gnu: GnuTransport::NumericPipe {
                        read: Descriptor { source: 6, target: 4 },
                        write: Descriptor { source: 7, target: 5 },
                    },
                    fences: Vec::new(),
                },
                timeout_ns: Some(METADATA_MAX_TIMEOUT_NS),
            },
            root: b"/sealed".to_vec(),
            cpu: MetadataCpu::SharedBorrow,
            program_sha256: [4; 32],
        }
    }

    #[test]
    fn metadata_envelope_is_distinct_exact_and_bounded() {
        for args in [
            &[&b"-vV"[..]][..],
            &[&b"--print"[..], &b"sysroot"[..]][..],
            &[&b"--unverified"[..], &b"--version"[..]][..],
        ] {
            let original = request(args);
            let bytes = original.encode().unwrap();
            assert!(SealedMetadataRequest::decode(&bytes).unwrap() == original);
            assert!(Request::decode(&bytes).is_err());
            for end in 0..bytes.len() {
                assert!(SealedMetadataRequest::decode(&bytes[..end]).is_err());
            }
            let mut extra = bytes;
            extra.push(0);
            assert!(SealedMetadataRequest::decode(&extra).is_err());
        }
    }

    #[test]
    fn metadata_and_linker_roles_coexist_without_reinterpreting_each_other() {
        let metadata = request(&[b"-vV"]);
        assert_eq!(METADATA_REQUEST_ROLE, 3);
        assert_eq!(crate::MACHO_LINKER_REQUEST_ROLE, 4);
        let member = metadata.member.encode().unwrap();
        assert!(Request::decode(&member).unwrap().role == Role::SealedMetadata);
        let mut linker = metadata.member.clone();
        linker.role =
            Role::MachOLinker(crate::Loan { parent_attempt: [9; 16], nonce: [8; 16], cpu_slot: 0 });
        linker.delegations.gnu = GnuTransport::None;
        linker.command.args =
            ["-flavor", "darwin", "input.o", "--threads=1", "--thinlto-jobs=1", "--read-workers=0"]
                .map(|word| word.as_bytes().to_vec())
                .to_vec();
        let encoded = linker.encode().unwrap();
        assert!(Request::decode(&encoded).unwrap() == linker);
        assert!(SealedMetadataRequest::decode(&encoded).is_err());
        let mut invalid_metadata = metadata.clone();
        invalid_metadata.member = linker;
        assert!(invalid_metadata.encode().is_err());
        assert!(crate::Call::decode(&metadata.encode().unwrap()).is_err());
    }

    #[test]
    fn metadata_hello_is_exact_and_excludes_private_capability() {
        let request = request(&[b"-vV"]);
        assert_eq!(request.hello().unwrap(), b"{\"version\":3,\"role\":\"sealed-metadata-v1\",\"session\":\"s-ab\",\"attempt\":\"01010101010101010101010101010101\"}");
    }

    #[test]
    fn metadata_requires_original_transport_finite_limits_and_clean_environment() {
        let original = request(&[b"-vV"]);
        for alter in 0..12 {
            let mut changed = original.clone();
            match alter {
                0 => changed.member.timeout_ns = None,
                1 => changed.member.timeout_ns = Some(0),
                2 => changed.member.timeout_ns = Some(METADATA_MAX_TIMEOUT_NS + 1),
                3 => changed.member.delegations.cpu = None,
                4 => changed.member.delegations.gnu = GnuTransport::None,
                5 => changed.member.delegations.fences.push(Descriptor { source: 8, target: 6 }),
                6 => changed.member.command.args.push(b"input.rs".to_vec()),
                7 => changed.member.command.arg0 = Some(b"other".to_vec()),
                8 => changed
                    .member
                    .command
                    .environment
                    .push((b"DYLD_INSERT_LIBRARIES".to_vec(), b"/other".to_vec())),
                9 => changed.root = b"/sealed/..".to_vec(),
                10 => changed.member.command.program = b"/sealed-foreign/bin/program".to_vec(),
                11 => changed.member.role = Role::MetadataVersion,
                _ => unreachable!(),
            }
            assert!(changed.encode().is_err(), "accepted altered metadata field {alter}");
        }
        for args in [
            &[&b"--version"[..]][..],
            &[&b"-vV"[..], &b"--print"[..]][..],
            &[&b"--print=sysroot"[..]][..],
            &[&b"--unverified"[..], &b"build"[..]][..],
        ] {
            assert!(request(args).encode().is_err());
        }
    }

    #[test]
    fn existing_metadata_role_has_its_original_syntax() {
        let mut original = request(&[b"--version"]);
        original.member.role = Role::MetadataVersion;
        original.member.timeout_ns = None;
        original.member.delegations.cpu = None;
        original.member.delegations.gnu = GnuTransport::None;
        assert!(original.member.encode().is_ok());
        original.member.command.args = vec![b"--print".to_vec(), b"sysroot".to_vec()];
        assert!(original.member.encode().is_err());
    }

    #[test]
    fn fixed_mode_is_explicit_and_cannot_describe_shared_cpu_rights() {
        let mut fixed = request(&[b"-vV"]);
        fixed.cpu = MetadataCpu::FixedBorrow;
        assert!(fixed.encode().is_err());
        fixed.member.delegations.cpu = None;
        let bytes = fixed.encode().unwrap();
        assert!(SealedMetadataRequest::decode(&bytes).unwrap() == fixed);
        fixed.cpu = MetadataCpu::SharedBorrow;
        assert!(fixed.encode().is_err());
    }

    #[test]
    fn metadata_and_existing_telemetry_have_distinct_protocol_kinds() {
        let metadata = request(&[b"-vV"]);
        let query = crate::TelemetryQuery {
            query: crate::ContextQuery {
                binding: metadata.member.binding.clone(),
                call_attempt: [8; 16],
            },
        };
        assert!(SealedMetadataRequest::decode(&query.encode().unwrap()).is_err());
        assert!(crate::TelemetryQuery::decode(&metadata.encode().unwrap()).is_err());
    }
    #[test]
    fn sealed_metadata_cannot_route_through_the_legacy_member_call() {
        let request = request(&[b"-vV"]);
        assert!(request.encode().is_ok());
        assert!(crate::Call::decode(&request.member.encode().unwrap()).is_err());
        assert!(crate::Call::Member(Box::new(request.member)).encode().is_err());
    }
}
