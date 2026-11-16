//! A distinct AY+consumer plan, never an expansion of workload-v1/Invocation40.
//! These bytes declare inputs and observations. They cannot create a root,
//! materialization, source/SDK authentication, resource grant or proof verdict.
use std::io;

use crate::wire::{Encoder, header, invalid};
use crate::workload::{InputFile, WorkloadInvocation};

pub mod budget;
pub mod host;
pub mod query;
pub mod service;

pub const PAIRED_STARTUP_ARGUMENT: &str = "--resource-paired-qualification-v1";
pub const PAIRED_CAPABILITY: &str = "paired-qualification-v1";
pub const PAIRED_READY_ROLE: &str = "native-paired-qualification-ready-v1";
pub const PAIRED_INVOCATION_HASH_DOMAIN: &[u8] = b"trust.paired-qualification-invocation.v1\0";
/// Support declaration only. The original held executable, full authenticated
/// plan/SCM startup, SDK/output custody and live host remain mandatory. Revision2
/// also declares service61/v2 + checked compiler observations62/v3; the Host's
/// original held-image check rejects earlier declarations BEFORE Root GO.
pub const PAIRED_PROTOCOL_MARKER: [u8; 64] = marker();
const fn marker() -> [u8; 64] {
    let mut value = [0; 64];
    let magic = *b"TRUSTPAIRQUAL002";
    let mut index = 0;
    while index < 16 {
        value[index] = magic[index];
        index += 1;
    }
    let fields = [3u64, 6, 7, 60, 48, 2];
    let mut field = 0;
    while field < fields.len() {
        let bytes = fields[field].to_be_bytes();
        let mut byte = 0;
        while byte < 8 {
            value[16 + field * 8 + byte] = bytes[byte];
            byte += 1;
        }
        field += 1;
    }
    value
}

/// Fixed native AY library subject. The actual frontend retains and rebinds
/// its original Source/DependencyAttempt separately; Git IDs and file digests
/// here are equality DATA, never authority supplied by a service message.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AySubject {
    pub root: Vec<u8>,
    pub workspace_manifest: InputFile,
    pub crate_manifest: InputFile,
    pub lockfile: InputFile,
    pub cargo_config: InputFile,
    pub toolchain_config: InputFile,
    pub source_commit: [u8; 20],
    pub crate_tree: [u8; 20],
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PairedInvocation {
    /// Still exactly its two targets as DATA. Ready48/v2 must bind the FULL60
    /// plan, never this subplan's40 bytes or its digest. No arbitrary selectors,
    /// verifier flags, solver path, requested pool or execution grants exist.
    pub consumer: WorkloadInvocation,
    pub ay: AySubject,
}
fn path(value: &[u8]) -> bool {
    value.len() > 1
        && value.len() <= 4096
        && value[0] == b'/'
        && !value.contains(&0)
        && value[1..]
            .split(|b| *b == b'/')
            .all(|part| !part.is_empty() && part != b"." && part != b"..")
}
fn contains(root: &[u8], other: &[u8]) -> bool {
    other == root || (other.starts_with(root) && other.get(root.len()) == Some(&b'/'))
}
impl AySubject {
    pub fn validate(&self) -> io::Result<()> {
        if !path(&self.root) || self.source_commit == [0; 20] || self.crate_tree == [0; 20] {
            return Err(invalid());
        }
        for (input, suffix) in self.inputs() {
            let mut expected = self.root.clone();
            expected.extend_from_slice(suffix);
            if input.path != expected || input.sha256 == [0; 32] {
                return Err(invalid());
            }
        }
        Ok(())
    }
    fn inputs(&self) -> [(&InputFile, &'static [u8]); 5] {
        [
            (&self.workspace_manifest, b"/Cargo.toml"),
            (&self.crate_manifest, b"/crates/ay-proof-common/Cargo.toml"),
            (&self.lockfile, b"/Cargo.lock"),
            (&self.cargo_config, b"/.cargo/config.toml"),
            (&self.toolchain_config, b"/rust-toolchain.toml"),
        ]
    }
}
impl PairedInvocation {
    pub fn validate(&self) -> io::Result<()> {
        self.consumer.validate()?;
        self.ay.validate()?;
        if contains(&self.ay.root, &self.consumer.output_root)
            || contains(&self.consumer.output_root, &self.ay.root)
        {
            return Err(invalid());
        }
        budget::Budget::new(self.consumer.repetitions, self.consumer.timeout_ns)?;
        Ok(())
    }
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        self.validate()?;
        let mut e = Encoder::new(60);
        e.number(1);
        e.frame_bytes(&self.consumer.encode()?)?;
        e.bytes(&self.ay.root)?;
        for (input, _) in self.ay.inputs() {
            e.bytes(&input.path)?;
            e.0.extend(input.sha256);
        }
        e.0.extend(self.ay.source_commit);
        e.0.extend(self.ay.crate_tree);
        e.finish()
    }
    pub fn decode(bytes: &[u8]) -> io::Result<Self> {
        let mut d = header(bytes, 60)?;
        if d.number()? != 1 {
            return Err(invalid());
        }
        let consumer = WorkloadInvocation::decode(&d.frame_bytes()?)?;
        let root = d.bytes()?;
        let mut input =
            || -> io::Result<InputFile> { Ok(InputFile { path: d.bytes()?, sha256: d.array()? }) };
        let workspace_manifest = input()?;
        let crate_manifest = input()?;
        let lockfile = input()?;
        let cargo_config = input()?;
        let toolchain_config = input()?;
        let ay = AySubject {
            root,
            workspace_manifest,
            crate_manifest,
            lockfile,
            cargo_config,
            toolchain_config,
            source_commit: d.array()?,
            crate_tree: d.array()?,
        };
        d.done()?;
        let value = Self { consumer, ay };
        value.validate()?;
        Ok(value)
    }
    /// SHA256 of exactly this preimage is FULL60digest for Ready48/49v2, bank,
    /// phases, census, evidence and service frames. Minimal DTO builds retain
    /// no mandatory hash dependency and create no authenticated startup owner.
    pub fn binding_preimage(&self) -> io::Result<Vec<u8>> {
        let bytes = self.encode()?;
        let mut value = PAIRED_INVOCATION_HASH_DOMAIN.to_vec();
        value.extend_from_slice(&(bytes.len() as u64).to_be_bytes());
        value.extend_from_slice(&bytes);
        Ok(value)
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    pub(crate) fn invocation() -> PairedInvocation {
        fn file(path: &str) -> InputFile {
            InputFile { path: path.as_bytes().to_vec(), sha256: [2; 32] }
        }
        PairedInvocation {
            consumer: WorkloadInvocation {
                invocation: [1; 16],
                observed_host_store: None,
                root: b"/sdk".to_vec(),
                program: file("/sdk/bin/targo"),
                compiler: file("/sdk/bin/trustc"),
                cwd: b"/source".to_vec(),
                cargo_home: b"/cargo-home".to_vec(),
                output_root: b"/output".to_vec(),
                refutation_step: file("/fixtures/step.rs"),
                refutation_loop: file("/fixtures/loop.rs"),
                trust_spec_source: file("/fixtures/spec.rs"),
                repetitions: 3,
                timeout_ns: 3_600_000_000_000,
            },
            ay: AySubject {
                root: b"/source/first-party/ay".to_vec(),
                workspace_manifest: file("/source/first-party/ay/Cargo.toml"),
                crate_manifest: file("/source/first-party/ay/crates/ay-proof-common/Cargo.toml"),
                lockfile: file("/source/first-party/ay/Cargo.lock"),
                cargo_config: file("/source/first-party/ay/.cargo/config.toml"),
                toolchain_config: file("/source/first-party/ay/rust-toolchain.toml"),
                source_commit: [3; 20],
                crate_tree: [4; 20],
            },
        }
    }
    #[test]
    fn new_full_plan_roundtrips_and_never_routes_as_legacy_workload_or_member() {
        let value = invocation();
        let bytes = value.encode().unwrap();
        assert_eq!(PairedInvocation::decode(&bytes).unwrap(), value);
        assert!(WorkloadInvocation::decode(&bytes).is_err());
        assert!(PairedInvocation::decode(&value.consumer.encode().unwrap()).is_err());
        assert!(crate::Request::decode(&bytes).is_err());
        assert!(crate::SealedMetadataRequest::decode(&bytes).is_err());
        let mut trailing = bytes.clone();
        trailing.push(0);
        assert!(PairedInvocation::decode(&trailing).is_err());
        let mut future = bytes.clone();
        future[16..24].copy_from_slice(&2u64.to_be_bytes());
        assert!(PairedInvocation::decode(&future).is_err());
    }
    #[test]
    fn all_source_and_consumer_inputs_participate_in_the_full_domain_binding() {
        let base = invocation();
        let preimage = base.binding_preimage().unwrap();
        assert!(preimage.starts_with(PAIRED_INVOCATION_HASH_DOMAIN));
        assert!(preimage.ends_with(&base.encode().unwrap()));
        let offset = PAIRED_INVOCATION_HASH_DOMAIN.len();
        assert_eq!(
            u64::from_be_bytes(preimage[offset..offset + 8].try_into().unwrap()),
            base.encode().unwrap().len() as u64
        );
        for change in 0..9 {
            let mut value = base.clone();
            match change {
                0 => value.consumer.repetitions += 1,
                1 => value.consumer.compiler.sha256[0] ^= 1,
                2 => value.ay.source_commit[0] ^= 1,
                3 => value.ay.crate_tree[0] ^= 1,
                4 => value.ay.workspace_manifest.sha256[0] ^= 1,
                5 => value.ay.crate_manifest.sha256[0] ^= 1,
                6 => value.ay.lockfile.sha256[0] ^= 1,
                7 => value.ay.cargo_config.sha256[0] ^= 1,
                _ => value.ay.toolchain_config.sha256[0] ^= 1,
            }
            assert_ne!(value.binding_preimage().unwrap(), preimage);
        }
        assert_ne!(base.consumer.encode().unwrap(), preimage);
    }
    #[test]
    fn source_path_substitution_overlap_unknown_ids_and_overflow_refuse() {
        for change in 0..8 {
            let mut value = invocation();
            match change {
                0 => value.ay.root = b"/source/../ay".to_vec(),
                1 => {
                    value.ay.crate_manifest.path =
                        b"/source/first-party/ay/crates/other/Cargo.toml".to_vec()
                }
                2 => value.ay.lockfile.path = b"/foreign/Cargo.lock".to_vec(),
                3 => value.ay.source_commit = [0; 20],
                4 => value.ay.crate_tree = [0; 20],
                5 => value.ay.cargo_config.sha256 = [0; 32],
                6 => value.consumer.output_root = b"/source/first-party/ay/target".to_vec(),
                _ => value.consumer.timeout_ns = u64::MAX,
            }
            assert!(value.encode().is_err());
        }
        assert_ne!(PAIRED_PROTOCOL_MARKER, crate::workload::WORKLOAD_PROTOCOL_MARKER);
        assert_eq!(&PAIRED_PROTOCOL_MARKER[..16], b"TRUSTPAIRQUAL002");
    }
}
