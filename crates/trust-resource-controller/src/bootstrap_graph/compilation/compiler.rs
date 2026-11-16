//! Private Bootstrap Fixed compiler/paired-linker binding DATA. No decoder
//! creates compiler, GNU, pause, primary loan, seed, execution or retirement.
use super::*;
use crate::context::{identity_decode, identity_encode};
use crate::{ContextQuery, Identity, MetadataFile};

#[cfg(all(feature = "channel", any(target_os = "macos", target_os = "linux")))]
pub mod transport;

pub const ADOPT_PURPOSE: &str = "native-bootstrap-fixed-compiler-v1";
pub const LINKER_PURPOSE: &str = "native-bootstrap-fixed-linker-v1";
pub const RETIRE_PURPOSE: &str = "native-bootstrap-fixed-linker-retire-v1";
pub const GNU_RIGHTS_MARKER: u8 = 0x76;

/// Support declaration only, separate from the standalone BootstrapFixed
/// execution profile. Actual native compiler adoption/NoFork/primary is still
/// mandatory; marker bytes never construct or renew those owners.
pub const BOOTSTRAP_FIXED_COMPILER_PROTOCOL_MARKER: [u8; 64] = compiler_marker();
/// Support DATA for the paired linker's actual producing-path option guard.
/// No declaration creates native NoFork, primary or retirement owners.
pub const BOOTSTRAP_FIXED_LINKER_PROTOCOL_MARKER: [u8; 64] = linker_marker();
const fn linker_marker() -> [u8; 64] {
    let mut bytes = [0; 64];
    let magic = *b"TRUSTBTFIXLLD001";
    let mut index = 0;
    while index < 16 {
        bytes[index] = magic[index];
        index += 1;
    }
    let fields = [1_u64, 1, 1, 1, 1, 0];
    let mut field = 0;
    while field < fields.len() {
        let value = fields[field].to_be_bytes();
        let mut byte = 0;
        while byte < 8 {
            bytes[16 + field * 8 + byte] = value[byte];
            byte += 1;
        }
        field += 1;
    }
    bytes
}
const fn compiler_marker() -> [u8; 64] {
    let mut bytes = [0; 64];
    let magic = *b"TRUSTBTFIXCOMP01";
    let mut index = 0;
    while index < 16 {
        bytes[index] = magic[index];
        index += 1;
    }
    let fields = [1_u64, 1, 118, 2, 1, 0];
    let mut field = 0;
    while field < fields.len() {
        let value = fields[field].to_be_bytes();
        let mut byte = 0;
        while byte < 8 {
            bytes[16 + field * 8 + byte] = value[byte];
            byte += 1;
        }
        field += 1;
    }
    bytes
}

#[derive(Clone, PartialEq, Eq)]
pub struct AdoptRequest {
    pub query: ContextQuery,
    pub compiler: Identity,
    pub gnu: GnuIdentity,
}
impl AdoptRequest {
    pub fn validate(&self) -> io::Result<()> {
        self.query.validate()?;
        identity_encode(&mut Encoder::new(0), self.compiler)?;
        self.gnu.write(&mut Encoder::new(0))
    }
    pub fn hello(&self) -> io::Result<Vec<u8>> {
        self.validate()?;
        super::super::purpose_hello(&self.query, ADOPT_PURPOSE)
    }
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        self.validate()?;
        let mut e = Encoder::new(180);
        e.number(1);
        e.frame_bytes(&self.query.encode()?)?;
        identity_encode(&mut e, self.compiler)?;
        self.gnu.write(&mut e)?;
        e.finish()
    }
    pub fn decode(bytes: &[u8]) -> io::Result<Self> {
        let mut d = header(bytes, 180)?;
        if d.number()? != 1 {
            return Err(invalid());
        }
        let value = Self {
            query: ContextQuery::decode(&d.frame_bytes()?)?,
            compiler: identity_decode(&mut d)?,
            gnu: GnuIdentity::read(&mut d)?,
        };
        d.done()?;
        value.validate()?;
        Ok(value)
    }
}

/// Descriptions from the SAME actual held compiler runtime and paired LLD.
/// These bytes create neither a public SDK nor a private seed/runtime owner.
#[derive(Clone, PartialEq, Eq)]
pub struct CompilerInputs {
    pub root: Vec<u8>,
    pub compiler: MetadataFile,
    pub paired_linker: MetadataFile,
}
impl CompilerInputs {
    fn validate(&self) -> io::Result<()> {
        if !super::super::absolute(&self.root) {
            return Err(invalid());
        }
        self.compiler.validate(&self.root)?;
        self.paired_linker.validate(&self.root)?;
        if self.compiler.sha256 == [0; 32]
            || self.paired_linker.sha256 == [0; 32]
            || self.paired_linker.path != [self.root.as_slice(), b"/bin/rust-lld"].concat()
            || (self.compiler.device, self.compiler.inode)
                == (self.paired_linker.device, self.paired_linker.inode)
        {
            return Err(invalid());
        }
        Ok(())
    }
    fn write(&self, e: &mut Encoder) -> io::Result<()> {
        self.validate()?;
        e.bytes(&self.root)?;
        self.compiler.encode(e)?;
        self.paired_linker.encode(e)
    }
    fn read(d: &mut Decoder<'_>) -> io::Result<Self> {
        let value = Self {
            root: d.bytes()?,
            compiler: MetadataFile::decode(d)?,
            paired_linker: MetadataFile::decode(d)?,
        };
        value.validate()?;
        Ok(value)
    }
}
#[derive(Clone, PartialEq, Eq)]
pub struct Adopted {
    pub request: AdoptRequest,
    /// The Host's SAME actual registered Full compiler, not a child selector.
    pub member: RetireRequest,
    pub adoption: [u8; 16],
    pub inputs: CompilerInputs,
    /// Fresh remaining ORIGINAL Root bound, sampled just before native reply.
    /// Anchor once at RPC start; reobservations only restrict an existing bound.
    pub remaining_ns: u64,
}
impl Adopted {
    pub fn validate(&self) -> io::Result<()> {
        self.request.validate()?;
        self.member.validate()?;
        self.inputs.validate()?;
        let graph = &self.member.key.attempt.key.graph;
        if self.request.query.binding != graph.query.binding
            || !(1..=MAX_MEMBER_NS).contains(&self.remaining_ns)
            || [
                [0; 16],
                self.member.member,
                self.member.key.compilation,
                self.member.key.attempt.key.operation,
                graph.graph,
                graph.query.call_attempt,
                graph.query.binding.root_attempt,
                self.request.query.call_attempt,
            ]
            .contains(&self.adoption)
        {
            return Err(invalid());
        }
        Ok(())
    }
    /// Stable binding comparison DATA only. A decreasing time observation is
    /// deliberately excluded; it cannot renew the privately retained endpoint.
    pub fn same_owner(&self, other: &Self) -> bool {
        self.request == other.request
            && self.member == other.member
            && self.adoption == other.adoption
            && self.inputs == other.inputs
    }
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        self.validate()?;
        let mut e = Encoder::new(181);
        e.number(2);
        e.frame_bytes(&self.request.encode()?)?;
        e.frame_bytes(&self.member.encode()?)?;
        e.0.extend(self.adoption);
        self.inputs.write(&mut e)?;
        e.number(self.remaining_ns);
        e.finish()
    }
    pub fn decode(bytes: &[u8]) -> io::Result<Self> {
        let mut d = header(bytes, 181)?;
        if d.number()? != 2 {
            return Err(invalid());
        }
        let value = Self {
            request: AdoptRequest::decode(&d.frame_bytes()?)?,
            member: RetireRequest::decode(&d.frame_bytes()?)?,
            adoption: d.array()?,
            inputs: CompilerInputs::read(&mut d)?,
            remaining_ns: d.number()?,
        };
        d.done()?;
        value.validate()?;
        Ok(value)
    }
}

#[derive(Clone, PartialEq, Eq)]
pub struct PairedLinkerRequest {
    pub adopted: Adopted,
    pub generation: u64,
    pub member: [u8; 16],
    pub command: CommandSpec,
    pub timeout_ns: u64,
}
impl PairedLinkerRequest {
    pub fn validate(&self) -> io::Result<()> {
        self.retirement().validate()?;
        crate::linker::validate_arguments(&self.command.args)?;
        if !(1..=MAX_MEMBER_NS).contains(&self.timeout_ns) {
            return Err(invalid());
        }
        command_write(&self.command, &mut Encoder::new(0))
    }
    pub fn hello(&self) -> io::Result<Vec<u8>> {
        self.validate()?;
        super::super::purpose_hello(&self.adopted.request.query, LINKER_PURPOSE)
    }
    pub fn retirement(&self) -> LinkerRetire {
        LinkerRetire {
            adopted: self.adopted.clone(),
            generation: self.generation,
            member: self.member,
        }
    }
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        self.validate()?;
        let mut e = Encoder::new(182);
        e.number(1);
        e.frame_bytes(&self.retirement().encode()?)?;
        command_write(&self.command, &mut e)?;
        e.number(self.timeout_ns);
        e.finish()
    }
    pub fn decode(bytes: &[u8]) -> io::Result<Self> {
        let mut d = header(bytes, 182)?;
        if d.number()? != 1 {
            return Err(invalid());
        }
        let retired = LinkerRetire::decode(&d.frame_bytes()?)?;
        let value = Self {
            adopted: retired.adopted,
            generation: retired.generation,
            member: retired.member,
            command: command_read(&mut d)?,
            timeout_ns: d.number()?,
        };
        d.done()?;
        value.validate()?;
        Ok(value)
    }
}

#[derive(Clone, PartialEq, Eq)]
pub struct LinkerRetire {
    pub adopted: Adopted,
    pub generation: u64,
    pub member: [u8; 16],
}
impl LinkerRetire {
    pub fn validate(&self) -> io::Result<()> {
        self.adopted.validate()?;
        let compiler = &self.adopted.member;
        let graph = &compiler.key.attempt.key.graph;
        if !(1..=MAX_MEMBERS).contains(&self.generation)
            || [
                [0; 16],
                self.adopted.adoption,
                compiler.member,
                compiler.key.compilation,
                compiler.key.attempt.key.operation,
                graph.graph,
                graph.query.call_attempt,
                graph.query.binding.root_attempt,
                self.adopted.request.query.call_attempt,
            ]
            .contains(&self.member)
        {
            return Err(invalid());
        }
        Ok(())
    }
    pub fn same_loan(&self, other: &Self) -> bool {
        self.adopted.same_owner(&other.adopted)
            && self.generation == other.generation
            && self.member == other.member
    }
    pub fn hello(&self) -> io::Result<Vec<u8>> {
        self.validate()?;
        super::super::purpose_hello(&self.adopted.request.query, RETIRE_PURPOSE)
    }
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        self.validate()?;
        let mut e = Encoder::new(183);
        e.number(1);
        e.frame_bytes(&self.adopted.encode()?)?;
        e.number(self.generation);
        e.0.extend(self.member);
        e.finish()
    }
    pub fn decode(bytes: &[u8]) -> io::Result<Self> {
        let mut d = header(bytes, 183)?;
        if d.number()? != 1 {
            return Err(invalid());
        }
        let value = Self {
            adopted: Adopted::decode(&d.frame_bytes()?)?,
            generation: d.number()?,
            member: d.array()?,
        };
        d.done()?;
        value.validate()?;
        Ok(value)
    }
}

/// Target outcome is distinct from native owning closure. In particular,
/// Exit(0) with HostFault is failed work and never a successful paired link.
#[derive(Clone, PartialEq, Eq)]
pub struct LinkerRetired {
    pub request: LinkerRetire,
    pub status: Status,
}
impl LinkerRetired {
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        self.request.validate()?;
        if !matches!(self.status, Status::Finished { .. } | Status::Refused { .. }) {
            return Err(invalid());
        }
        let status = StatusFrame {
            root_attempt: self.request.adopted.request.query.binding.root_attempt,
            member_attempt: self.request.member,
            status: self.status.clone(),
        };
        let mut e = Encoder::new(184);
        e.number(1);
        e.frame_bytes(&self.request.encode()?)?;
        e.frame_bytes(&status.encode()?)?;
        e.finish()
    }
    pub fn decode(bytes: &[u8]) -> io::Result<Self> {
        let mut d = header(bytes, 184)?;
        if d.number()? != 1 {
            return Err(invalid());
        }
        let request = LinkerRetire::decode(&d.frame_bytes()?)?;
        let status = StatusFrame::decode(
            &d.frame_bytes()?,
            request.adopted.request.query.binding.root_attempt,
            request.member,
        )?
        .status;
        d.done()?;
        let value = Self { request, status };
        value.encode()?;
        Ok(value)
    }
}
#[cfg(test)]
pub(crate) mod tests;
