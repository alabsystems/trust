// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

/// Maximum private frame, including command and complete environment.
pub const MAX_PAYLOAD: usize = 1024 * 1024;
/// Maximum lossless argument, environment entry or pathname.
pub const MAX_FIELD: usize = 65536;
/// Maximum arguments or environment entries.
pub const MAX_ITEMS: usize = 4096;
/// Compatibility bound; current v3 production accepts no lifetime fences.
pub const MAX_FENCES: usize = 127;
/// Default private helper entry for fixed-FD fixtures. Production formats its
/// held socket numbers with HelperFds::arguments; neither carries a grant.
pub const HELPER_ARGUMENTS: [&str; 4] = [
    "__resource-member-v3",
    "--protocol=3",
    "--control-fd=3",
    "--producer-fd=4",
];
/// The helper's private control endpoint; never inherited by the target.
pub const CONTROL_FD: u32 = 3;
/// The helper's producer-proof endpoint; never inherited by the target.
pub const PRODUCER_FD: u32 = 4;

/// Private original-root context. Intentionally has no diagnostic formatter.
#[derive(Clone, PartialEq, Eq)]
pub struct JobBinding {
    pub session: String,
    pub root_attempt: [u8; 16],
    pub capability: [u8; 32],
}

/// Command bytes are Unix OS bytes, never lossy UTF-8. Environment is a complete
/// snapshot; the helper must not merge in its own ambient environment.
#[derive(Clone, PartialEq, Eq)]
pub struct CommandSpec {
    pub program: Vec<u8>,
    pub arg0: Option<Vec<u8>>,
    pub args: Vec<Vec<u8>>,
    pub environment: Vec<(Vec<u8>, Vec<u8>)>,
    pub cwd: Vec<u8>,
}
impl CommandSpec {
    /// Capacity retained by this DATA snapshot, including unused collection
    /// capacity. This is memory accounting, never command or resource authority.
    pub fn retained_bytes(&self) -> Option<usize> {
        let mut bytes = std::mem::size_of::<Self>()
            .checked_add(self.program.capacity())?
            .checked_add(self.cwd.capacity())?
            .checked_add(
                self.args
                    .capacity()
                    .checked_mul(std::mem::size_of::<Vec<u8>>())?,
            )?
            .checked_add(
                self.environment
                    .capacity()
                    .checked_mul(std::mem::size_of::<(Vec<u8>, Vec<u8>)>())?,
            )?;
        if let Some(arg0) = &self.arg0 {
            bytes = bytes.checked_add(arg0.capacity())?;
        }
        for arg in &self.args {
            bytes = bytes.checked_add(arg.capacity())?;
        }
        for (name, value) in &self.environment {
            bytes = bytes
                .checked_add(name.capacity())?
                .checked_add(value.capacity())?;
        }
        Some(bytes)
    }
}

/// Helper source and future target descriptors inhabit different namespaces.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Descriptor {
    pub source: u32,
    pub target: u32,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GnuTransport {
    None,
    NumericPipe {
        read: Descriptor,
        write: Descriptor,
    },
    NamedFifo {
        locator: Vec<u8>,
        device: u64,
        inode: u64,
        read: Descriptor,
        write: Descriptor,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Delegations {
    pub cpu: Option<Descriptor>,
    pub gnu: GnuTransport,
    pub fences: Vec<Descriptor>,
}

/// Request-role discriminator. Role 3 belongs to the maintained sealed
/// metadata envelope; never reinterpret it as a linker continuation.
pub const MACHO_LINKER_REQUEST_ROLE: u64 = 4;

/// Syntax-only binding to an existing member's unit, not a quiescence proof,
/// recovery capability, or permission to acquire another CPU credit.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Loan {
    /// Existing compiler member, never the original root or new child attempt.
    pub parent_attempt: [u8; 16],
    /// One non-replayable loan identity; not a recovery or allocation capability.
    pub nonce: [u8; 16],
    /// Observation to match against the parent's actual held primary lease.
    pub cpu_slot: u32,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Role {
    MetadataVersion,
    Compile,
    /// Exact bounded paired-compiler sysroot or built-in target inventory query.
    MetadataProbe,
    /// Separately negotiated sealed native metadata member. The envelope is
    /// `SealedMetadataRequest`; neither this tag nor decoding grants admission.
    SealedMetadata,
    /// One charged CPU unit lent by an independently quiescent compiler member.
    /// Host authentication, durable custody and strict paired linker validation
    /// remain mandatory; these syntax fields grant no execution authority.
    MachOLinker(Loan),
    /// Closed compiler queries under a separately ready resolver root. The
    /// SealedResolverQueryRequest envelope is mandatory; data grants nothing.
    ResolverQuery,
    /// Closed queries under a separately authenticated cooperative workload
    /// owner. Only workload::host::CompilerQuery may carry this role.
    WorkloadQuery,
    /// A live registered UnitOutput under the original exclusive queue phase.
    /// Only workload::host::produced::ProducedRequest may carry this role.
    WorkloadProduced,
    /// Actual registered produced coordinator's single existing primary is
    /// lent before ARM, then returned only after native compiler retirement.
    /// The Host independently proves the parent, source/output and SDK owners.
    CoordinatorCompiler([u8; 16]),
}
impl Role {
    /// The original producer-proof proxy has a closed purpose set. New direct
    /// workload/metadata envelopes cannot enter it by encoding a raw Request.
    pub fn is_proxy_member(self) -> bool {
        matches!(
            self,
            Self::MetadataVersion
                | Self::Compile
                | Self::MetadataProbe
                | Self::MachOLinker(_)
                | Self::CoordinatorCompiler(_)
        )
    }
}

/// One attempt. Unknown delivery must never cause this request to be replayed.
/// Intentionally has no Debug implementation because it contains a capability.
#[derive(Clone, PartialEq, Eq)]
pub struct Request {
    pub binding: JobBinding,
    pub member_attempt: [u8; 16],
    pub role: Role,
    pub command: CommandSpec,
    pub delegations: Delegations,
    pub timeout_ns: Option<u64>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BirthKind {
    MacosWallMicroseconds,
    LinuxStartTicks,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Identity {
    pub pid: u32,
    pub birth: u64,
    pub birth_kind: BirthKind,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Started {
    pub identity: Identity,
    pub monotonic_ns: u64,
    pub unix_ns: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Outcome {
    Exit(i32),
    Signal(i32),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CompletionCause {
    Exited,
    Timeout,
    Cancelled,
    ResourceLimit,
    /// The host lost execution or custody integrity; diagnostics retain the fault.
    HostFault,
}

/// Finished is delivered only after authenticated scope retirement and resource
/// return. Runtime measures target execution, excluding retirement cleanup.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Status {
    Attached,
    Started(Started),
    Finished {
        outcome: Outcome,
        cause: CompletionCause,
        runtime_ns: u64,
    },
    Refused {
        reason: String,
    },
    Unknown {
        reason: String,
        started: Option<Started>,
    },
}

/// Frames bind every fact/cancellation to the same original and member attempt.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StatusFrame {
    pub root_attempt: [u8; 16],
    pub member_attempt: [u8; 16],
    pub status: Status,
}
