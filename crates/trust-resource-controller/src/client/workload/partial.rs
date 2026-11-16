// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Original-channel partial phase custody. No decoded frame constructs funding.
use super::*;
use crate::workload::host::partial as wire;

/// The SAME actual retained bank services crossed requests. This is not an
/// observer/grant fallback: a positive answer still transfers its real FD and
/// Host independently checks the original held unit before any target GO.
pub trait PartialBank {
    /// Reserve the actual incoming three-FD envelope in the SAME original
    /// process descriptor budget before recvmsg creates any originals.
    fn reserve_pending_keeper(&mut self) -> io::Result<crate::descriptors::OriginalInputPermit> {
        Err(io::ErrorKind::Unsupported.into())
    }
    /// Store the actual non-executable originals in the SAME original worker
    /// owner until positive quiescence/closure. This supplies no new funding.
    fn retain_pending_keeper(
        &mut self,
        _owner: std::sync::Arc<super::AuthenticatedPendingKeeper>,
    ) -> io::Result<()> {
        Err(io::Error::new(
            io::ErrorKind::Unsupported,
            "original pending keeper storage unavailable",
        ))
    }
    fn service(
        &mut self,
        request: &host::bank::Request,
        reply: &mut PartialBankReply<'_>,
    ) -> io::Result<()>;
}
pub struct PartialBankReply<'a> {
    control: &'a mut WorkloadControl,
    deadline: Instant,
    replied: bool,
}
impl PartialBankReply<'_> {
    pub fn send(
        &mut self,
        reply: &host::bank::Reply,
        original: Option<std::os::fd::BorrowedFd<'_>>,
    ) -> io::Result<()> {
        if self.replied {
            self.control.failed = true;
            return Err(refused());
        }
        self.control.reply_bank(reply, original, self.deadline)?;
        self.replied = true;
        Ok(())
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Stage {
    Prepared,
    Releasing,
    Released,
    Funded,
}
#[derive(Clone, Copy)]
enum Preparation {
    Runtime,
    Initial,
}
pub(super) struct State {
    phase: [u8; 16],
    ordinal: u64,
    implicit: wire::CpuUnit,
    stage: Stage,
    funded: Vec<wire::CpuUnit>,
}

impl WorkloadControl {
    pub(super) fn keeper_phase_matches(&self, phase: [u8; 16]) -> bool {
        self.partial
            .as_ref()
            .is_some_and(|state| state.phase == phase && state.stage == Stage::Released)
            || matches!(self.initial, Some(initial::GnuStage::Awaiting(original)) if original == phase)
    }
    pub(super) fn current_share_ready(&self) -> bool {
        !matches!(self.initial, Some(initial::GnuStage::Awaiting(_)))
            && match &self.partial {
                Some(state) => state.stage == Stage::Released && !state.funded.is_empty(),
                None => matches!(self.initial, Some(initial::GnuStage::Armed)),
            }
    }
}

/// Authenticated original Host preparation. It grants no CPU; it binds only
/// the exclusion/release continuation to the SAME root, GNU and implicit unit.
pub struct PreparedPartialPhase {
    root_attempt: [u8; 16],
    invocation_sha256: [u8; 32],
    phase: [u8; 16],
    ordinal: u64,
    gnu: FileIdentity,
    implicit: wire::CpuUnit,
    _host: std::sync::Arc<trust_resource_provenance::PinnedHelper>,
}
impl PreparedPartialPhase {
    pub fn binding(&self) -> ([u8; 16], [u8; 32], [u8; 16], u64) {
        (self.root_attempt, self.invocation_sha256, self.phase, self.ordinal)
    }
    pub fn gnu(&self) -> FileIdentity {
        self.gnu
    }
    pub fn implicit(&self) -> wire::CpuUnit {
        self.implicit
    }
}
/// Positive completion on the SAME original control after actual FD install.
/// No decoded Committed frame can construct this continuation.
pub struct CommittedPartialPhase {
    root_attempt: [u8; 16],
    invocation_sha256: [u8; 32],
    phase: [u8; 16],
    ordinal: u64,
    host: std::sync::Arc<trust_resource_provenance::PinnedHelper>,
    funded: usize,
}
impl CommittedPartialPhase {
    pub fn funded_width(&self) -> usize {
        self.funded
    }
    pub fn matches_original(&self, original: &PreparedPartialPhase) -> bool {
        self.root_attempt == original.root_attempt
            && self.invocation_sha256 == original.invocation_sha256
            && self.phase == original.phase
            && self.ordinal == original.ordinal
            && std::sync::Arc::ptr_eq(&self.host, &original._host)
    }
}

/// Actual replacement unit descriptions received from the SAME pinned Host
/// over the original root channel. Non-Clone, no constructor from wire DATA.
pub struct AuthenticatedPartialFunding {
    original_cpu: crate::Cpu,
    root_attempt: [u8; 16],
    invocation_sha256: [u8; 32],
    phase: [u8; 16],
    ordinal: u64,
    funded_before: usize,
    supplementary: Vec<wire::CpuUnit>,
    originals: Vec<OwnedFd>,
    _host: std::sync::Arc<trust_resource_provenance::PinnedHelper>,
}
impl AuthenticatedPartialFunding {
    pub fn original_cpu(&self) -> crate::Cpu {
        self.original_cpu
    }
    pub fn root_attempt(&self) -> [u8; 16] {
        self.root_attempt
    }
    pub fn invocation_sha256(&self) -> [u8; 32] {
        self.invocation_sha256
    }
    pub fn phase(&self) -> [u8; 16] {
        self.phase
    }
    pub fn ordinal(&self) -> u64 {
        self.ordinal
    }
    pub fn funded_before(&self) -> usize {
        self.funded_before
    }
    /// Consume actual received descriptions, not reconstructed paths or ACKs.
    pub fn into_originals(self) -> (Vec<wire::CpuUnit>, Vec<File>) {
        (self.supplementary, self.originals.into_iter().map(File::from).collect())
    }
}

impl WorkloadControl {
    fn partial_call(
        &mut self,
        phase: [u8; 16],
        operation: wire::Operation,
        gnu: Option<[std::os::fd::BorrowedFd<'_>; 2]>,
        bank: &mut dyn PartialBank,
        deadline: Instant,
    ) -> io::Result<wire::Reply> {
        if self.failed || self.drained || self.pending.is_some() || self.active_phase.is_some() {
            return Err(refused());
        }
        let result = (|| {
            let request = wire::Request {
                key: host::bank::Key {
                    root_attempt: self.root_attempt,
                    invocation_sha256: self.invocation_sha256,
                    sequence: self.last_phase_sequence.checked_add(1).ok_or_else(refused)?,
                },
                phase,
                operation,
            };
            let bytes = request.encode()?;
            self.host.validate(deadline)?;
            self.channel.send(&bytes, deadline)?;
            if let Some(fds) = gnu {
                // SAFETY: duplicates this still-held native control descriptor
                // close-on-exec; it does not alter the original OFD flags.
                let raw = unsafe {
                    libc::fcntl(self.channel.as_fd().as_raw_fd(), libc::F_DUPFD_CLOEXEC, 5)
                };
                if raw < 0 {
                    return Err(io::Error::last_os_error());
                }
                // SAFETY: fresh close-only duplicate of the original channel;
                // descriptor transfer creates no second control reader.
                let stream =
                    std::os::unix::net::UnixStream::from(unsafe { OwnedFd::from_raw_fd(raw) });
                jobserver_utils::descriptor_transfer::send(
                    &stream,
                    &fds,
                    host::phase::GNU_MARKER,
                    deadline,
                )?;
            }
            let reply = loop {
                let frame = self.channel.receive(deadline)?;
                if let Ok(request) = host::keeper::Request::decode(&frame) {
                    self.receive_pending_keeper(request, bank, deadline)?;
                    continue;
                }
                match wire::Reply::decode(&frame, &request) {
                    Ok(reply) => break reply,
                    Err(error) => {
                        let crossed = match host::bank::Request::decode(&frame) {
                            Ok(crossed) => crossed,
                            Err(_) => return Err(error),
                        };
                        self.accept_bank_request(&crossed)?;
                        let mut sink = PartialBankReply { control: self, deadline, replied: false };
                        bank.service(&crossed, &mut sink)?;
                        if !sink.replied {
                            return Err(refused());
                        }
                    }
                }
            };
            self.host.validate(deadline)?;
            self.last_phase_sequence = request.key.sequence;
            Ok(reply)
        })();
        if result.is_err() {
            self.failed = true;
        }
        result
    }

    /// Preparation returns no capacity. The caller still retains every native
    /// original and actual GNU escrow until the distinct release transition.
    pub fn prepare_partial_phase(
        &mut self,
        phase: [u8; 16],
        implicit: wire::CpuUnit,
        gnu: [std::os::fd::BorrowedFd<'_>; 2],
        bank: &mut dyn PartialBank,
        deadline: Instant,
    ) -> io::Result<Option<PreparedPartialPhase>> {
        if matches!(self.initial, Some(initial::GnuStage::Awaiting(_))) {
            return Err(refused());
        }
        self.prepare_owned_phase(phase, implicit, gnu, bank, deadline, Preparation::Runtime)
    }

    /// Only the distinct authenticated startup can supply this original phase.
    /// The caller must retain captive GNU through Busy/unknown; no token is
    /// backed by the declared ceiling alone.
    pub fn prepare_initial_phase(
        &mut self,
        implicit: wire::CpuUnit,
        gnu: [std::os::fd::BorrowedFd<'_>; 2],
        bank: &mut dyn PartialBank,
        deadline: Instant,
    ) -> io::Result<Option<PreparedPartialPhase>> {
        let Some(initial::GnuStage::Awaiting(phase)) = self.initial else { return Err(refused()) };
        self.prepare_owned_phase(phase, implicit, gnu, bank, deadline, Preparation::Initial)
    }

    fn prepare_owned_phase(
        &mut self,
        phase: [u8; 16],
        implicit: wire::CpuUnit,
        gnu: [std::os::fd::BorrowedFd<'_>; 2],
        bank: &mut dyn PartialBank,
        deadline: Instant,
        preparation: Preparation,
    ) -> io::Result<Option<PreparedPartialPhase>> {
        if self.failed || self.drained || self.pending.is_some() || self.active_phase.is_some() {
            return Err(refused());
        }
        if self.partial_unsupported && matches!(preparation, Preparation::Runtime) {
            return Ok(None);
        }
        if self.partial.is_some()
            || self.output_locks.is_none()
            || !matches!(self.original_cpu, crate::Cpu::CooperativeShared { ceiling, .. }
                if ceiling >= match preparation { Preparation::Runtime => 2, Preparation::Initial => 1 })
        {
            return Err(refused());
        }
        let backing = fifo_identity(gnu[0], libc::O_RDONLY)?;
        if fifo_identity(gnu[1], libc::O_WRONLY)? != backing {
            return Err(refused());
        }
        match self
            .partial_call(
                phase,
                match preparation {
                    Preparation::Runtime => wire::Operation::Prepare { gnu: backing, implicit },
                    Preparation::Initial => {
                        wire::Operation::PrepareInitial { gnu: backing, implicit }
                    }
                },
                Some(gnu),
                bank,
                deadline,
            )?
            .decision
        {
            wire::Decision::Prepared => {
                if matches!(preparation, Preparation::Initial) {
                    self.initial = Some(initial::GnuStage::Armed);
                }
                let ordinal = self.last_phase_sequence;
                self.partial = Some(State {
                    phase,
                    ordinal,
                    implicit,
                    stage: Stage::Prepared,
                    funded: vec![implicit],
                });
                Ok(Some(PreparedPartialPhase {
                    root_attempt: self.root_attempt,
                    invocation_sha256: self.invocation_sha256,
                    phase,
                    ordinal,
                    gnu: backing,
                    implicit,
                    _host: std::sync::Arc::clone(&self.host),
                }))
            }
            wire::Decision::Busy => Ok(None),
            wire::Decision::Unsupported if matches!(preparation, Preparation::Runtime) => {
                self.partial_unsupported = true;
                Ok(None)
            }
            _ => {
                self.failed = true;
                Err(refused())
            }
        }
    }

    /// # Safety
    /// The original SDK/bank owner must have parked new primary/extra dispatch,
    /// retained SAME supplementary GNU escrow, joined/excluded every extra and
    /// CLOSED every supplementary native description before the FIRST call.
    /// That exclusion must persist across failure and Host/worker loss. Neither
    /// a decoded Prepared nor an empty loan table proves this obligation.
    pub unsafe fn release_after_sdk_park(
        &mut self,
        phase: [u8; 16],
        bank: &mut dyn PartialBank,
        deadline: Instant,
    ) -> io::Result<bool> {
        let state = self.partial.as_mut().ok_or_else(refused)?;
        if state.phase != phase
            || !matches!(state.stage, Stage::Prepared | Stage::Releasing | Stage::Released)
        {
            return Err(refused());
        }
        state.stage = Stage::Releasing;
        match self.partial_call(phase, wire::Operation::Release, None, bank, deadline)?.decision {
            wire::Decision::Released => {
                let state = self.partial.as_mut().ok_or_else(refused)?;
                state.stage = Stage::Released;
                state.funded.truncate(1);
                Ok(true)
            }
            wire::Decision::Busy => Ok(false),
            _ => {
                self.failed = true;
                Err(refused())
            }
        }
    }

    /// A fair Host decision must return ACTUAL unit FDs. Metadata alone never
    /// creates this opaque funding value or restores a GNU token.
    pub fn restore_partial_phase(
        &mut self,
        phase: [u8; 16],
        bank: &mut dyn PartialBank,
        deadline: Instant,
    ) -> io::Result<Option<AuthenticatedPartialFunding>> {
        let state = self.partial.as_ref().ok_or_else(refused)?;
        if state.phase != phase || state.stage != Stage::Released {
            return Err(refused());
        }
        let implicit = state.implicit;
        let funded_before = state.funded.len();
        let ordinal = state.ordinal;
        let crate::Cpu::CooperativeShared { ceiling, .. } = self.original_cpu else {
            return Err(refused());
        };
        let reply = self.partial_call(phase, wire::Operation::Restore, None, bank, deadline)?;
        let result = (|| match reply.decision {
            wire::Decision::Busy => Ok(None),
            wire::Decision::Funded { supplementary } => {
                if supplementary.len()
                    > (ceiling as usize).checked_sub(funded_before).ok_or_else(refused)?
                    || supplementary.iter().any(|cpu| {
                        cpu.slot == implicit.slot
                            || cpu.backing == implicit.backing
                            || self.partial.as_ref().is_none_or(|state| {
                                state
                                    .funded
                                    .iter()
                                    .any(|old| old.slot == cpu.slot || old.backing == cpu.backing)
                            })
                    })
                {
                    return Err(refused());
                }
                self.partial
                    .as_mut()
                    .ok_or_else(refused)?
                    .funded
                    .try_reserve_exact(supplementary.len())
                    .map_err(io::Error::other)?;
                let originals =
                    receive_marked(&self.channel, supplementary.len(), wire::CPU_MARKER, deadline)?;
                for (fd, expected) in originals.iter().zip(&supplementary) {
                    if identity(fd.as_raw_fd())? != expected.backing {
                        return Err(refused());
                    }
                }
                self.host.validate(deadline)?;
                let state = self.partial.as_mut().ok_or_else(refused)?;
                state.funded.extend_from_slice(&supplementary);
                state.stage = Stage::Funded;
                Ok(Some(AuthenticatedPartialFunding {
                    original_cpu: self.original_cpu,
                    root_attempt: self.root_attempt,
                    invocation_sha256: self.invocation_sha256,
                    phase,
                    ordinal,
                    funded_before,
                    supplementary,
                    originals,
                    _host: std::sync::Arc::clone(&self.host),
                }))
            }
            _ => Err(refused()),
        })();
        if result.is_err() {
            self.failed = true;
        }
        result
    }

    /// # Safety
    /// The original bank must already own and validate ALL actual received
    /// replacements under this SAME phase, retain implicit backing and GNU
    /// escrow, and preserve its original policy/stop. A reply/count alone is
    /// insufficient. Unknown must not resume or return escrowed GNU tokens.
    pub unsafe fn commit_after_funding_install(
        &mut self,
        phase: [u8; 16],
        bank: &mut dyn PartialBank,
        deadline: Instant,
    ) -> io::Result<CommittedPartialPhase> {
        let initial_single = matches!(self.initial, Some(initial::GnuStage::Armed))
            && matches!(self.original_cpu, crate::Cpu::CooperativeShared { ceiling: 1, .. });
        if self.partial.as_ref().is_none_or(|state| {
            state.phase != phase
                || !(state.stage == Stage::Funded
                    || (initial_single
                        && state.stage == Stage::Released
                        && state.funded.len() == 1))
        }) {
            return Err(refused());
        }
        match self.partial_call(phase, wire::Operation::Commit, None, bank, deadline)?.decision {
            wire::Decision::Committed => {
                let state = self.partial.as_mut().ok_or_else(refused)?;
                let funded = state.funded.len();
                let ordinal = state.ordinal;
                let crate::Cpu::CooperativeShared { ceiling, .. } = self.original_cpu else {
                    return Err(refused());
                };
                state.stage = Stage::Released;
                if funded == ceiling as usize {
                    self.partial.take();
                }
                Ok(CommittedPartialPhase {
                    root_attempt: self.root_attempt,
                    invocation_sha256: self.invocation_sha256,
                    phase,
                    ordinal,
                    host: std::sync::Arc::clone(&self.host),
                    funded,
                })
            }
            _ => {
                self.failed = true;
                Err(refused())
            }
        }
    }
}
