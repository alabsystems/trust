// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Parent observation of SAME native preparation originals. No grant/retirement.
use super::*;
use crate::workload::host::coordinator as wire;
use std::os::unix::ffi::OsStrExt as _;

pub(super) struct OriginalCompilerTransport {
    files: Vec<OwnedFd>,
    reply: wire::TransportReply,
    control: Option<trust_resource_provenance::PinnedHelper>,
    _descriptors: crate::descriptors::OriginalInputPermit,
}
fn backing(fd: BorrowedFd<'_>) -> io::Result<crate::FileIdentity> {
    // SAFETY: one held FD and initialized native stat output; no descriptor allocation.
    let mut stat: libc::stat = unsafe { std::mem::zeroed() };
    // SAFETY: this descriptor remains borrowed and the native output is writable.
    if unsafe { libc::fstat(fd.as_raw_fd(), &mut stat) } != 0 {
        return Err(io::Error::last_os_error());
    }
    Ok(crate::FileIdentity {
        device: stat.st_dev as u64,
        inode: stat.st_ino as u64,
    })
}
fn source(child: &ProxyChild, number: u32) -> io::Result<BorrowedFd<'_>> {
    child
        .descriptions
        .iter()
        .find(|fd| fd.as_raw_fd() as u32 == number)
        .map(AsFd::as_fd)
        .ok_or_else(invalid)
}
impl OriginalCompilerTransport {
    fn import_control(
        &mut self,
        expected: &trust_resource_provenance::PinnedHelper,
        deadline: Instant,
    ) -> io::Result<()> {
        if self.control.is_some() || self.files.len() != wire::TRANSPORT_ORIGINALS {
            return Err(invalid());
        }
        let copies = self.files[5..]
            .iter()
            .map(OwnedFd::try_clone)
            .collect::<io::Result<Vec<_>>>()?
            .try_into()
            .map_err(|_| invalid())?;
        self.control = Some(expected.receive_original_control(copies, deadline)?);
        Ok(())
    }
    pub(super) fn retained_bytes(&self) -> Option<usize> {
        let context = &self.reply.context.context;
        let mut bytes = std::mem::size_of::<Self>()
            .checked_add(
                self.files
                    .capacity()
                    .checked_mul(std::mem::size_of::<OwnedFd>())?,
            )?
            .checked_add(self.reply.advertisement.capacity())?;
        for capacity in [
            context.session.capacity(),
            context.host.capacity(),
            context.boot.capacity(),
            context.memory.marker.capacity(),
        ] {
            bytes = bytes.checked_add(capacity)?;
        }
        if let Some(sdk) = &context.sdk {
            bytes = bytes
                .checked_add(sdk.execution.capacity())?
                .checked_add(sdk.lease_path.capacity())?;
        }
        if let Some(control) = &self.control {
            bytes = bytes.checked_add(control.retained_control_bytes()?)?;
        }
        Some(bytes)
    }
    fn validate(
        &self,
        child: &ProxyChild,
        compiler: &trust_resource_provenance::program::HeldProgram,
        deadline: Instant,
    ) -> io::Result<()> {
        let request = child.compiler_request.as_ref().ok_or_else(invalid)?;
        let cpu = request.delegations.cpu.ok_or_else(invalid)?;
        let crate::GnuTransport::NumericPipe { read, write } = request.delegations.gnu else {
            return Err(invalid());
        };
        if cpu.target != 6
            || read.target != 8
            || write.target != 9
            || self.files.len() != wire::TRANSPORT_ORIGINALS
            || self.reply.target
                != child
                    .compiler_prepared
                    .as_ref()
                    .ok_or_else(invalid)?
                    .identity
        {
            return Err(invalid());
        }
        super::super::workload::live_context(&self.reply.context.context, None)?;
        super::super::sdk::validate_sdk_keeper(&self.reply.context.context)?;
        let sdk = self
            .reply
            .context
            .context
            .sdk
            .as_ref()
            .ok_or_else(invalid)?;
        if sdk.execution != compiler.root().as_os_str().as_bytes()
            || sdk.lease != self.reply.backings[3]
        {
            return Err(invalid());
        }
        let store = child.host.duplicate_original_store(deadline)?;
        if backing(store.as_fd())? != self.reply.backings[4] {
            return Err(invalid());
        }
        for (index, number) in [cpu.source, read.source, write.source]
            .into_iter()
            .enumerate()
        {
            if backing(source(child, number)?)? != self.reply.backings[index] {
                return Err(invalid());
            }
        }
        // SAFETY: geteuid only observes the current process credential.
        let uid = unsafe { libc::geteuid() };
        for (index, file) in self.files.iter().enumerate() {
            if backing(file.as_fd())? != self.reply.backings[index] {
                return Err(invalid());
            }
            // Validate actual received rights/kinds, never an advertised count.
            // SAFETY: observe access flags on this actual held received FD.
            let flags = unsafe { libc::fcntl(file.as_raw_fd(), libc::F_GETFL) };
            // SAFETY: initialized stat storage for the following read-only syscall.
            let mut stat: libc::stat = unsafe { std::mem::zeroed() };
            if flags < 0 {
                return Err(io::Error::last_os_error());
            }
            // SAFETY: the owned received FD is live and stat is writable output.
            if unsafe { libc::fstat(file.as_raw_fd(), &mut stat) } != 0 {
                return Err(io::Error::last_os_error());
            }
            let kind = stat.st_mode & libc::S_IFMT;
            if match index {
                1 => kind != libc::S_IFIFO || flags & libc::O_ACCMODE != libc::O_RDONLY,
                2 => kind != libc::S_IFIFO || flags & libc::O_ACCMODE != libc::O_WRONLY,
                4..=7 | 11..=12 => {
                    kind != libc::S_IFDIR || flags & libc::O_ACCMODE != libc::O_RDONLY
                }
                13 => kind != libc::S_IFSOCK,
                _ => {
                    kind != libc::S_IFREG
                        || stat.st_uid != uid
                        || stat.st_mode & 0o077 != 0
                        || stat.st_nlink != 1
                }
            } {
                return Err(invalid());
            }
        }
        let control = self.control.as_ref().ok_or_else(invalid)?;
        control.validate(deadline)?;
        if control.host_pid() != child.host.host_pid()
            || control.host_birth() != child.host.host_birth()
            || control.helper_path() != child.host.helper_path()
            || control.socket_path() != child.host.socket_path()
            || !control.same_original_store_directory(self.files[4].as_fd())?
        {
            return Err(invalid());
        }
        child.host.validate(deadline)?;
        compiler.validate(deadline)
    }
}
impl ProxyChild {
    /// Reconstruct the entire producing command from SAME actual originals.
    /// This never creates a CPU/SDK/scope/producer/proof or completion grant.
    pub fn bind_compiler_producing(
        &mut self,
        query: &crate::ContextQuery,
        compiler: &trust_resource_provenance::program::HeldProgram,
        budget: &std::sync::Arc<crate::descriptors::DescriptorBudget>,
        deadline: Instant,
    ) -> io::Result<()> {
        let run = (|| {
            if !self.compiler_original_store
                || !self.accounted
                || !self.attached
                || !self.proof_done
                || self.compiler_binding_attempted
                || self.compiler_transport.is_some()
                || self.terminal.is_some()
            {
                return Err(invalid());
            }
            self.compiler_scope
                .as_ref()
                .ok_or_else(invalid)?
                .validate(deadline)?;
            let request = self.compiler_request.as_ref().ok_or_else(invalid)?;
            request.validate()?;
            if query.binding != request.binding
                || compiler.program().as_os_str().as_bytes() != request.command.program
            {
                return Err(invalid());
            }
            let prepared = self.compiler_prepared.as_ref().ok_or_else(invalid)?;
            let selected = wire::CompilerSelection {
                root_attempt: prepared.root_attempt,
                member_attempt: prepared.member_attempt,
                coordinator_attempt: prepared.coordinator_attempt,
                prepared_sha256: prepared.digest()?,
            };
            let witness = wire::TransportRequest {
                query: query.clone(),
                selected: selected.clone(),
            };
            let payload = witness.encode()?;
            // Reserve THIS receiver's complete incoming population/transport
            // before connect/receive; Host capacity pays another process.
            let room = budget.reserve_original_inputs(
                wire::TRANSPORT_ORIGINALS
                    + trust_resource_provenance::ORIGINAL_CONTROL_DESCRIPTORS
                    + 6,
            )?;
            let pin = self.host.connect(deadline)?;
            let mut channel = Channel::new(pin.stream().try_clone()?)?;
            channel.send(&witness.hello()?, deadline)?;
            pin.revalidate(deadline)?;
            channel.send(&payload, deadline)?;
            let reply = wire::TransportReply::decode(&channel.receive(deadline)?, &witness)?;
            let files = super::super::workload::receive_marked(
                &channel,
                wire::TRANSPORT_ORIGINALS,
                wire::TRANSPORT_MARKER,
                deadline,
            )?;
            self.compiler_transport = Some(OriginalCompilerTransport {
                files,
                reply,
                control: None,
                _descriptors: room,
            });
            self.compiler_transport
                .as_mut()
                .unwrap()
                .import_control(&self.host, deadline)?;
            self.compiler_transport
                .as_ref()
                .unwrap()
                .validate(self, compiler, deadline)?;
            pin.revalidate(deadline)?;
            channel.send(&[1], deadline)?;
            crate::runtime_input_retention::transport::require_reply_eof(&mut channel, deadline)?;
            let original = self.compiler_transport.as_ref().unwrap();
            original.validate(self, compiler, deadline)?;
            let prepared = self.compiler_prepared.as_ref().ok_or_else(invalid)?;
            let host = trust_resource_provenance::process::read_identity(self.host.host_pid())?;
            let actual = trust_resource_provenance::process::read_identity(prepared.identity.pid)?;
            let kind = if cfg!(target_os = "macos") {
                BirthKind::MacosWallMicroseconds
            } else {
                BirthKind::LinuxStartTicks
            };
            if prepared.identity.birth_kind != kind
                || actual.birth != prepared.identity.birth
                || actual.parent != host.pid
                || host.birth != self.host.host_birth()
                || (cfg!(target_os = "macos") && actual.parent_unique_id != host.unique_id)
            {
                return Err(invalid());
            }
            compiler.validate_loaded(actual, deadline)?;
            let runtime = compiler
                .runtime_environment()?
                .into_iter()
                .map(|(key, value)| (key.as_bytes().to_vec(), value.as_bytes().to_vec()))
                .collect::<Vec<_>>();
            let request = self.compiler_request.as_ref().ok_or_else(invalid)?;
            let expected = wire::compiler_producing_command(
                &request.binding,
                &request.command,
                self.host.helper_path().as_os_str().as_bytes(),
                &runtime,
                &original.reply.advertisement,
            )?;
            if expected != prepared.command {
                return Err(invalid());
            }
            self.compiler_scope.as_ref().unwrap().validate(deadline)?;
            compiler.validate(deadline)?;
            self.host.validate(deadline)?;
            if trust_resource_provenance::process::read_identity(actual.pid)? != actual
                || Instant::now() >= deadline
            {
                return Err(invalid());
            }
            Ok(selected)
        })();
        let result = run.and_then(|selected| self.bind_compiler(&selected, deadline));
        if let Err(error) = result {
            self.compiler_binding_attempted = true;
            self.accounting = None;
            self.terminal = Some(Status::Unknown {
                reason: "native producing compiler original transport binding unavailable".into(),
                started: self.started,
            });
            return Err(error);
        }
        Ok(())
    }
}
