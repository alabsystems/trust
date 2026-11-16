// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Actual original input transfer, distinct from any later compiler admission.
use super::*;
use crate::descriptors::{AdmittedRootDirectory, AdmittedRootFile, DescriptorBudget};
use crate::workload::host::coordinator::{SCOPE_MARKER, ScopeFile, ScopeReply, ScopeRequest};

pub struct CompilerScope {
    request: ScopeRequest,
    directory: Arc<AdmittedRootDirectory>,
    files: Vec<Arc<AdmittedRootFile>>,
    host: Arc<PinnedHelper>,
    failed: AtomicBool,
    deadline: Instant,
}
/// The actual retained directory and selected producer files, never path DATA.
pub struct CompilerScopeInputs {
    pub directory: Arc<AdmittedRootDirectory>,
    pub dependencies: Vec<(Arc<AdmittedRootFile>, [u8; 16])>,
}
pub enum CompilerScopeError {
    BeforeRequest(io::Error),
    Unknown { original: Arc<CompilerScope>, error: io::Error },
}
impl std::fmt::Debug for CompilerScopeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::BeforeRequest(error) => f.debug_tuple("BeforeRequest").field(error).finish(),
            Self::Unknown { error, .. } => {
                f.debug_struct("Unknown").field("error", error).finish_non_exhaustive()
            }
        }
    }
}
impl std::fmt::Display for CompilerScopeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "native compiler input attachment {self:?}")
    }
}
impl std::error::Error for CompilerScopeError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        Some(match self {
            Self::BeforeRequest(error) | Self::Unknown { error, .. } => error,
        })
    }
}
impl CompilerScope {
    pub fn retained_bytes(&self) -> Option<usize> {
        std::mem::size_of::<Self>().checked_add(self.request.retained_bytes()?)?.checked_add(
            self.files.capacity().checked_mul(std::mem::size_of::<Arc<AdmittedRootFile>>())?,
        )
    }
    pub fn request(&self) -> &ScopeRequest {
        &self.request
    }
    pub fn validate(&self, deadline: Instant) -> io::Result<()> {
        let deadline = deadline.min(self.deadline);
        let result = (|| {
            if self.failed.load(Ordering::Acquire) {
                return Err(refused());
            }
            self.host.validate(deadline)?;
            self.directory.validate(deadline)?;
            for file in &self.files {
                file.validate(deadline)?;
            }
            self.host.validate(deadline)?;
            if Instant::now() >= deadline {
                return Err(io::ErrorKind::TimedOut.into());
            }
            Ok(())
        })();
        if result.is_err() {
            self.failed.store(true, Ordering::Release);
        }
        result
    }
}
fn send_originals(
    channel: &Channel,
    originals: &[BorrowedFd<'_>],
    deadline: Instant,
) -> io::Result<()> {
    if originals.is_empty()
        || originals.len() > 1 + crate::workload::host::coordinator::MAX_SCOPE_FILES
    {
        return Err(refused());
    }
    #[cfg(target_os = "macos")]
    {
        let enabled: libc::c_int = 1;
        // SAFETY: configure only this private held socket so a disconnected
        // receiver becomes a retained io::Error, never an ambient SIGPIPE.
        if unsafe {
            libc::setsockopt(
                channel.as_fd().as_raw_fd(),
                libc::SOL_SOCKET,
                libc::SO_NOSIGPIPE,
                (&enabled as *const libc::c_int).cast(),
                std::mem::size_of_val(&enabled) as _,
            )
        } != 0
        {
            return Err(io::Error::last_os_error());
        }
    }
    let raw = originals.iter().map(AsRawFd::as_raw_fd).collect::<Vec<_>>();
    let length = std::mem::size_of_val(raw.as_slice());
    // SAFETY: bounded <=129 native int descriptors; CMSG_SPACE only computes a size.
    let space = unsafe { libc::CMSG_SPACE(length as u32) } as usize;
    let mut control = vec![0usize; space.div_ceil(std::mem::size_of::<usize>())];
    let mut marker = [SCOPE_MARKER];
    let mut iov = libc::iovec { iov_base: marker.as_mut_ptr().cast(), iov_len: 1 };
    // SAFETY: zero is the initial msghdr representation; all used pointers are set below.
    let mut message: libc::msghdr = unsafe { std::mem::zeroed() };
    message.msg_iov = &mut iov;
    message.msg_iovlen = 1;
    message.msg_control = control.as_mut_ptr().cast();
    message.msg_controllen = space as _;
    // SAFETY: aligned control holds the complete bounded ancillary description.
    unsafe {
        let header = libc::CMSG_FIRSTHDR(&message);
        if header.is_null() {
            return Err(refused());
        }
        (*header).cmsg_level = libc::SOL_SOCKET;
        (*header).cmsg_type = libc::SCM_RIGHTS;
        (*header).cmsg_len = libc::CMSG_LEN(length as u32) as _;
        std::ptr::copy_nonoverlapping(raw.as_ptr().cast::<u8>(), libc::CMSG_DATA(header), length);
    }
    loop {
        if Instant::now() >= deadline {
            return Err(io::ErrorKind::TimedOut.into());
        }
        #[cfg(target_os = "linux")]
        let flags = libc::MSG_NOSIGNAL;
        #[cfg(not(target_os = "linux"))]
        let flags = 0;
        // SAFETY: all buffers remain live; this transfers copies of retained originals.
        let sent = unsafe { libc::sendmsg(channel.as_fd().as_raw_fd(), &message, flags) };
        if sent == 1 {
            return Ok(());
        }
        if sent >= 0 {
            return Err(io::ErrorKind::WriteZero.into());
        }
        let error = io::Error::last_os_error();
        match error.kind() {
            io::ErrorKind::Interrupted => continue,
            io::ErrorKind::WouldBlock => {
                let mut poll = libc::pollfd {
                    fd: channel.as_fd().as_raw_fd(),
                    events: libc::POLLOUT,
                    revents: 0,
                };
                let millis =
                    deadline.saturating_duration_since(Instant::now()).as_millis().clamp(1, 100)
                        as i32;
                // SAFETY: one initialized pollfd, no ownership transfer.
                let ready = unsafe { libc::poll(&mut poll, 1, millis) };
                if ready < 0 && io::Error::last_os_error().kind() != io::ErrorKind::Interrupted {
                    return Err(io::Error::last_os_error());
                }
            }
            _ => return Err(error),
        }
    }
}
impl Client {
    /// Attach actual selected originals; this never starts/adopts a CPU unit.
    /// # Safety
    /// The trusted parent derives the directory from the SAME selected Unit
    /// and files from its actual retired producer/dependency ledger, retains
    /// those owners and original source/SDK/output guards through consumers,
    /// and separately enforces semantic coverage, retirement and proof grades.
    /// It already retains the SAME distinct reserved compiler primary for this
    /// operation; this input attachment cannot create or settle that loan.
    pub unsafe fn attach_compiler_scope(
        &self,
        query: &crate::ContextQuery,
        coordinator: [u8; 16],
        member: [u8; 16],
        inputs: CompilerScopeInputs,
        budget: &Arc<DescriptorBudget>,
        deadline: Instant,
    ) -> Result<Arc<CompilerScope>, CompilerScopeError> {
        let CompilerScopeInputs { directory, dependencies } = inputs;
        if dependencies.len() > crate::workload::host::coordinator::MAX_SCOPE_FILES {
            return Err(CompilerScopeError::BeforeRequest(refused()));
        }
        let request = ScopeRequest {
            query: query.clone(),
            coordinator,
            member,
            directory: directory.path().as_os_str().as_bytes().to_vec(),
            files: dependencies
                .iter()
                .map(|(file, producer)| ScopeFile {
                    path: file.observation().path.as_os_str().as_bytes().to_vec(),
                    producer: *producer,
                })
                .collect(),
        };
        let setup = (|| {
            let payload = request.encode()?;
            directory.validate(deadline)?;
            for (file, _) in &dependencies {
                file.validate(deadline)?;
                if file.output_root() != directory.output_root() {
                    return Err(refused());
                }
            }
            let permit = budget.reserve_member_transport()?;
            let pin = self.host.connect(deadline)?;
            let mut channel = Channel::new(pin.stream().try_clone()?)?;
            channel.send(&request.hello()?, deadline)?;
            Ok((payload, permit, pin, channel))
        })()
        .map_err(CompilerScopeError::BeforeRequest)?;
        let (payload, _permit, pin, mut channel) = setup;
        let original = Arc::new(CompilerScope {
            request,
            directory,
            files: dependencies.into_iter().map(|(file, _)| file).collect(),
            host: Arc::clone(&self.host),
            failed: AtomicBool::new(false),
            deadline,
        });
        let exchange = (|| {
            original.validate(deadline)?;
            pin.revalidate(deadline)?;
            channel.send(&payload, deadline)?;
            // The Host has now authenticated/admitted its bounded receive
            // envelope. No SCM rights are offered before this exact marker.
            if channel.receive(deadline)? != [SCOPE_MARKER] {
                return Err(refused());
            }
            let mut descriptions = vec![original.directory.descriptor(deadline)?];
            for file in &original.files {
                descriptions.push(file.descriptor(deadline)?);
            }
            send_originals(&channel, &descriptions, deadline)?;
            ScopeReply::decode(&channel.receive(deadline)?, &original.request)?;
            original.validate(deadline)?;
            pin.revalidate(deadline)?;
            channel.send(&[1], deadline)?;
            crate::runtime_input_retention::transport::require_reply_eof(&mut channel, deadline)?;
            original.validate(deadline)
        })();
        match exchange {
            Ok(()) => Ok(original),
            Err(error) => {
                original.failed.store(true, Ordering::Release);
                Err(CompilerScopeError::Unknown { original, error })
            }
        }
    }
}
