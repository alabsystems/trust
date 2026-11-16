// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! One-shot original coordinator startup. A decoded reply cannot supply any
//! of these descriptions, their original Host pin or the native parent loan.
use std::os::fd::{AsRawFd, BorrowedFd, OwnedFd};
use std::os::unix::ffi::OsStrExt as _;
use std::sync::atomic::{AtomicBool, Ordering};

use super::*;
use crate::workload::host::coordinator::{OriginalReply, OriginalRequest};

mod broker;
mod scope;
pub use broker::{
    CoordinatorBroker, CoordinatorBrokerEndpoint, CoordinatorBrokerServer,
    CoordinatorCompilerCapture, GraphAcknowledgement, PublicationAcknowledgement,
};
pub use scope::{CompilerScope, CompilerScopeError, CompilerScopeInputs};

pub struct AuthenticatedCoordinator {
    reply: OriginalReply,
    primary: OwnedFd,
    broker: OwnedFd,
    outputs: Vec<OwnedFd>,
    host: Arc<PinnedHelper>,
    failed: AtomicBool,
    // LAST: the actual accepted originals and validation scratch close before
    // this same child-process capacity reservation can return.
    _descriptors: crate::descriptors::OriginalInputPermit,
}
/// Actual received originals, consumed by the native CPU/Layout adopters.
/// No public constructor, Clone or deserializer exists.
pub struct CoordinatorOriginals {
    reply: OriginalReply,
    primary: OwnedFd,
    broker: OwnedFd,
    outputs: Vec<OwnedFd>,
    host: Arc<PinnedHelper>,
    failed: AtomicBool,
    broker_taken: AtomicBool,
    _descriptors: crate::descriptors::OriginalInputPermit,
}
fn refused() -> io::Error {
    io::ErrorKind::PermissionDenied.into()
}
fn identity(fd: BorrowedFd<'_>) -> io::Result<crate::FileIdentity> {
    use std::os::unix::fs::MetadataExt as _;
    let flags = unsafe { libc::fcntl(fd.as_raw_fd(), libc::F_GETFD) };
    let file = std::fs::File::from(fd.try_clone_to_owned()?);
    let meta = file.metadata()?;
    if flags < 0
        || flags & libc::FD_CLOEXEC == 0
        || !meta.is_file()
        || meta.nlink() != 1
        || meta.uid() != unsafe { libc::geteuid() }
        || meta.mode() & 0o022 != 0
    {
        return Err(refused());
    }
    Ok(crate::FileIdentity { device: meta.dev(), inode: meta.ino() })
}
fn validate_originals(
    reply: &OriginalReply,
    primary: &OwnedFd,
    outputs: &[OwnedFd],
    host: &PinnedHelper,
    failed: &AtomicBool,
    deadline: Instant,
) -> io::Result<()> {
    use std::os::fd::AsFd as _;
    let result = (|| {
        if failed.load(Ordering::Acquire) || Instant::now() >= deadline {
            return Err(refused());
        }
        host.validate(deadline)?;
        super::workload::live_context(
            &reply.context.context,
            match reply.context.context.subject {
                crate::Subject::RegisteredMember { attempt, .. } => Some(attempt),
                _ => return Err(refused()),
            },
        )?;
        super::sdk::validate_sdk_keeper(&reply.context.context)?;
        reply.encode()?;
        if identity(primary.as_fd())? != reply.primary.backing
            || outputs.len() != reply.outputs.locks.len()
        {
            return Err(refused());
        }
        for (fd, lock) in outputs.iter().zip(&reply.outputs.locks) {
            if identity(fd.as_fd())? != lock.backing {
                return Err(refused());
            }
        }
        host.validate(deadline)
    })();
    if result.is_err() {
        failed.store(true, Ordering::Release);
    }
    result
}

impl AuthenticatedCoordinator {
    pub fn observation(&self) -> &OriginalReply {
        &self.reply
    }
    pub fn validate(&self, deadline: Instant) -> io::Result<()> {
        validate_originals(
            &self.reply,
            &self.primary,
            &self.outputs,
            &self.host,
            &self.failed,
            deadline,
        )
    }
    /// Failed validation preserves the entire original capsule for the owning
    /// abort/retention path. It never returns an apparently unused CPU unit.
    pub fn into_parts(
        self,
        deadline: Instant,
    ) -> Result<CoordinatorOriginals, (io::Error, Box<Self>)> {
        if let Err(error) = self.validate(deadline) {
            return Err((error, Box::new(self)));
        }
        Ok(CoordinatorOriginals {
            reply: self.reply,
            primary: self.primary,
            broker: self.broker,
            outputs: self.outputs,
            host: self.host,
            failed: self.failed,
            broker_taken: AtomicBool::new(false),
            _descriptors: self._descriptors,
        })
    }
}
impl CoordinatorOriginals {
    pub fn validate(&self, deadline: Instant) -> io::Result<()> {
        validate_originals(
            &self.reply,
            &self.primary,
            &self.outputs,
            &self.host,
            &self.failed,
            deadline,
        )
    }
    pub fn observation(&self) -> &OriginalReply {
        &self.reply
    }
    pub fn primary(&self) -> BorrowedFd<'_> {
        use std::os::fd::AsFd as _;
        self.primary.as_fd()
    }
    pub fn outputs(&self) -> &[OwnedFd] {
        &self.outputs
    }
}
impl Client {
    pub fn coordinator_original(
        &self,
        request: &OriginalRequest,
        budget: &Arc<crate::descriptors::DescriptorBudget>,
        deadline: Instant,
    ) -> Result<AuthenticatedCoordinator, CallError> {
        let payload = request.encode().map_err(before)?;
        let original = self.host.connect(deadline).map_err(before)?;
        let mut channel =
            Channel::new(original.stream().try_clone().map_err(before)?).map_err(before)?;
        channel.send(&request.hello().map_err(before)?, deadline).map_err(before)?;
        let exchange = (|| {
            original.revalidate(deadline)?;
            channel.send(&payload, deadline)?;
            let reply = OriginalReply::decode(&channel.receive(deadline)?, request)?;
            super::workload::live_context(&reply.context.context, Some(request.member_attempt))?;
            super::sdk::validate_sdk_keeper(&reply.context.context)?;
            // The bounded authenticated reply declares the complete received
            // population. Admit it in THIS process before recvmsg installs any
            // of its CPU/broker/Layout descriptions, including one validation
            // scratch duplicate. Host-side capacity is a different process.
            let demand = reply.outputs.locks.len().checked_add(3).ok_or_else(refused)?;
            let descriptors = budget.reserve_original_inputs(demand)?;
            let mut originals =
                super::workload::receive(&channel, 2 + reply.outputs.locks.len(), deadline)?;
            let primary = originals.remove(0);
            let broker = originals.remove(0);
            let owner = AuthenticatedCoordinator {
                reply,
                primary,
                broker,
                outputs: originals,
                host: Arc::clone(&self.host),
                failed: AtomicBool::new(false),
                _descriptors: descriptors,
            };
            owner.validate(deadline)?;
            original.revalidate(deadline)?;
            channel.send(&[1], deadline)?;
            crate::runtime_input_retention::transport::require_reply_eof(&mut channel, deadline)?;
            owner.validate(deadline)?;
            Ok(owner)
        })();
        exchange.map_err(|error| CallError { delivery: Delivery::Unknown, error })
    }
}
