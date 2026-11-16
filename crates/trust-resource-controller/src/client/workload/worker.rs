// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Actual original worker descriptions and explicit cooperative SDK settlement.
//! Dropping a loan sends no message and never frees the root bank's entry.
use std::fs::File;
use std::io;
use std::os::fd::{AsRawFd, OwnedFd};
use std::sync::Arc;
use std::time::Instant;

use super::{identity, live_context, receive};
use crate::Channel;
use crate::client::{CallError, Client, Delivery};
use crate::workload::host::worker as wire;

pub struct AuthenticatedWorkerCpu {
    reply: wire::Reply,
    original: OwnedFd,
    loan: WorkerLoan,
    origin: Arc<super::MemberOriginalContext>,
}
impl AuthenticatedWorkerCpu {
    pub fn observation(&self) -> &wire::Reply {
        &self.reply
    }
    pub fn into_original(self) -> (wire::Reply, File, WorkerLoan) {
        (self.reply, File::from(self.original), self.loan)
    }
    pub fn into_retained_original(
        self,
    ) -> (wire::Reply, File, WorkerLoan, Arc<super::MemberOriginalContext>) {
        (self.reply, File::from(self.original), self.loan, self.origin)
    }
}
/// Non-Clone and not deserializable. A saved Return frame has no access to this
/// live owner. Drop has NO RPC/return/settlement action, on every error path.
pub struct WorkerLoan {
    client: Client,
    returned: wire::Return,
    origin: Arc<super::MemberOriginalContext>,
}
impl WorkerLoan {
    pub fn slot(&self) -> u32 {
        self.returned.slot
    }
    /// # Safety
    /// The actual trusted SDK producing task must be joined or positively
    /// parked, with no producing work left using this unit. This is cooperative
    /// SDK settlement, not a kernel thread-exit observation or process outcome.
    pub unsafe fn settle_after_sdk_quiescence(
        mut self,
        deadline: Instant,
    ) -> Result<(), CallError> {
        self.returned.settlement = wire::Settlement::SdkQuiescent;
        self.settle(deadline)
    }
    /// # Safety
    /// Cancellation of the unused offer must atomically prevent dispatch. No
    /// task may have entered or be able to enter after this settlement.
    pub unsafe fn settle_unused_offer_after_cancel(
        mut self,
        deadline: Instant,
    ) -> Result<(), CallError> {
        self.returned.settlement = wire::Settlement::UnusedOfferCancelled;
        self.settle(deadline)
    }
    fn settle(self, deadline: Instant) -> Result<(), CallError> {
        self.origin
            .validate(deadline)
            .map_err(|error| CallError { delivery: Delivery::Unknown, error })?;
        let payload = self.returned.encode().map_err(super::super::before)?;
        let original = self.client.host.connect(deadline).map_err(super::super::before)?;
        let mut channel =
            Channel::new(original.stream().try_clone().map_err(super::super::before)?)
                .map_err(super::super::before)?;
        channel
            .send(&self.returned.hello().map_err(super::super::before)?, deadline)
            .map_err(super::super::before)?;
        let exchange = (|| {
            original.revalidate(deadline)?;
            channel.send(&payload, deadline)?;
            let reply = wire::Returned::decode(&channel.receive(deadline)?, &self.returned)?;
            live_context(
                &reply.context.context,
                Some(self.returned.request.original.member_attempt),
            )?;
            crate::client::sdk::validate_sdk_keeper(&reply.context.context)?;
            if &reply.context.context != self.origin.observation() {
                return Err(super::refused());
            }
            self.origin.validate(deadline)?;
            original.revalidate(deadline)?;
            channel.send(&[1], deadline)?;
            Ok(())
        })();
        exchange.map_err(|error| CallError { delivery: Delivery::Unknown, error })
    }
}
impl Client {
    pub fn workload_extra(
        &self,
        request: &wire::Request,
        deadline: Instant,
    ) -> Result<Option<AuthenticatedWorkerCpu>, CallError> {
        let payload = request.encode().map_err(super::super::before)?;
        let original = self.host.connect(deadline).map_err(super::super::before)?;
        let mut channel =
            Channel::new(original.stream().try_clone().map_err(super::super::before)?)
                .map_err(super::super::before)?;
        channel
            .send(&request.hello().map_err(super::super::before)?, deadline)
            .map_err(super::super::before)?;
        let exchange = (|| {
            original.revalidate(deadline)?;
            channel.send(&payload, deadline)?;
            let reply = wire::Reply::decode(&channel.receive(deadline)?, request)?;
            live_context(&reply.context.context, Some(request.original.member_attempt))?;
            crate::client::sdk::validate_sdk_keeper(&reply.context.context)?;
            let granted = match &reply.decision {
                wire::Decision::Granted { loan, slot, backing } => {
                    let mut originals = receive(&channel, 1, deadline)?;
                    let fd = originals.remove(0);
                    if identity(fd.as_raw_fd())? != *backing {
                        return Err(super::refused());
                    }
                    Some((fd, *loan, *slot))
                }
                wire::Decision::Busy => None,
                wire::Decision::Refused { reason } => {
                    return Err(io::Error::new(io::ErrorKind::PermissionDenied, reason.clone()));
                }
            };
            original.revalidate(deadline)?;
            channel.send(&[1], deadline)?;
            let Some((fd, loan, slot)) = granted else {
                return Ok(None);
            };
            let origin = super::MemberOriginalContext::capture(
                self.clone(),
                request.original.clone(),
                reply.context.context.clone(),
                deadline,
            )?;
            Ok(Some(AuthenticatedWorkerCpu {
                reply,
                original: fd,
                origin: origin.clone(),
                loan: WorkerLoan {
                    client: self.clone(),
                    origin,
                    returned: wire::Return {
                        request: request.clone(),
                        loan,
                        slot,
                        settlement: wire::Settlement::SdkQuiescent,
                    },
                },
            }))
        })();
        exchange.map_err(|error| CallError { delivery: Delivery::Unknown, error })
    }
}
