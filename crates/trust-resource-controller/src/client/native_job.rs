// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Distinct authenticated native-job startup. A decoded Ready49/v3 is observation
//! data; only this original live exchange can retain its received descriptions.

use std::fs::File;
use std::io;
use std::os::fd::OwnedFd;
use std::sync::Arc;
use std::time::Instant;

use super::workload::{self, EarlyCpuSet, WorkloadControl};
use crate::Channel;
use crate::descriptors::{DescriptorBudget, OriginalInputPermit};
use crate::native_job::{Plan, READY_ROLE, host};

/// Not Clone or deserializable. Owns only descriptions received from the
/// authenticated original Host, plus that same still-live control connection.
pub struct AuthenticatedNativeJobStartup {
    reply: host::ReadyReply,
    originals: Option<Vec<OwnedFd>>,
    control: Option<WorkloadControl>,
    _reservation: OriginalInputPermit,
}
impl AuthenticatedNativeJobStartup {
    pub fn observation(&self) -> &host::ReadyReply {
        &self.reply
    }
    /// Transfer actual originals to their native lease owner without creating
    /// a another protocol startup or changing the complete106 digest.
    pub fn take_originals(&mut self) -> io::Result<Vec<File>> {
        self.originals
            .take()
            .map(|files| files.into_iter().map(File::from).collect())
            .ok_or_else(|| io::Error::other("native-job originals already adopted"))
    }
    pub fn take_control(&mut self) -> io::Result<WorkloadControl> {
        self.control
            .take()
            .ok_or_else(|| io::Error::other("native-job control already transferred"))
    }
}

fn check_binding(observed: [u8; 32], invocation: &Plan) -> io::Result<()> {
    use sha2::{Digest, Sha256};
    let expected: [u8; 32] = Sha256::digest(invocation.binding_preimage()?).into();
    if observed != expected {
        return Err(io::Error::new(
            io::ErrorKind::PermissionDenied,
            "native-job whole-plan binding differs",
        ));
    }
    Ok(())
}

impl super::Client {
    /// No v1 or generic-context fallback. The new purpose must be accepted by
    /// this independently selected original Host before actual adoption.
    pub fn native_job_ready(
        &self,
        request: &host::ReadyRequest,
        early: EarlyCpuSet,
        budget: &Arc<DescriptorBudget>,
        deadline: Instant,
    ) -> Result<AuthenticatedNativeJobStartup, super::CallError> {
        let payload = request.encode().map_err(super::before)?;
        let hello = format!(
            "{{\"version\":3,\"role\":\"{READY_ROLE}\",\"session\":\"{}\",\"capabilities\":{}}}",
            request.query.binding.session,
            host::READY_CAPABILITIES_JSON,
        );
        let original = self.host.connect(deadline).map_err(super::before)?;
        let mut channel = Channel::new(original.stream().try_clone().map_err(super::before)?)
            .map_err(super::before)?;
        channel.send(hello.as_bytes(), deadline).map_err(super::before)?;
        let exchange = (|| {
            original.revalidate(deadline)?;
            channel.send(&payload, deadline)?;
            let reply = host::ReadyReply::decode(&channel.receive(deadline)?, request)?;
            check_binding(reply.invocation_sha256, &request.plan)?;
            workload::live_context(&reply.context.context, None)?;
            super::sdk::validate_sdk_keeper(&reply.context.context)?;
            original.revalidate(deadline)?;
            let set: Vec<_> = reply.cpu_set().collect();
            // Demand is checked and retained BEFORE SCM_RIGHTS materializes the
            // SAME received set. The opaque startup outlives adopted leases.
            let reservation = budget.reserve_original_inputs(
                set.len()
                    .checked_add(1)
                    .ok_or_else(|| io::Error::other("native-job CPU envelope overflow"))?,
            )?;
            let originals = workload::receive_set(&channel, &set, early, deadline)?;
            original.revalidate(deadline)?;
            channel.send(&[1], deadline)?;
            let control = WorkloadControl::from_native_job_original_channel(
                channel,
                Arc::clone(&self.host),
                reply.context.context.root_attempt,
                reply.invocation_sha256,
                reply.context.context.cpu,
                &request.plan,
            )?;
            Ok(AuthenticatedNativeJobStartup {
                reply,
                originals: Some(originals),
                control: Some(control),
                _reservation: reservation,
            })
        })();
        // A lost reply/ack cannot establish that the original root did not
        // launch, release its bank, or permit a replacement execution.
        exchange.map_err(|error| super::CallError { delivery: super::Delivery::Unknown, error })
    }
}
