// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Distinct authenticated paired startup. A decoded Ready49/v2 is observation
//! data; only this original live exchange can retain its received descriptions.

use std::fs::File;
use std::io;
use std::os::fd::OwnedFd;
use std::sync::Arc;
use std::time::Instant;

use super::workload::{self, EarlyCpuSet, WorkloadControl};
use crate::Channel;
use crate::paired_qualification::{PAIRED_READY_ROLE, PairedInvocation, host};

/// Not Clone or deserializable. Owns only descriptions received from the
/// authenticated original Host, plus that same still-live control connection.
pub struct AuthenticatedPairedQualificationStartup {
    reply: host::ReadyReply,
    originals: Vec<OwnedFd>,
    control: WorkloadControl,
}
impl AuthenticatedPairedQualificationStartup {
    pub fn observation(&self) -> &host::ReadyReply {
        &self.reply
    }
    /// Transfer actual originals to their native lease owner without creating
    /// a v1 startup or changing the complete60 digest to a consumer40 digest.
    pub fn into_originals(self) -> (host::ReadyReply, Vec<File>, WorkloadControl) {
        (self.reply, self.originals.into_iter().map(File::from).collect(), self.control)
    }
}

fn check_binding(observed: [u8; 32], invocation: &PairedInvocation) -> io::Result<()> {
    use sha2::{Digest, Sha256};
    let expected: [u8; 32] = Sha256::digest(invocation.binding_preimage()?).into();
    if observed != expected {
        return Err(io::Error::new(
            io::ErrorKind::PermissionDenied,
            "paired whole-plan binding differs",
        ));
    }
    Ok(())
}

impl super::Client {
    /// No v1 or generic-context fallback. The new purpose must be accepted by
    /// this independently selected original Host before actual adoption.
    pub fn paired_qualification_ready(
        &self,
        request: &host::ReadyRequest,
        early: EarlyCpuSet,
        deadline: Instant,
    ) -> Result<AuthenticatedPairedQualificationStartup, super::CallError> {
        let payload = request.encode().map_err(super::before)?;
        let hello = format!(
            "{{\"version\":3,\"role\":\"{PAIRED_READY_ROLE}\",\"session\":\"{}\",\"capabilities\":{}}}",
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
            check_binding(reply.invocation_sha256, &request.invocation)?;
            workload::live_context(&reply.context.context, None)?;
            super::sdk::validate_sdk_keeper(&reply.context.context)?;
            original.revalidate(deadline)?;
            let set: Vec<_> = reply.cpu_set().collect();
            let originals = workload::receive_set(&channel, &set, early, deadline)?;
            original.revalidate(deadline)?;
            channel.send(&[1], deadline)?;
            let control = WorkloadControl::from_original_channel(
                channel,
                Arc::clone(&self.host),
                reply.context.context.root_attempt,
                reply.invocation_sha256,
                reply.context.context.cpu,
            );
            Ok(AuthenticatedPairedQualificationStartup { reply, originals, control })
        })();
        // A lost reply/ack cannot establish that the original root did not
        // launch, release its bank, or permit a replacement execution.
        exchange.map_err(|error| super::CallError { delivery: super::Delivery::Unknown, error })
    }
}

#[cfg(test)]
mod tests {
    use sha2::{Digest, Sha256};

    use super::*;

    #[test]
    fn complete_paired_binding_rejects_consumer40_and_undomained60_hashes() {
        let plan = crate::paired_qualification::tests::invocation();
        let digest = Sha256::digest(plan.binding_preimage().unwrap()).into();
        check_binding(digest, &plan).unwrap();
        assert!(
            check_binding(Sha256::digest(plan.consumer.encode().unwrap()).into(), &plan).is_err()
        );
        assert!(check_binding(Sha256::digest(plan.encode().unwrap()).into(), &plan).is_err());
    }

    #[test]
    fn same_consumer_never_authorizes_another_ay_subject_or_policy_input() {
        let plan = crate::paired_qualification::tests::invocation();
        let digest = Sha256::digest(plan.binding_preimage().unwrap()).into();
        for mutation in 0..7 {
            let mut changed = plan.clone();
            match mutation {
                0 => changed.ay.source_commit[0] ^= 1,
                1 => changed.ay.crate_tree[0] ^= 1,
                2 => changed.ay.workspace_manifest.sha256[0] ^= 1,
                3 => changed.ay.crate_manifest.sha256[0] ^= 1,
                4 => changed.ay.lockfile.sha256[0] ^= 1,
                5 => changed.ay.cargo_config.sha256[0] ^= 1,
                6 => changed.ay.toolchain_config.sha256[0] ^= 1,
                _ => unreachable!(),
            }
            assert!(changed.consumer == plan.consumer);
            assert!(check_binding(digest, &changed).is_err(), "mutation {mutation}");
        }
    }
}
