// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Original Host/FD custody for distinct partial initial startup. Decoded
//! fields and a support declaration never construct this owner.
use sha2::{Digest, Sha256};

use super::super::{CallError, Delivery, before};
use super::*;
use crate::workload::host::initial as wire;
#[derive(Clone, Copy)]
pub(super) enum GnuStage {
    Awaiting([u8; 16]),
    Armed,
}

pub struct AuthenticatedInitialStartup {
    reply: wire::ReadyReply,
    originals: Vec<OwnedFd>,
    control: WorkloadControl,
    keeper: std::sync::Arc<super::AuthenticatedInitialKeeper>,
}
impl AuthenticatedInitialStartup {
    pub fn observation(&self) -> &wire::ReadyReply {
        &self.reply
    }
    pub fn into_originals(
        self,
    ) -> (
        wire::ReadyReply,
        Vec<File>,
        WorkloadControl,
        std::sync::Arc<super::AuthenticatedInitialKeeper>,
    ) {
        (
            self.reply,
            self.originals.into_iter().map(File::from).collect(),
            self.control,
            self.keeper,
        )
    }
}

impl super::super::Client {
    /// Authenticate the original Root/SDK/M context and receive its actual
    /// inherited pair on the SAME pinned native Host connection. Unsupported
    /// V1/old hosts refuse; there is no generic or full-domain fallback.
    pub fn workload_initial_ready(
        &self,
        request: &wire::ReadyRequest,
        early: EarlyCpuSet,
        keeper: super::EarlyInitialKeeper,
        deadline: Instant,
    ) -> Result<AuthenticatedInitialStartup, CallError> {
        let payload = request.encode().map_err(before)?;
        let digest: [u8; 32] = Sha256::digest(&payload).into();
        let hello = format!(
            "{{\"version\":3,\"role\":\"{}\",\"session\":\"{}\",\"capabilities\":{}}}",
            wire::READY_ROLE,
            request.query.binding.session,
            wire::READY_CAPABILITIES_JSON
        );
        let original = self.host.connect(deadline).map_err(before)?;
        let mut channel =
            Channel::new(original.stream().try_clone().map_err(before)?).map_err(before)?;
        channel.send(hello.as_bytes(), deadline).map_err(before)?;
        let exchange = (|| {
            original.revalidate(deadline)?;
            channel.send(&payload, deadline)?;
            let reply = wire::ReadyReply::decode(&channel.receive(deadline)?, request)?;
            if reply.invocation_sha256 != digest {
                return Err(refused());
            }
            live_context(&reply.context.context, None)?;
            super::super::sdk::validate_sdk_keeper(&reply.context.context)?;
            original.revalidate(deadline)?;
            let originals = receive_set(&channel, &[&reply.primary], early, deadline)?;
            let keeper = keeper.authenticate(&reply)?;
            original.revalidate(deadline)?;
            let mut control = WorkloadControl::from_original_channel(
                channel,
                std::sync::Arc::clone(&self.host),
                reply.context.context.root_attempt,
                reply.invocation_sha256,
                reply.context.context.cpu,
            );
            control.initial = Some(GnuStage::Awaiting(reply.phase));
            control.channel.send(&[1], deadline)?;
            Ok(AuthenticatedInitialStartup { reply, originals, control, keeper })
        })();
        exchange.map_err(|error| CallError { delivery: Delivery::ContextUnavailable, error })
    }
}
