// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! One measured observation and original host-only liveness pipe. Cached sample
//! age is retained across all RPC/descriptor work; it is never reset at receipt.
use std::io;
use std::os::fd::OwnedFd;
use std::time::{Duration, Instant};

use trust_resource_provenance::process;

use super::{CallError, Client, Delivery};
use crate::{Channel, TelemetryQuery, TelemetryReply, TelemetryResponse};

pub struct ReceivedTelemetry {
    pub reply: TelemetryReply,
    pub received_at: Instant,
    pub lifeline: OwnedFd,
}
impl ReceivedTelemetry {
    /// Includes time since the reply arrived, including descriptor transfer and
    /// host post-response validation. Overflow is unavailable, never fresh.
    pub fn age(&self) -> Option<Duration> {
        Duration::from_nanos(self.reply.snapshot.sample_age_ns)
            .checked_add(Instant::now().checked_duration_since(self.received_at)?)
    }
}
impl Client {
    /// Exactly one bounded authenticated native RPC. Callers cache/poll at a
    /// bounded cadence; this does not query the GUI or execute two CLI probes.
    pub fn telemetry(
        &self,
        query: &TelemetryQuery,
        deadline: Instant,
    ) -> Result<ReceivedTelemetry, CallError> {
        let before = |error| CallError { delivery: Delivery::BeforeRequest, error };
        let payload = query.encode().map_err(before)?;
        let host = self.host.connect(deadline).map_err(before)?;
        let mut channel =
            Channel::new(host.stream().try_clone().map_err(before)?).map_err(before)?;
        let hello = format!(
            "{{\"version\":3,\"role\":\"native-telemetry\",\"session\":\"{}\"}}",
            query.query.binding.session
        );
        channel.send(hello.as_bytes(), deadline).map_err(before)?;
        let mut exchange = || -> io::Result<_> {
            channel.send(&payload, deadline)?;
            let response = TelemetryResponse::decode(&channel.receive(deadline)?, query)?;
            let received_at = Instant::now();
            host.revalidate(deadline)?;
            if let TelemetryResponse::Ready(reply) = &response {
                let (machine, boot) = process::host_boot()?;
                if reply.context.context.host != machine || reply.context.context.boot != boot {
                    return Err(io::Error::new(
                        io::ErrorKind::PermissionDenied,
                        "native telemetry host or boot changed",
                    ));
                }
            }
            channel.send(&[1], deadline)?;
            match response {
                TelemetryResponse::Unavailable(value) => Ok(Err(value.reason)),
                TelemetryResponse::Ready(reply) => {
                    let lifeline = channel.receive_read_lifeline(deadline)?;
                    host.revalidate(deadline)?;
                    channel.send(&[2], deadline)?;
                    Ok(Ok(ReceivedTelemetry { reply: *reply, received_at, lifeline }))
                }
            }
        };
        match exchange() {
            Ok(Ok(value)) => Ok(value),
            Ok(Err(reason)) => Err(CallError {
                delivery: Delivery::ContextUnavailable,
                error: io::Error::new(io::ErrorKind::PermissionDenied, reason),
            }),
            Err(error) => Err(CallError { delivery: Delivery::Unknown, error }),
        }
    }
}
