// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Direct read-only context bootstrap as the actual native producer. Producing
//! member execution uses the separately authenticated helper/proof protocol.

use std::io;
use std::sync::Arc;
use std::time::Instant;

use trust_resource_provenance::{PinnedHelper, Store, process};

use crate::{Channel, ContextQuery, ContextReply, ContextResponse};

mod coordinator;
pub use coordinator::{
    AuthenticatedCoordinator, CompilerScope, CompilerScopeError, CompilerScopeInputs,
    CoordinatorBroker, CoordinatorBrokerEndpoint, CoordinatorBrokerServer,
    CoordinatorCompilerCapture, CoordinatorOriginals, GraphAcknowledgement,
    PublicationAcknowledgement,
};

/// Delivery facts, never a claim that the original root did not launch or that
/// any resources were released. None authorizes CPU or an execution retry.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Delivery {
    BeforeRequest,
    Unknown,
    ContextUnavailable,
}
#[derive(Debug)]
pub struct CallError {
    pub delivery: Delivery,
    pub error: io::Error,
}
impl std::fmt::Display for CallError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "native resource context {:?}: {}", self.delivery, self.error)
    }
}
impl std::error::Error for CallError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        Some(&self.error)
    }
}
fn before(error: io::Error) -> CallError {
    CallError { delivery: Delivery::BeforeRequest, error }
}

/// Cache the original image/host selection once per root. Reconnects validate
/// actual kernel peer and original backing without repeatedly hashing images.
#[derive(Clone)]
pub struct Client {
    host: Arc<PinnedHelper>,
}
impl Client {
    /// Observe the independently selected original Store for equality checks.
    /// This data cannot select discovery, replace validation or grant a root.
    pub fn original_store_path(&self) -> &std::path::Path {
        self.host.original_store_path()
    }
    /// Bind the initial invocation inside the actual original cooperative
    /// workload root. Neither these bytes nor the reply grants execution.
    /// Missing support refuses; there is no generic-context fallback.
    pub fn workload_ready(
        &self,
        request: &crate::workload::host::ReadyRequest,
        early: workload::EarlyCpuSet,
        deadline: Instant,
    ) -> Result<workload::AuthenticatedWorkloadStartup, CallError> {
        use crate::workload::{WORKLOAD_READY_ROLE, host};
        let payload = request.encode().map_err(before)?;
        let hello = format!(
            "{{\"version\":3,\"role\":\"{WORKLOAD_READY_ROLE}\",\"session\":\"{}\",\"capabilities\":{}}}",
            request.query.binding.session,
            host::READY_CAPABILITIES_JSON,
        );
        let original = self.host.connect(deadline).map_err(before)?;
        let mut channel =
            Channel::new(original.stream().try_clone().map_err(before)?).map_err(before)?;
        channel.send(hello.as_bytes(), deadline).map_err(before)?;
        let exchanged = (|| {
            original.revalidate(deadline)?;
            channel.send(&payload, deadline)?;
            let reply = host::ReadyReply::decode(&channel.receive(deadline)?, request)?;
            original.revalidate(deadline)?;
            let startup = workload::receive_originals(&channel, reply, early, request, deadline)?;
            original.revalidate(deadline)?;
            channel.send(&[1], deadline)?;
            Ok(startup.attach_control(channel, Arc::clone(&self.host)))
        })();
        exchanged.map_err(|error| CallError { delivery: Delivery::ContextUnavailable, error })
    }
    pub fn discover(deadline: Instant) -> io::Result<Self> {
        Self::from_store(Store::open_account()?, deadline)
    }
    /// Explicit per-invocation discovery data, never a resource/store creator
    /// or a fallback. Applies the SAME original backing/image/native ancestor
    /// checks as account discovery; a pathname or decoded book grants nothing.
    pub fn discover_at(path: &std::path::Path, deadline: Instant) -> io::Result<Self> {
        Self::from_store(Store::open_at(path)?, deadline)
    }
    fn from_store(store: Store, deadline: Instant) -> io::Result<Self> {
        let host = store.connect_ancestor(deadline)?;
        Ok(Self::from_helper(Arc::new(host.into_helper(deadline)?)))
    }
    pub fn from_helper(host: Arc<PinnedHelper>) -> Self {
        Self { host }
    }
    /// Reconnect only to the independently selected ORIGINAL pin. This is
    /// discovery/authentication, never admission or a fallback to account state.
    pub fn connect_original_host(
        &self,
        deadline: Instant,
    ) -> io::Result<trust_resource_provenance::Host> {
        self.host.connect(deadline)
    }
    /// Obtain observations on an authenticated direct native connection before
    /// choosing initial-vs-borrowed admission. No helper process is spawned and
    /// no CPU credit, memory claim or subgroup is created by this lookup.
    pub fn context(
        &self,
        query: &ContextQuery,
        deadline: Instant,
    ) -> Result<ContextReply, CallError> {
        self.context_role(query, deadline, "native-context")
    }
    /// Explicit new codec/custody purpose. There is no legacy-role fallback.
    /// The reply still carries observations; the actual inherited keeper must
    /// separately match after this authenticated call.
    pub fn context_with_sdk(
        &self,
        query: &ContextQuery,
        deadline: Instant,
    ) -> Result<ContextReply, CallError> {
        let reply = self.context_role(query, deadline, crate::CONTEXT_SDK_ROLE)?;
        if reply.context.sdk.is_none() {
            return Err(CallError {
                delivery: Delivery::ContextUnavailable,
                error: io::Error::new(
                    io::ErrorKind::PermissionDenied,
                    "native context has no original inherited SDK keeper",
                ),
            });
        }
        Ok(reply)
    }
    /// Negotiate INSIDE the already registered original metadata root; there
    /// is no preparatory capability subprocess lacking durable ARM custody.
    /// Readiness data does not mint capacity. The host still requires its real
    /// root/SDK/GNU/memory and binds all later members to that original owner.
    pub fn metadata_context(
        &self,
        query: &ContextQuery,
        deadline: Instant,
    ) -> Result<ContextReply, CallError> {
        query.validate().map_err(before)?;
        let hello = format!(
            "{{\"version\":3,\"role\":\"{}\",\"session\":\"{}\",\"capabilities\":{}}}",
            crate::METADATA_READY_ROLE,
            query.binding.session,
            crate::METADATA_CAPABILITIES_JSON
        );
        let reply = self.context_exchange(query, deadline, hello.as_bytes())?;
        if reply.context.sdk.is_none() {
            return Err(CallError {
                delivery: Delivery::ContextUnavailable,
                error: io::Error::new(
                    io::ErrorKind::PermissionDenied,
                    "metadata readiness has no original inherited SDK keeper",
                ),
            });
        }
        Ok(reply)
    }
    /// Distinct Ready purpose INSIDE the original fixed-one resolver root.
    /// Data never replaces its actual original SDK/GNU/CPU/memory custody.
    pub fn resolver_context(
        &self,
        query: &ContextQuery,
        deadline: Instant,
    ) -> Result<ContextReply, CallError> {
        query.validate().map_err(before)?;
        let hello = format!(
            "{{\"version\":3,\"role\":\"{}\",\"session\":\"{}\",\"capabilities\":{}}}",
            crate::resolver::RESOLVER_READY_ROLE,
            query.binding.session,
            crate::resolver::RESOLVER_CAPABILITIES_JSON,
        );
        let reply = self.context_exchange(query, deadline, hello.as_bytes())?;
        if reply.context.sdk.is_none() {
            return Err(CallError {
                delivery: Delivery::ContextUnavailable,
                error: io::Error::new(
                    io::ErrorKind::PermissionDenied,
                    "resolver readiness has no original inherited SDK keeper",
                ),
            });
        }
        Ok(reply)
    }
    fn context_role(
        &self,
        query: &ContextQuery,
        deadline: Instant,
        role: &str,
    ) -> Result<ContextReply, CallError> {
        query.validate().map_err(before)?;
        let hello = format!(
            "{{\"version\":3,\"role\":\"{role}\",\"session\":\"{}\"}}",
            query.binding.session
        );
        self.context_exchange(query, deadline, hello.as_bytes())
    }
    fn context_exchange(
        &self,
        query: &ContextQuery,
        deadline: Instant,
        hello: &[u8],
    ) -> Result<ContextReply, CallError> {
        let payload = query.encode().map_err(before)?;
        let host = self.host.connect(deadline).map_err(before)?;
        let mut channel =
            Channel::new(host.stream().try_clone().map_err(before)?).map_err(before)?;
        channel.send(hello, deadline).map_err(before)?;
        let exchange = (|| {
            channel.send(&payload, deadline)?;
            let response = ContextResponse::decode(&channel.receive(deadline)?, query)?;
            host.revalidate(deadline)?;
            if let ContextResponse::Ready(reply) = &response {
                let (machine, boot) = process::host_boot()?;
                if reply.context.host != machine || reply.context.boot != boot {
                    return Err(io::Error::new(
                        io::ErrorKind::PermissionDenied,
                        "native context host or boot changed",
                    ));
                }
            }
            // Keep the original connected Host alive until the server observes
            // ACK; Darwin can lose peer credentials as soon as it closes.
            channel.send(&[1], deadline)?;
            Ok(response)
        })();
        match exchange {
            Ok(ContextResponse::Ready(reply)) => Ok(*reply),
            Ok(ContextResponse::Unavailable(value)) => Err(CallError {
                delivery: Delivery::ContextUnavailable,
                error: io::Error::new(io::ErrorKind::PermissionDenied, value.reason),
            }),
            Err(error) => Err(CallError { delivery: Delivery::Unknown, error }),
        }
    }
}

mod member;
pub use member::{
    HelperObservation, MemberError, MemberIo, ProxyChild, explicit_inheritance_supported,
    inherit_descriptions,
};

mod metadata;
pub use metadata::{
    CompletedProducedOperation, ContainedProducedError, ContainedProducedMember, LinkerError,
    LinkerMember, LinkerOutcome, LinkerResult, MetadataError, MetadataIo, MetadataMember,
    MetadataOutputStream, MetadataResult, ProducedError, ProducedFailureObservation,
    ProducedMember, ProducedResult, SuccessfulProducedCompletion,
};

mod telemetry;
pub use telemetry::ReceivedTelemetry;

mod liveness;
pub use liveness::HostLifeline;

pub mod bootstrap_graph;
pub mod native_job;
pub mod paired_qualification;
pub mod sdk;
pub mod workload;

#[cfg(feature = "probe-scheduler")]
pub mod probe_scheduler;
pub mod runtime_input_retention;
