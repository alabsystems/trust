// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Private proxy control data. Decoding creates no resource authority. The
//! custodian must authenticate the actual native producer, original live job,
//! CPU/GNU descriptions and retained memory before launching a member.

#![cfg_attr(
    all(
        trust_std,
        feature = "client",
        any(target_os = "linux", target_os = "macos")
    ),
    feature(trust_process_inherit_fds)
)]

pub mod accounting;
pub mod bootstrap_graph;
mod context;
mod helper_fds;
pub mod linker;
mod locator;
pub mod native_job;
pub mod paired_qualification;
pub mod resolver;
pub mod runtime_input_retention;
mod sealed_metadata;
pub mod workload;
pub use helper_fds::{HelperFds, WorkloadHelperFds};
pub use sealed_metadata::{
    CONTEXT_SDK_CAPABILITY, CONTEXT_SDK_ROLE, METADATA_CAPABILITIES_JSON, METADATA_CAPABILITY,
    METADATA_CAPABILITY_QUERY, METADATA_EVENT_PREFIX_MAX_BYTES, METADATA_MAX_OUTPUT,
    METADATA_MAX_TIMEOUT_NS, METADATA_READY_ROLE, METADATA_REPORT_MAX_BYTES, METADATA_REQUEST_ROLE,
    METADATA_STARTUP_ARGUMENT, MetadataBatch, MetadataBatchReport, MetadataCompletion, MetadataCpu,
    MetadataEvent, MetadataFailureObservation, MetadataFile, MetadataPrepared, MetadataProbe,
    MetadataProbeCommand, MetadataResult, MetadataRunnerObservation, SealedMetadataRequest,
};
mod telemetry;
pub use telemetry::*;
mod types;
pub use context::*;
mod validate;
mod wire;
pub use types::*;
pub use wire::{Cancel, ProducerChallenge};
#[cfg(all(feature = "channel", any(target_os = "linux", target_os = "macos")))]
mod channel;
#[cfg(all(feature = "channel", any(target_os = "linux", target_os = "macos")))]
pub use channel::Channel;
#[cfg(test)]
mod tests;

#[cfg(all(feature = "client", any(target_os = "linux", target_os = "macos")))]
pub mod client;

#[cfg(all(unix, feature = "client"))]
pub mod descriptors;

/// Private solver bootstrap data and authenticated final-image receiver.
pub mod solver_bootstrap;
