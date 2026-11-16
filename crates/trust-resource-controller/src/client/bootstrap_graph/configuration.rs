//! Bounded ordered actual configuration offers on the same accepted channel.
use std::io;
use std::os::fd::BorrowedFd;
use std::time::Instant;

use sha2::{Digest as _, Sha256};

use super::{
    GraphFailure, OutputBoundBootstrapGraph, SourceBoundBootstrapGraph, bounded, finish, live,
    original_deadline,
};
use crate::bootstrap_graph::{ConfigurationAttachment, ConfigurationReply, transport};
use crate::client::Delivery;

impl SourceBoundBootstrapGraph {
    /// The accepted binding DATA; it is neither a config issuer nor a seed.
    pub fn configuration(&self) -> Option<&ConfigurationAttachment> {
        self.configuration.last()
    }

    /// Accepted bindings are DATA. Every actual issuer must remain retained.
    pub fn configurations(&self) -> &[ConfigurationAttachment] {
        &self.configuration
    }
    /// Negative limits for the actual issuer BEFORE allocating/reading a file.
    /// These counts cannot construct an issuer or authorize a content read.
    pub fn configuration_remaining_files(&self) -> usize {
        self.configuration_budget.remaining_files()
    }
    pub fn configuration_remaining_bytes(&self) -> u64 {
        self.configuration_budget.remaining_bytes()
    }

    /// Transfer a close-only configuration description under the same original
    /// source-bound graph, in exact sequence. All earlier actual issuers must
    /// also remain held and bookended. The receiver retains the delivered resource before
    /// checking its contents; acknowledgement does not grant preparation.
    ///
    /// # Safety
    /// Before capture the caller must apply both remaining limits to the actual
    /// issuer, refusing zero and oversize before reading/allocating.
    /// The caller must retain the actual same-scope OriginalPreparationInputs
    /// issuer before entering this method and through actual graph retirement.
    /// `source` and `configuration` must be borrowed from those real offers,
    /// with their original-owner checks before and after this entire exchange,
    /// including errors/unwind. `deadline` must not exceed the actual minimum
    /// original source/configuration input endpoint. Paths, hashes, arbitrary reopened files, parsed
    /// Config and this accepted binding cannot substitute for those owners.
    pub unsafe fn attach_original_configuration(
        mut self,
        mut request: ConfigurationAttachment,
        source: &[BorrowedFd<'_>; 4],
        configuration: BorrowedFd<'_>,
        deadline: Instant,
    ) -> Result<Self, GraphFailure> {
        let started = Instant::now();
        let mut original = self.original.take().expect("private source-bound graph");
        let preflight = (|| {
            // Capture BEFORE any request or content observation. The native
            // enrollment anchor necessarily precedes this sender capture, so
            // anchor + remaining only shortens the actual input endpoint.
            let remaining =
                deadline.checked_duration_since(started).ok_or(io::ErrorKind::TimedOut)?;
            request.input_remaining_ns =
                remaining.as_nanos().try_into().map_err(|_| crate::wire::invalid())?;
            bounded(original.deadline, deadline)?;
            original.queries.enrollment_allowed()?;
            if self.materialization.is_none() || request.key != original.request.key {
                return Err(crate::wire::invalid());
            }
            self.configuration_budget.reserve(&request)?;
            transport::check_source(&self.source, source, deadline)?;
            transport::check_configuration(&request, source[0], configuration, deadline)?;
            original.check(deadline)
        })();
        if let Err(error) = preflight {
            return Err(GraphFailure::retaining(original, Delivery::BeforeRequest, error));
        }
        let payload = match request.encode() {
            Ok(payload) => payload,
            Err(error) => {
                return Err(GraphFailure::retaining(original, Delivery::BeforeRequest, error));
            }
        };
        let digest: [u8; 32] =
            Sha256::digest(request.binding_preimage().expect("same validated configuration frame"))
                .into();
        let mut effective = deadline;
        let result = finish(deadline, || {
            original.channel.send(&payload, deadline)?;
            match ConfigurationReply::decode(
                &original.channel.receive(deadline)?,
                &request,
                digest,
            )? {
                ConfigurationReply::Prepared { context, remaining_input_ns, .. }
                    if context == original.context =>
                {
                    effective = original_deadline(started, remaining_input_ns)?.min(effective);
                }
                ConfigurationReply::Refused { reason, .. } => {
                    return Err(io::Error::new(io::ErrorKind::PermissionDenied, reason));
                }
                _ => return Err(crate::wire::invalid()),
            }
            original.check(effective)?;
            transport::check_source(&self.source, source, effective)?;
            transport::check_configuration(&request, source[0], configuration, effective)?;
            transport::send_configuration_description(
                &mut original.channel,
                configuration,
                effective,
            )?;
            match ConfigurationReply::decode(
                &original.channel.receive(effective)?,
                &request,
                digest,
            )? {
                ConfigurationReply::Attached { context, remaining_input_ns, .. }
                    if context == original.context =>
                {
                    effective = original_deadline(started, remaining_input_ns)?.min(effective);
                }
                _ => return Err(crate::wire::invalid()),
            }
            original.original.revalidate(effective)?;
            live(&original.context, effective)?;
            transport::check_source(&self.source, source, effective)?;
            transport::check_configuration(&request, source[0], configuration, effective)
        });
        if let Err(error) = result {
            original.channel.poison();
            return Err(GraphFailure::retaining(original, Delivery::Unknown, error));
        }
        original.deadline = original.deadline.min(effective);
        self.original = Some(original);
        self.configuration.push(request);
        Ok(self)
    }
}

impl OutputBoundBootstrapGraph {
    /// Every accepted configuration binding, without issuing or release authority.
    pub fn configurations(&self) -> &[ConfigurationAttachment] {
        &self.configuration
    }

    /// Accepted binding DATA only; the original issuer must remain retained.
    pub fn configuration(&self) -> Option<&ConfigurationAttachment> {
        self.configuration.last()
    }
}
