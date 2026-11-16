//! Fresh native custody must precede the issuer's first configuration read.
use std::io;
use std::os::fd::BorrowedFd;
use std::time::Instant;

use sha2::{Digest as _, Sha256};

use super::{
    GraphFailure, OutputBoundBootstrapGraph, SourceBoundBootstrapGraph, bounded, original_deadline,
};
use crate::FileIdentity;
use crate::bootstrap_graph::{MaterializationPreparation, MaterializationReply, transport};
use crate::client::Delivery;

pub(super) struct PreparedContents {
    request: MaterializationPreparation,
    contents: FileIdentity,
}
impl PreparedContents {
    pub(super) fn check(
        &self,
        source: FileIdentity,
        output: Option<&crate::bootstrap_graph::OutputAttachment>,
    ) -> io::Result<()> {
        if self.contents.inode == 0
            || self.contents == source
            || output
                .is_some_and(|output| self.contents == output.root || self.contents == output.lock)
        {
            return Err(crate::wire::invalid());
        }
        Ok(())
    }
}

impl SourceBoundBootstrapGraph {
    /// Native preparation binding DATA, never a producer or seed constructor.
    pub fn materialization(&self) -> Option<&MaterializationPreparation> {
        self.materialization.as_ref().map(|value| &value.request)
    }
    /// Accepted resident observation DATA only; no directory is opened/adopted.
    pub fn materialization_contents(&self) -> Option<FileIdentity> {
        self.materialization.as_ref().map(|value| value.contents)
    }
    /// Current restrictive endpoint. Subsequent input issuance must use this
    /// minimum; it never renews the original Root's resource epoch.
    pub fn original_deadline(&self) -> Instant {
        self.original.as_ref().expect("private source-bound graph").deadline
    }

    /// Establish fresh workspace/cache custody in the original native Job
    /// before issuing/capturing configuration or reading source contents.
    ///
    /// # Safety
    /// `source` must borrow the same actual original SourceOffer retained by
    /// the caller before this call and through native graph retirement. Its
    /// owner bookends this whole exchange, including failure/unwind. `deadline`
    /// cannot exceed that actual issuer's endpoint. After success the caller
    /// must use `original_deadline()` for subsequent input issuance/reads;
    /// the authenticated native bound may conservatively be earlier.
    pub unsafe fn prepare_materialization(
        mut self,
        source: &[BorrowedFd<'_>; 4],
        deadline: Instant,
    ) -> Result<Self, GraphFailure> {
        let started = Instant::now();
        let mut original = self.original.take().expect("private source-bound graph");
        let request = (|| {
            bounded(original.deadline, deadline)?;
            original.queries.enrollment_allowed()?;
            if self.materialization.is_some() || !self.configuration.is_empty() {
                return Err(crate::wire::invalid());
            }
            let remaining =
                deadline.checked_duration_since(started).ok_or(io::ErrorKind::TimedOut)?;
            let request = MaterializationPreparation {
                key: original.request.key.clone(),
                input_remaining_ns: remaining
                    .as_nanos()
                    .try_into()
                    .map_err(|_| crate::wire::invalid())?,
            };
            request.validate()?;
            transport::check_source(&self.source, source, deadline)?;
            original.check(deadline)?;
            Ok(request)
        })();
        let request = match request {
            Ok(request) => request,
            Err(error) => {
                return Err(GraphFailure::retaining(original, Delivery::BeforeRequest, error));
            }
        };
        let digest: [u8; 32] =
            Sha256::digest(request.binding_preimage().expect("same preparation request")).into();
        let prepared = (|| {
            original.channel.send(&request.encode()?, deadline)?;
            let (remaining_input_ns, contents_directory) = match MaterializationReply::decode(
                &original.channel.receive(deadline)?,
                &request,
                digest,
            )? {
                MaterializationReply::Prepared {
                    context,
                    remaining_input_ns,
                    contents_directory,
                    ..
                } if *context == original.context => (remaining_input_ns, contents_directory),
                MaterializationReply::Refused { reason, .. } => {
                    return Err(io::Error::new(io::ErrorKind::PermissionDenied, reason));
                }
                _ => return Err(crate::wire::invalid()),
            };
            // The sender's pre-request anchor precedes the Host's remaining
            // capture. This acknowledgement can only shorten its actual bound.
            let accepted = original_deadline(started, remaining_input_ns)?.min(deadline);
            original.check(accepted)?;
            transport::check_source(&self.source, source, accepted)?;
            let contents =
                PreparedContents { request: request.clone(), contents: contents_directory };
            contents.check(self.source.source_directory, None)?;
            Ok((accepted, contents))
        })();
        let (accepted, contents) = match prepared {
            Ok(accepted) => accepted,
            Err(error) => {
                original.channel.poison();
                return Err(GraphFailure::retaining(original, Delivery::Unknown, error));
            }
        };
        original.deadline = original.deadline.min(accepted);
        self.original = Some(original);
        self.materialization = Some(contents);
        Ok(self)
    }
}

impl OutputBoundBootstrapGraph {
    pub fn materialization(&self) -> Option<&MaterializationPreparation> {
        self.materialization.as_ref().map(|value| &value.request)
    }
    /// Exact accepted DATA, retained across output attachment; not a producer.
    pub fn materialization_contents(&self) -> Option<FileIdentity> {
        self.materialization.as_ref().map(|value| value.contents)
    }
}

#[cfg(test)]
mod tests;
