// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Paged observations on the SAME original control owner. A complete census
//! means complete reported data, never action, source or retirement authority.

use std::collections::BTreeSet;
use std::io;
use std::time::Instant;

use super::{WorkloadControl, refused};
use crate::workload::host::census::{Entry, MAX_ENTRIES, Page, Reply, Request};

struct Pages {
    root_attempt: [u8; 16],
    invocation_sha256: [u8; 32],
    snapshot: [u8; 16],
    offset: u32,
    total: Option<u32>,
    seen: BTreeSet<[u8; 16]>,
    failed: bool,
}
impl Pages {
    fn request(&self) -> Request {
        Request {
            root_attempt: self.root_attempt,
            invocation_sha256: self.invocation_sha256,
            snapshot: self.snapshot,
            offset: self.offset,
        }
    }
    fn complete(&self) -> bool {
        !self.failed && self.total == Some(self.offset)
    }
    fn accept(&mut self, page: Page) -> io::Result<Vec<Entry>> {
        if self.failed
            || self.complete()
            || page.request != self.request()
            || self.total.is_some_and(|total| total != page.total)
            || page.total > MAX_ENTRIES
        {
            self.failed = true;
            return Err(refused());
        }
        // Retain each original attempt, including Unknown and None metrics.
        // Never shrink the denominator or turn missing fields into a zero.
        for entry in &page.entries {
            if !self.seen.insert(entry.member_attempt) {
                self.failed = true;
                return Err(refused());
            }
        }
        let next = self.offset.checked_add(page.entries.len() as u32).ok_or_else(refused)?;
        if next > page.total || (page.entries.is_empty() && page.total != 0) {
            self.failed = true;
            return Err(refused());
        }
        self.total = Some(page.total);
        self.offset = next;
        Ok(page.entries)
    }
}

/// Borrows the sole original reader/writer until its immutable snapshot is
/// complete or abandoned. It owns no FD transfer, work dispatch or CPU grant.
pub struct CensusSnapshot<'a> {
    control: &'a mut WorkloadControl,
    pages: Pages,
}
impl WorkloadControl {
    /// Query even after positive command Drained; bank/phase remain closed.
    /// The first accepted offset0 freezes an actual host-quiescent snapshot.
    /// Busy is a bound data refusal, never permission to start/retire work.
    pub fn census_snapshot(
        &mut self,
        snapshot: [u8; 16],
        deadline: Instant,
    ) -> io::Result<CensusSnapshot<'_>> {
        if self.failed || self.pending.is_some() || snapshot == [0; 16] {
            return Err(refused());
        }
        if Instant::now() >= deadline {
            return Err(io::ErrorKind::TimedOut.into());
        }
        Ok(CensusSnapshot {
            pages: Pages {
                root_attempt: self.root_attempt,
                invocation_sha256: self.invocation_sha256,
                snapshot,
                offset: 0,
                total: None,
                seen: BTreeSet::new(),
                failed: false,
            },
            control: self,
        })
    }
}
impl CensusSnapshot<'_> {
    pub fn total(&self) -> Option<u32> {
        self.pages.total
    }
    pub fn received(&self) -> u32 {
        self.pages.offset
    }
    pub fn complete(&self) -> bool {
        self.pages.complete()
    }

    /// Unknown/partial transport poisons the SAME control; no legacy reply,
    /// re-execution or offset advance is accepted. A valid Busy returns
    /// WouldBlock with the same offset/nonce, and a known refusal preserves
    /// PermissionDenied without fabricating an empty/complete population.
    pub fn next_page(&mut self, deadline: Instant) -> io::Result<Option<Vec<Entry>>> {
        if self.control.failed || self.pages.failed {
            return Err(refused());
        }
        if self.pages.complete() {
            return Ok(None);
        }
        if Instant::now() >= deadline {
            return Err(io::ErrorKind::TimedOut.into());
        }
        let request = self.pages.request();
        let exchanged = (|| {
            self.control.host.validate(deadline)?;
            self.control.channel.send(&request.encode()?, deadline)?;
            let reply = Reply::decode(&self.control.channel.receive(deadline)?, &request)?;
            self.control.host.validate(deadline)?;
            Ok(reply)
        })();
        let reply = match exchanged {
            Ok(reply) => reply,
            Err(error) => {
                self.control.failed = true;
                self.pages.failed = true;
                return Err(error);
            }
        };
        match reply {
            Reply::Page(page) => match self.pages.accept(page) {
                Ok(entries) => Ok(Some(entries)),
                Err(error) => {
                    self.control.failed = true;
                    self.pages.failed = true;
                    Err(error)
                }
            },
            Reply::Busy { .. } => Err(io::ErrorKind::WouldBlock.into()),
            Reply::Refused { reason, .. } => {
                self.pages.failed = true;
                Err(io::Error::new(io::ErrorKind::PermissionDenied, reason))
            }
        }
    }
}

#[cfg(test)]
mod tests;
