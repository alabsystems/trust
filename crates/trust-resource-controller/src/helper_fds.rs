// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

use std::ffi::{OsStr, OsString};
use std::io;

use crate::wire::invalid;
use crate::{CONTROL_FD, Delegations, GnuTransport, PRODUCER_FD};

fn number(arg: &OsStr, prefix: &str) -> io::Result<u32> {
    let text = arg.to_str().and_then(|v| v.strip_prefix(prefix)).ok_or_else(invalid)?;
    let value: u32 = text.parse().map_err(|_| invalid())?;
    if value.to_string() != text {
        return Err(invalid());
    }
    Ok(value)
}

/// Actual inherited socket-number locators, never resource authority. Production
/// uses held source numbers and child-only CLOEXEC clearing, avoiding dup2 onto
/// a runtime's private exec-status descriptors or a parent's live FD table.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct HelperFds {
    pub control: u32,
    pub producer: u32,
}
impl Default for HelperFds {
    fn default() -> Self {
        Self { control: CONTROL_FD, producer: PRODUCER_FD }
    }
}
impl HelperFds {
    pub fn validate(self) -> io::Result<()> {
        if self.control < 3
            || self.producer < 3
            || self.control == self.producer
            || self.control > i32::MAX as u32
            || self.producer > i32::MAX as u32
        {
            return Err(invalid());
        }
        Ok(())
    }
    /// Recognize only this private entry. Invalid recognized shapes refuse,
    /// while unrelated CLI entries return None without changing their routing.
    pub fn parse(args: &[OsString]) -> io::Result<Option<Self>> {
        Self::parse_entry(args, "__resource-member-v3")
    }
    /// The explicit owning-wait route never silently uses a legacy helper.
    pub fn parse_accounted(args: &[OsString]) -> io::Result<Option<Self>> {
        Self::parse_entry(args, crate::accounting::HELPER_ENTRY)
    }
    fn parse_entry(args: &[OsString], entry: &str) -> io::Result<Option<Self>> {
        if args.first().map(OsString::as_os_str) != Some(OsStr::new(entry)) {
            return Ok(None);
        }
        if args.len() != 4 || args[1] != "--protocol=3" {
            return Err(invalid());
        }
        let fds = Self {
            control: number(&args[2], "--control-fd=")?,
            producer: number(&args[3], "--producer-fd=")?,
        };
        fds.validate()?;
        Ok(Some(fds))
    }
    pub fn arguments(self) -> io::Result<Vec<OsString>> {
        self.arguments_entry("__resource-member-v3")
    }
    pub fn accounted_arguments(self) -> io::Result<Vec<OsString>> {
        self.arguments_entry(crate::accounting::HELPER_ENTRY)
    }
    fn arguments_entry(self, entry: &str) -> io::Result<Vec<OsString>> {
        self.validate()?;
        Ok(vec![
            entry.into(),
            "--protocol=3".into(),
            format!("--control-fd={}", self.control).into(),
            format!("--producer-fd={}", self.producer).into(),
        ])
    }
    /// Check BEFORE descriptor duplication, which could reuse an advertised
    /// closed slot. Target numbers belong to a separate namespace.
    pub fn validate_delegations(self, delegations: &Delegations) -> io::Result<()> {
        self.validate()?;
        let mut sources = delegations.fences.iter().map(|d| d.source).collect::<Vec<_>>();
        if let Some(cpu) = delegations.cpu {
            sources.push(cpu.source);
        }
        match delegations.gnu {
            GnuTransport::None => {}
            GnuTransport::NumericPipe { read, write }
            | GnuTransport::NamedFifo { read, write, .. } => {
                sources.extend([read.source, write.source])
            }
        }
        if sources.into_iter().any(|fd| fd == self.control || fd == self.producer) {
            return Err(invalid());
        }
        Ok(())
    }
}

/// The existing native helper with its independently selected original store.
/// All fields are locators only; actual ancestor/image/backing and resource
/// custody still need authentication. Legacy helper arguments stay unchanged.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct WorkloadHelperFds {
    pub transport: HelperFds,
    pub store: u32,
}
impl WorkloadHelperFds {
    pub const ENTRY: &str = "__resource-workload-member-v1";

    pub fn validate(self) -> io::Result<()> {
        self.transport.validate()?;
        if self.store < 6
            || self.store > i32::MAX as u32
            || self.store == self.transport.control
            || self.store == self.transport.producer
        {
            return Err(invalid());
        }
        Ok(())
    }
    pub fn parse(args: &[OsString]) -> io::Result<Option<Self>> {
        if args.first().map(OsString::as_os_str) != Some(OsStr::new(Self::ENTRY)) {
            return Ok(None);
        }
        if args.len() != 5 {
            return Err(invalid());
        }
        let value = Self {
            transport: HelperFds::parse_entry(&args[..4], Self::ENTRY)?.ok_or_else(invalid)?,
            store: number(&args[4], "--store-fd=")?,
        };
        value.validate()?;
        Ok(Some(value))
    }
    pub fn arguments(self) -> io::Result<Vec<OsString>> {
        self.validate()?;
        let mut args = self.transport.arguments_entry(Self::ENTRY)?;
        args.push(format!("--store-fd={}", self.store).into());
        Ok(args)
    }
    /// Check before duplicating/opening anything: an invalid missing source
    /// must never become the newly allocated discovery or socket descriptor.
    pub fn validate_delegations(self, delegations: &Delegations) -> io::Result<()> {
        self.validate()?;
        self.transport.validate_delegations(delegations)?;
        let mut sources = delegations.fences.iter().map(|fd| fd.source).collect::<Vec<_>>();
        sources.extend(delegations.cpu.iter().map(|fd| fd.source));
        match delegations.gnu {
            GnuTransport::None => {}
            GnuTransport::NumericPipe { read, write }
            | GnuTransport::NamedFifo { read, write, .. } => {
                sources.extend([read.source, write.source]);
            }
        }
        if sources.contains(&self.store) {
            return Err(invalid());
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Descriptor;

    #[test]
    fn original_store_entry_is_closed_and_legacy_arguments_stay_distinct() {
        let fds =
            WorkloadHelperFds { transport: HelperFds { control: 11, producer: 12 }, store: 13 };
        let args = fds.arguments().unwrap();
        assert_eq!(WorkloadHelperFds::parse(&args).unwrap(), Some(fds));
        assert!(HelperFds::parse(&args).unwrap().is_none());
        assert!(HelperFds::parse_accounted(&args).unwrap().is_none());
        for args in
            [fds.transport.arguments().unwrap(), fds.transport.accounted_arguments().unwrap()]
        {
            assert!(WorkloadHelperFds::parse(&args).unwrap().is_none());
        }
        for store in [0, 1, 2, 3, 4, 5, 11, 12, u32::MAX] {
            assert!(WorkloadHelperFds { store, ..fds }.arguments().is_err());
        }
        for value in ["--store-fd=013", "--store-fd=+13", "--store-fd=-1", "--other=13"] {
            let mut bad = args.clone();
            bad[4] = value.into();
            assert!(WorkloadHelperFds::parse(&bad).is_err());
        }
        let mut bad = args.clone();
        bad.push("extra".into());
        assert!(WorkloadHelperFds::parse(&bad).is_err());
    }

    #[test]
    fn original_store_must_be_disjoint_from_every_advertised_source() {
        let fds =
            WorkloadHelperFds { transport: HelperFds { control: 11, producer: 12 }, store: 13 };
        let mut rights = Delegations {
            cpu: Some(Descriptor { source: 14, target: 6 }),
            gnu: GnuTransport::None,
            fences: vec![],
        };
        fds.validate_delegations(&rights).unwrap();
        rights.cpu.as_mut().unwrap().source = 13;
        assert!(fds.validate_delegations(&rights).is_err());
        rights.cpu.as_mut().unwrap().source = 14;
        rights.fences.push(Descriptor { source: 13, target: 8 });
        assert!(fds.validate_delegations(&rights).is_err());
        rights.fences.clear();
        rights.gnu = GnuTransport::NumericPipe {
            read: Descriptor { source: 15, target: 3 },
            write: Descriptor { source: 13, target: 4 },
        };
        assert!(fds.validate_delegations(&rights).is_err());
    }
}
