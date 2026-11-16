// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

use std::io;

use crate::wire::invalid;
use crate::*;

fn os_bytes(bytes: &[u8], nonempty: bool) -> bool {
    bytes.len() <= MAX_FIELD && (!nonempty || !bytes.is_empty()) && !bytes.contains(&0)
}
fn absolute(bytes: &[u8]) -> bool {
    os_bytes(bytes, true) && bytes.starts_with(b"/")
}

fn linker_loan_shape(request: &Request, loan: Loan) -> bool {
    let args = &request.command.args;
    loan.parent_attempt != [0; 16]
        && loan.parent_attempt != request.binding.root_attempt
        && loan.parent_attempt != request.member_attempt
        && loan.nonce != [0; 16]
        && request.delegations.cpu.is_some()
        && matches!(request.delegations.gnu, GnuTransport::None)
        && request.delegations.fences.is_empty()
        && args.len() >= 5
        && args[0] == b"-flavor"
        && args[1] == b"darwin"
        && args[args.len() - 3] == b"--threads=1"
        && args[args.len() - 2] == b"--thinlto-jobs=1"
        && args[args.len() - 1] == b"--read-workers=0"
        && !args.iter().any(|arg| arg.starts_with(b"@"))
}
impl Request {
    /// Validate syntax only; every descriptor and producer still needs native authentication.
    pub fn validate(&self) -> io::Result<()> {
        self.validate_profile(false)
    }
    // Selected only by the distinct paired50/v2 codec. Ordinary Request and
    // every existing role6 exchange retain the original closed env6 profile.
    pub(crate) fn validate_paired_query(&self) -> io::Result<()> {
        if self.role != Role::WorkloadQuery {
            return Err(invalid());
        }
        self.validate_profile(true)
    }
    fn validate_profile(&self, paired_query: bool) -> io::Result<()> {
        self.binding.validate()?;
        if self.member_attempt == [0; 16]
            || self.member_attempt == self.binding.root_attempt
            || self.timeout_ns == Some(0)
        {
            return Err(invalid());
        }
        let c = &self.command;
        if !absolute(&c.program)
            || !absolute(&c.cwd)
            || c.args.len() > MAX_ITEMS
            || c.environment.len() > MAX_ITEMS
            || c.arg0.as_ref().is_some_and(|v| !os_bytes(v, true))
            || c.args.iter().any(|v| !os_bytes(v, false))
        {
            return Err(invalid());
        }
        let mut names = std::collections::BTreeSet::new();
        for (key, value) in &c.environment {
            if !os_bytes(key, true)
                || key.contains(&b'=')
                || !os_bytes(value, false)
                || !names.insert(key)
            {
                return Err(invalid());
            }
        }
        let ds = &self.delegations;
        if ds.fences.len() > MAX_FENCES {
            return Err(invalid());
        }
        let mut descriptors = ds.fences.clone();
        if let Some(cpu) = ds.cpu {
            descriptors.push(cpu);
        }
        match &ds.gnu {
            GnuTransport::None => {}
            GnuTransport::NumericPipe { read, write } => descriptors.extend([*read, *write]),
            GnuTransport::NamedFifo {
                locator,
                inode,
                read,
                write,
                ..
            } => {
                if !absolute(locator)
                    || *inode == 0
                    || std::str::from_utf8(locator)
                        .map_or(true, |v| v.chars().any(char::is_whitespace))
                {
                    return Err(invalid());
                }
                descriptors.extend([*read, *write]);
            }
        }
        let mut sources = std::collections::BTreeSet::new();
        let mut targets = std::collections::BTreeSet::new();
        for d in descriptors {
            if d.source < 5
                || d.target < 3
                || d.source > i32::MAX as u32
                || d.target > i32::MAX as u32
                || !sources.insert(d.source)
                || !targets.insert(d.target)
            {
                return Err(invalid());
            }
        }
        match self.role {
            Role::ResolverQuery => crate::resolver::validate_member(self)?,
            Role::WorkloadQuery if paired_query => {
                crate::paired_qualification::query::validate_member(self)?
            }
            Role::WorkloadQuery => crate::workload::host::validate_query_member(self)?,
            Role::WorkloadProduced => crate::workload::host::produced::validate_member(self)?,
            Role::CoordinatorCompiler(coordinator) => {
                if coordinator == [0; 16]
                    || coordinator == self.binding.root_attempt
                    || coordinator == self.member_attempt
                    // SAME native workload compiler layout: SDK5, CPU6,
                    // Store7. CPU5 remains the separate nondelegating linker.
                    || ds.cpu.is_none_or(|cpu| cpu.target != 6)
                    || !ds.fences.is_empty()
                    || self.timeout_ns.is_none()
                    || c.arg0.is_some()
                    || c.args.iter().any(|arg| arg.starts_with(b"@"))
                    || c.environment.iter().any(|(name, _)| {
                        matches!(
                            name.as_slice(),
                            b"RUSTC_WRAPPER" | b"RUSTC_WORKSPACE_WRAPPER"
                        )
                    })
                {
                    return Err(invalid());
                }
            }
            Role::MachOLinker(loan) if !linker_loan_shape(self, loan) => {
                return Err(invalid());
            }
            Role::Compile if ds.cpu.is_none() || matches!(ds.gnu, GnuTransport::None) => {
                return Err(invalid());
            }
            Role::MetadataVersion
                if c.args.len() != 1 || !matches!(c.args[0].as_slice(), b"-vV" | b"--version") =>
            {
                return Err(invalid());
            }
            Role::SealedMetadata => crate::sealed_metadata::validate_member(self)?,
            Role::MetadataProbe
                if c.args.len() != 1
                    || !matches!(
                        c.args[0].as_slice(),
                        b"--print=sysroot" | b"--print=target-list"
                    )
                    || ds.cpu.is_none()
                    || !matches!(ds.gnu, GnuTransport::None)
                    || !ds.fences.is_empty()
                    || !self.timeout_ns.is_some_and(|value| value <= 8_000_000_000) =>
            {
                return Err(invalid());
            }
            _ => {}
        }
        Ok(())
    }
}

impl JobBinding {
    /// Validate private routing syntax, never native custody or permission.
    pub fn validate(&self) -> io::Result<()> {
        validate_session(&self.session)?;
        if self.root_attempt == [0; 16] || self.capability == [0; 32] {
            return Err(invalid());
        }
        Ok(())
    }
}

/// A session is aterm's tab ID: `t` and 10 lower-case Crockford base32 characters (`0-9`, `a-z`
/// without `i`, `l`, `o`, `u`), or the earlier form, `s-` and 1 to 62 lower-case hex digits.
pub(crate) fn validate_session(value: &str) -> io::Result<()> {
    if let Some(tab) = value.strip_prefix('t') {
        let crockford = |c: u8| c.is_ascii_digit() || (c.is_ascii_lowercase() && !b"ilou".contains(&c));
        if tab.len() == 10 && tab.bytes().all(crockford) {
            return Ok(());
        }
        return Err(invalid());
    }
    let session = value.strip_prefix("s-").ok_or_else(invalid)?;
    if session.is_empty()
        || session.len() > 62
        || !session
            .bytes()
            .all(|c| c.is_ascii_digit() || (b'a'..=b'f').contains(&c))
    {
        return Err(invalid());
    }
    Ok(())
}
