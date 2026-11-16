// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Full actual command at the Host's second-image hold, and the parent's
//! one-shot selection. Both are DATA: actual original native resource/input
//! owners still authorize execution; neither frame creates a CPU/SDK grant.
use super::*;
use crate::{BirthKind, CommandSpec, Identity, Request as MemberRequest, Role};
mod query;
mod transport;
pub use query::{
    compiler_producing_command, compiler_query_command, compiler_transport_environment_name,
};
pub use transport::{
    TRANSPORT_MARKER, TRANSPORT_ORIGINALS, TRANSPORT_PURPOSE, TransportReply, TransportRequest,
};

#[derive(Clone, PartialEq, Eq)]
pub struct CompilerPrepared {
    pub root_attempt: [u8; 16],
    pub member_attempt: [u8; 16],
    pub coordinator_attempt: [u8; 16],
    pub identity: Identity,
    pub command: CommandSpec,
}
fn attempts(root: [u8; 16], member: [u8; 16], coordinator: [u8; 16]) -> io::Result<()> {
    if [root, member, coordinator].contains(&[0; 16])
        || root == member
        || root == coordinator
        || member == coordinator
    {
        return Err(invalid());
    }
    Ok(())
}
impl CompilerPrepared {
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        attempts(
            self.root_attempt,
            self.member_attempt,
            self.coordinator_attempt,
        )?;
        if self.identity.pid <= 1 || self.identity.birth == 0 {
            return Err(invalid());
        }
        let mut e = Encoder::new(89);
        e.number(1);
        e.0.extend(self.root_attempt);
        e.0.extend(self.member_attempt);
        e.0.extend(self.coordinator_attempt);
        e.number(self.identity.pid.into());
        e.number(self.identity.birth);
        e.number(match self.identity.birth_kind {
            BirthKind::MacosWallMicroseconds => 1,
            BirthKind::LinuxStartTicks => 2,
        });
        super::broker::command_write(&self.command, &mut e)?;
        e.finish()
    }
    pub fn decode(bytes: &[u8], request: &MemberRequest) -> io::Result<Self> {
        request.validate()?;
        let Role::CoordinatorCompiler(coordinator) = request.role else {
            return Err(invalid());
        };
        let mut d = header(bytes, 89)?;
        if d.number()? != 1 {
            return Err(invalid());
        }
        let root_attempt = d.array()?;
        let member_attempt = d.array()?;
        let coordinator_attempt = d.array()?;
        let pid = d.narrow()?;
        let birth = d.number()?;
        let birth_kind = match d.number()? {
            1 => BirthKind::MacosWallMicroseconds,
            2 => BirthKind::LinuxStartTicks,
            _ => return Err(invalid()),
        };
        let command = super::broker::command_read(&mut d)?;
        d.done()?;
        let value = Self {
            root_attempt,
            member_attempt,
            coordinator_attempt,
            identity: Identity {
                pid,
                birth,
                birth_kind,
            },
            command,
        };
        value.encode()?;
        if root_attempt != request.binding.root_attempt
            || member_attempt != request.member_attempt
            || coordinator_attempt != coordinator
            || value.command.program != request.command.program
            || value.command.arg0 != request.command.arg0
            || value.command.args != request.command.args
            || value.command.cwd != request.command.cwd
        {
            return Err(invalid());
        }
        Ok(value)
    }
    /// Digest of the complete observed command/identity, for equality only.
    #[cfg(feature = "client")]
    pub fn digest(&self) -> io::Result<[u8; 32]> {
        use sha2::Digest as _;
        Ok(sha2::Sha256::digest(self.encode()?).into())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CompilerSelection {
    pub root_attempt: [u8; 16],
    pub member_attempt: [u8; 16],
    pub coordinator_attempt: [u8; 16],
    pub prepared_sha256: [u8; 32],
}
impl CompilerSelection {
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        attempts(
            self.root_attempt,
            self.member_attempt,
            self.coordinator_attempt,
        )?;
        if self.prepared_sha256 == [0; 32] {
            return Err(invalid());
        }
        let mut e = Encoder::new(90);
        e.number(1);
        e.0.extend(self.root_attempt);
        e.0.extend(self.member_attempt);
        e.0.extend(self.coordinator_attempt);
        e.0.extend(self.prepared_sha256);
        e.finish()
    }
    pub fn decode(bytes: &[u8]) -> io::Result<Self> {
        let mut d = header(bytes, 90)?;
        if d.number()? != 1 {
            return Err(invalid());
        }
        let value = Self {
            root_attempt: d.array()?,
            member_attempt: d.array()?,
            coordinator_attempt: d.array()?,
            prepared_sha256: d.array()?,
        };
        d.done()?;
        value.encode()?;
        Ok(value)
    }
}

#[cfg(test)]
mod tests;
