//! Trust: the actual completed producer lends its original input descriptions.
//! This does not enable the session entry. A qualified Bootstrap Root recipe
//! and authentic original-root membership are still required before Steps.

use std::io;
use std::os::fd::{AsRawFd, BorrowedFd};
use std::os::unix::ffi::OsStrExt;
use std::sync::Arc;
use std::time::Instant;

use build_helper::trust_repo_lock::management::WithheldLease;
use trust_resource_controller::client::runtime_input_retention::RetainedRuntimeInputs;
use trust_resource_controller::client::{CallError, Client, Delivery};
use trust_resource_controller::runtime_input_retention::{Input, Kind, Request, SupportQuery};
use trust_resource_controller::{Context, ContextQuery, FileIdentity};

use super::{
    CommandOwnership, CommandState, CompletedRuntime, OriginalCompletedInputs, RetentionBinding,
};

impl CommandOwnership {
    /// Negotiate as the actual eligible caller BEFORE costly normal Steps.
    /// Support is only a prerequisite observation. This consumes only the SAME
    /// owned lease into durable exclusion; it grants no execution or release.
    /// A borrowed ordinary exec cannot promote its ancestor's holder.
    pub(crate) fn prepare_input_retention(
        &self,
        client: &Client,
        query: ContextQuery,
        deadline: Instant,
    ) -> Result<Arc<WithheldLease>, String> {
        {
            let original = self.lease.lock().map_err(|_| "native command ownership is poisoned")?;
            Self::check_retention_candidate(&original)?;
        }
        let binding = query.binding.clone();
        let supported = client
            .runtime_input_support(&SupportQuery { query }, deadline)
            .map_err(|error| error.to_string())?;
        let mut original = self.lease.lock().map_err(|_| "native command ownership is poisoned")?;
        if Instant::now() >= deadline {
            return Err("runtime input support crossed the original deadline".into());
        }
        Self::check_retention_candidate(&original)?;
        if Instant::now() >= deadline {
            return Err("original ownership recheck crossed the support deadline".into());
        }
        let scope_original = if matches!(&*original, CommandState::Original(_)) {
            Self::withhold_original_locked(&mut original)?
        } else {
            let CommandState::Withheld { lease, .. } = &*original else { unreachable!() };
            Arc::clone(lease)
        };
        let CommandState::Withheld { retention, .. } = &mut *original else { unreachable!() };
        // Only this successful live negotiation attaches retention observations.
        // An engine's earlier withholding is exclusion, never retention support.
        *retention =
            Some(RetentionBinding { context: supported.observation().context.clone(), binding });
        if Instant::now() >= deadline {
            return Err("durable withholding crossed the original deadline; retained".into());
        }
        Ok(scope_original)
    }

    fn check_retention_candidate(original: &CommandState) -> Result<(), String> {
        match original {
            CommandState::Original(lease) if !lease.is_borrowed() => {
                lease.check_current().map_err(|e| e.to_string())
            }
            CommandState::Withheld { lease, retention: None, offered: false } => {
                lease.check_current().map_err(|e| e.to_string())
            }
            _ => Err("runtime retention requires the original unbound owned custody".into()),
        }
    }

    fn retained_context(&self) -> io::Result<Context> {
        let original =
            self.lease.lock().map_err(|_| io::Error::other("native ownership poisoned"))?;
        match &*original {
            CommandState::Withheld { lease, retention: Some(binding), .. } => {
                lease.check_current()?;
                Ok(binding.context.clone())
            }
            _ => Err(io::Error::new(
                io::ErrorKind::PermissionDenied,
                "runtime inputs require actual owned durable withholding",
            )),
        }
    }

    fn begin_input_transfer(&self, query: &ContextQuery) -> io::Result<()> {
        let mut original =
            self.lease.lock().map_err(|_| io::Error::other("native ownership poisoned"))?;
        match &mut *original {
            CommandState::Withheld { lease, retention: Some(binding), offered }
                if !*offered && binding.binding == query.binding =>
            {
                lease.check_current()?;
                // Consume BEFORE connecting, never replay uncertain delivery.
                // Even a subsequent before-request refusal requires a new
                // original run rather than guessing whether input escaped.
                *offered = true;
                Ok(())
            }
            _ => Err(io::Error::new(
                io::ErrorKind::PermissionDenied,
                "runtime input transfer already used or differs from original support",
            )),
        }
    }
}

/// A connected observation owner borrowing the SAME completed producer. Its
/// Drop closes only the observation channel, never releases manager/Host debt.
/// No ACK, EOF, record or directory can construct this value or completion.
pub(crate) struct RetainedCompletedInputs<'a> {
    retained: RetainedRuntimeInputs,
    completed: &'a CompletedRuntime,
}

impl RetainedCompletedInputs<'_> {
    pub(crate) fn check(&self, deadline: Instant) -> io::Result<()> {
        self.retained.revalidate(deadline)?;
        self.completed.check().map_err(io::Error::other)?;
        if self.completed.state.ownership.command.retained_context()?
            != self.retained.observation().context
        {
            return Err(io::Error::new(io::ErrorKind::PermissionDenied, "original context moved"));
        }
        time(deadline)
    }
}

impl CompletedRuntime {
    /// Offer the complete originals once, retaining this actual live producer.
    /// Missing prior owned withholding refuses BEFORE any delivery. Unknown
    /// transfer preserves durable exclusion; it never retries or releases.
    pub(crate) fn retain_original_inputs(
        &self,
        client: &Client,
        query: ContextQuery,
        transfer: [u8; 16],
        deadline: Instant,
    ) -> Result<RetainedCompletedInputs<'_>, CallError> {
        let before = |error| CallError { delivery: Delivery::BeforeRequest, error };
        time(deadline).map_err(before)?;
        let context = self.state.ownership.command.retained_context().map_err(before)?;
        if context.session != query.binding.session
            || context.root_attempt != query.binding.root_attempt
        {
            return Err(before(io::Error::new(
                io::ErrorKind::PermissionDenied,
                "retention query differs from the actual supported original root",
            )));
        }
        let originals =
            self.original_input_descriptions().map_err(io::Error::other).map_err(before)?;
        let (request, descriptors) = originals.request(query, transfer).map_err(before)?;
        time(deadline).map_err(before)?;
        self.state.ownership.command.begin_input_transfer(&request.query).map_err(before)?;
        let retained = client.retain_runtime_inputs(&request, &descriptors, deadline)?;
        let owner = RetainedCompletedInputs { retained, completed: self };
        owner.check(deadline).map_err(|error| CallError { delivery: Delivery::Unknown, error })?;
        Ok(owner)
    }
}

impl<'a> OriginalCompletedInputs<'a> {
    fn request(
        &self,
        query: ContextQuery,
        transfer: [u8; 16],
    ) -> io::Result<(Request, Vec<BorrowedFd<'a>>)> {
        input_request(&self.runtime, &self.output, query, transfer)
    }
}

// Mechanical metadata from the actual borrowed owners, never completion.
// Kept separate so the real immutable-input actor can exercise its COMPLETE
// 171-description transfer without manufacturing a CompletedRuntime or Host.
fn input_request<'a>(
    runtime: &crate::utils::retained_compiler_fixture::OriginalRuntimeDescriptions<'a>,
    output: &build_helper::trust_output_lock::OriginalOutputDescriptions<'a>,
    query: ContextQuery,
    transfer: [u8; 16],
) -> io::Result<(Request, Vec<BorrowedFd<'a>>)> {
    let count = runtime.count().checked_add(2).ok_or(io::ErrorKind::InvalidData)?;
    if count > trust_resource_controller::runtime_input_retention::MAX_INPUTS {
        return Err(io::ErrorKind::InvalidData.into());
    }
    let mut inputs = Vec::with_capacity(count);
    let mut descriptors = Vec::with_capacity(count);
    inputs.push(observe(
        Kind::RuntimeRoot,
        &[],
        runtime.root.as_os_str().as_bytes(),
        runtime.root_descriptor,
    )?);
    descriptors.push(runtime.root_descriptor);
    for entry in &runtime.entries {
        let mut input = observe(
            if entry.directory { Kind::RuntimeDirectory } else { Kind::RuntimeFile },
            entry.logical.as_os_str().as_bytes(),
            entry.target.as_os_str().as_bytes(),
            entry.descriptor,
        )?;
        input.alias = entry.alias.map(|p| p.as_os_str().as_bytes().to_vec());
        input.size = entry.bytes;
        input.sha256 = entry.sha256.map(digest).transpose()?;
        input.executable = entry.executable;
        inputs.push(input);
        descriptors.push(entry.descriptor);
    }
    inputs.push(observe(
        Kind::OutputRoot,
        &[],
        output.root().as_os_str().as_bytes(),
        output.directory(),
    )?);
    descriptors.push(output.directory());
    inputs.push(observe(
        Kind::OutputLock,
        b"lock",
        output.root().join("lock").as_os_str().as_bytes(),
        output.lock(),
    )?);
    descriptors.push(output.lock());
    let request = Request { query, transfer, inputs };
    // Encoding enforces the unchanged frame budget BEFORE any delivery.
    // Keep duplicate backing for explicit aliases, never inode-deduplicate.
    request.encode()?;
    trust_resource_controller::runtime_input_retention::transport::check_inputs(
        &request,
        &descriptors,
    )?;
    Ok((request, descriptors))
}

fn observe(kind: Kind, logical: &[u8], target: &[u8], fd: BorrowedFd<'_>) -> io::Result<Input> {
    let mut stat = std::mem::MaybeUninit::<libc::stat>::uninit();
    // SAFETY: observe the actual borrowed original without changing its cursor,
    // flags or locking state. Never reopen a name to reconstruct the owner.
    if unsafe { libc::fstat(fd.as_raw_fd(), stat.as_mut_ptr()) } != 0 {
        return Err(io::Error::last_os_error());
    }
    let stat = unsafe { stat.assume_init() };
    Ok(Input {
        kind,
        logical_path: logical.to_vec(),
        target: target.to_vec(),
        alias: None,
        backing: FileIdentity { device: stat.st_dev as u64, inode: stat.st_ino as u64 },
        size: None,
        sha256: None,
        executable: false,
    })
}

fn digest(value: &str) -> io::Result<[u8; 32]> {
    if value.len() != 64 {
        return Err(io::ErrorKind::InvalidData.into());
    }
    let mut hash = [0; 32];
    for (index, pair) in value.as_bytes().chunks_exact(2).enumerate() {
        let hex = |byte| match byte {
            b'0'..=b'9' => Ok(byte - b'0'),
            b'a'..=b'f' => Ok(byte - b'a' + 10),
            _ => Err(io::Error::from(io::ErrorKind::InvalidData)),
        };
        hash[index] = (hex(pair[0])? << 4) | hex(pair[1])?;
    }
    Ok(hash)
}

fn time(deadline: Instant) -> io::Result<()> {
    if Instant::now() >= deadline { Err(io::ErrorKind::TimedOut.into()) } else { Ok(()) }
}

#[cfg(test)]
mod tests;
