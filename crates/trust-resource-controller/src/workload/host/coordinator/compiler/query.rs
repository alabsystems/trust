// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Shared closed-query construction DATA. Callers supply values from actual
//! original native owners; this function creates no admission, FD, SDK or proof
//! authority. The complete resulting environment remains semantic input.
use super::*;
use crate::JobBinding;

/// Exact names replaced/removed by the native installation. This is NEVER an
/// equivalence exemption: consumers must compare/hash the whole final command.
pub fn compiler_transport_environment_name(name: &[u8]) -> bool {
    matches!(
        name,
        b"ATERM_RESOURCE_JOB_V3"
            | b"ATERM_RESOURCE_INSPECTOR"
            | b"ATERM_SESSION_ID"
            | b"ATERM_PARENT_SESSION_ID"
            | b"PARENT_SESSION_ID"
            | b"ATERM_SDK_LEASE_V3"
            | b"ATERM_WORKLOAD_CPU_FDS_V1"
            | b"ATERM_WORKLOAD_HOST_STORE_FD_V1"
            | b"ATERM_WORKLOAD_HOST_CONTROL_FDS_V1"
            | b"TRUST_CPU_HANDOFF"
            | b"TRUST_CPU_IMPLICIT_FD"
            | b"CARGO_JOBSERVER_HANDOFF"
            | b"TRUST_JOBSERVER_HANDOFF"
            | b"BUILD_SLOT_FENCE_FDS"
            | b"BUILD_SLOT_CPU_LEASE_FD"
            | b"BUILD_SLOT_CPU_PROTOCOL"
            | b"BUILD_SLOT_HELD"
            | b"MAKEFLAGS"
            | b"MFLAGS"
            | b"CARGO_MAKEFLAGS"
    )
}
fn hex(bytes: &[u8]) -> String {
    const DIGITS: &[u8; 16] = b"0123456789abcdef";
    let mut result = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        result.push(char::from(DIGITS[(byte >> 4) as usize]));
        result.push(char::from(DIGITS[(byte & 15) as usize]));
    }
    result
}
/// Project the ONE current native query layout: original SDK5, CPU6, Store7,
/// no GNU/implicit handoff and no producing flags. The workload original
/// adopter consumes CPU_SET_FDS, so this does not install implicit adoption.
/// The authenticated owning receiver
/// must independently check those real originals and actual held target first.
/// `inspector` comes from the actual pinned custodian; `runtime_environment`
/// comes from the SAME held compiler. Neither may come from the reported env.
pub fn compiler_query_command(
    binding: &JobBinding,
    original: &CommandSpec,
    inspector: &[u8],
    runtime_environment: &[(Vec<u8>, Vec<u8>)],
) -> io::Result<CommandSpec> {
    crate::resolver::classify_resolver_query(&original.args)?;
    original_command(binding, original, inspector, runtime_environment)
}
/// One currently selected numeric-GNU producing layout. This only constructs
/// command DATA: the caller must hold its genuine original transport witness,
/// native scope and independent source/SDK/command selection before binding GO.
pub fn compiler_producing_command(
    binding: &JobBinding,
    original: &CommandSpec,
    inspector: &[u8],
    runtime_environment: &[(Vec<u8>, Vec<u8>)],
    advertisement: &[u8],
) -> io::Result<CommandSpec> {
    if !matches!(original.args.as_slice(),[worker,subgroups,..]
        if worker==b"--resource-worker-v3" && subgroups==b"--resource-subgroups-v3")
        || advertisement.is_empty()
        || advertisement.len() > 4096
        || advertisement.contains(&0)
    {
        return Err(invalid());
    }
    let mut command = original_command(binding, original, inspector, runtime_environment)?;
    let mut environment = command
        .environment
        .into_iter()
        .collect::<std::collections::BTreeMap<_, _>>();
    for name in [b"MAKEFLAGS".as_slice(), b"MFLAGS", b"CARGO_MAKEFLAGS"] {
        environment.insert(
            name.to_vec(),
            b"-j --jobserver-fds=8,9 --jobserver-auth=8,9".to_vec(),
        );
    }
    environment.insert(b"CARGO_JOBSERVER_HANDOFF".to_vec(), advertisement.to_vec());
    command.environment = environment.into_iter().collect();
    super::super::broker::command_write(&command, &mut Encoder::new(0))?;
    Ok(command)
}
fn original_command(
    binding: &JobBinding,
    original: &CommandSpec,
    inspector: &[u8],
    runtime_environment: &[(Vec<u8>, Vec<u8>)],
) -> io::Result<CommandSpec> {
    binding.validate()?;
    if original.arg0.is_some()
        || !inspector.starts_with(b"/")
        || inspector.contains(&0)
        || inspector.len() > crate::MAX_FIELD
        || runtime_environment.len() > 1
    {
        return Err(invalid());
    }
    // Bound/validate the borrowed command before cloning any caller bytes.
    let mut validation = Encoder::new(0);
    super::super::broker::command_write(original, &mut validation)?;
    drop(validation);
    let mut environment = std::collections::BTreeMap::new();
    for (key, value) in &original.environment {
        if super::super::super::produced::loader_override_name(key)
            || (super::super::super::produced::protected_environment_name(key)
                && !compiler_transport_environment_name(key))
        {
            return Err(invalid());
        }
        if !compiler_transport_environment_name(key) {
            environment.insert(key.clone(), value.clone());
        }
    }
    for (key, value) in runtime_environment {
        if key != b"DYLD_LIBRARY_PATH"
            || value.contains(&0)
            || value.len() > crate::MAX_FIELD
            || value.is_empty()
        {
            return Err(invalid());
        }
        environment.insert(key.clone(), value.clone());
    }
    let locator = format!(
        "v3:{}:{}:{}",
        binding.session,
        hex(&binding.root_attempt),
        hex(&binding.capability)
    );
    for (key, value) in [
        (b"ATERM_RESOURCE_JOB_V3".as_slice(), locator.as_bytes()),
        (b"ATERM_RESOURCE_INSPECTOR", inspector),
        (b"ATERM_SESSION_ID", binding.session.as_bytes()),
        (b"ATERM_PARENT_SESSION_ID", binding.session.as_bytes()),
        (b"ATERM_SDK_LEASE_V3", b"5"),
        (b"ATERM_WORKLOAD_CPU_FDS_V1", b"6"),
        (b"ATERM_WORKLOAD_HOST_STORE_FD_V1", b"7"),
        (
            super::super::super::CONTROL_FDS_ENV.as_bytes(),
            super::super::super::CONTROL_ADVERTISEMENT.as_bytes(),
        ),
    ] {
        environment.insert(key.to_vec(), value.to_vec());
    }
    let result = CommandSpec {
        program: original.program.clone(),
        arg0: None,
        args: original.args.clone(),
        cwd: original.cwd.clone(),
        environment: environment.into_iter().collect(),
    };
    let mut validation = Encoder::new(0);
    super::super::broker::command_write(&result, &mut validation)?;
    Ok(result)
}

#[cfg(test)]
mod tests;
