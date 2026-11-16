//! Trust: bootstrap uses the shared native build-holder implementation.

pub(crate) use build_helper::trust_repo_lock::{BuildLease, require_parent_handoff};

#[cfg(any(target_os = "macos", target_os = "linux"))]
pub(crate) fn acquire_command(
    root: &std::path::Path,
    kind: crate::core::builder::Kind,
) -> Result<build_helper::trust_repo_lock::management::Lease, String> {
    use build_helper::trust_repo_lock::management::{Acquire, Kind, LeaseAcquisition, Manager};
    let optional = |name: &str| match std::env::var(name) {
        Ok(value) => Ok(Some(value)),
        Err(std::env::VarError::NotPresent) => Ok(None),
        Err(_) => Err(format!("{name} must be UTF-8")),
    };
    let wait = optional("TRUST_BUILD_LOCK_WAIT")?.map_or(Ok(0), |value| {
        if value.is_empty() || !value.bytes().all(|byte| byte.is_ascii_digit()) {
            return Err("TRUST_BUILD_LOCK_WAIT must be a nonnegative integer".to_owned());
        }
        value.parse::<u64>().map_err(|_| "TRUST_BUILD_LOCK_WAIT exceeds its range".to_owned())
    })?;
    let request = Acquire {
        kind: Kind::Build,
        owner_pid: std::process::id(),
        purpose: format!("native bootstrap {kind:?}"),
        contract: "compiler output and its measurements share this original build tree".into(),
        wait: std::time::Duration::from_secs(wait),
        inherited_token: optional("TRUST_BUILD_LOCK_TOKEN")?,
        break_reason: None,
    };
    match Manager::open(root).and_then(|manager| manager.acquire_lease(&request)) {
        Ok(LeaseAcquisition::Granted(lease)) => Ok(lease),
        Ok(LeaseAcquisition::Busy(_)) => {
            Err("native build tree is held by another writer or measurement".into())
        }
        Err(error) => Err(error.to_string()),
    }
}

/// The commands that can write or remove compiler outputs. Keep this exhaustive
/// over native command kinds instead of reparsing the original argument string.
pub(crate) fn writes_build_tree(kind: crate::core::builder::Kind) -> bool {
    use crate::core::builder::Kind;
    match kind {
        Kind::Build
        | Kind::Check
        | Kind::Clippy
        | Kind::Fix
        | Kind::Test
        | Kind::Miri
        | Kind::MiriSetup
        | Kind::MiriTest
        | Kind::Bench
        | Kind::Doc
        | Kind::Clean
        | Kind::Dist
        | Kind::Install
        | Kind::Run => true,
        Kind::Format | Kind::Setup | Kind::Vendor => false,
    }
}

#[cfg(all(test, unix))]
#[path = "trust_repo_lock/tests/namespace.rs"]
pub(crate) mod namespace_tests;
