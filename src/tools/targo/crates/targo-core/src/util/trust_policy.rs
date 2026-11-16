//! Trust: the project's `[trust]` policy, as targo sees it.
//!
//! targo is not the policy authority — `targo trust` decides what gets proved
//! and refuses to start on a policy it cannot read. targo needs the same table
//! for two other reasons: a build must be able to say which policy governs the
//! sources it is compiling, and the policy has to be reachable from a `Unit` so
//! it can eventually take part in the fingerprint that decides whether a unit
//! is fresh. Both need one parse of the table, shared with the manifest.

use std::path::PathBuf;

use cargo_util_schemas::manifest::TomlTrust;

use crate::workspace::Workspace;
use crate::util::errors::CargoResult;

/// The policy governing every package of a workspace: its root's table.
#[derive(Clone, Debug)]
pub struct WorkspaceTrustPolicy {
    pub policy: TomlTrust,
    /// The workspace root's manifest, which declares it.
    pub declared_in: PathBuf,
}

impl WorkspaceTrustPolicy {
    /// One line naming the declared keys and where they came from.
    pub fn summary(&self) -> String {
        let declared = self.policy.declared();
        let keys = if declared.is_empty() {
            "no keys".to_string()
        } else {
            declared
                .into_iter()
                .map(|(key, value)| format!("{key} = {value}"))
                .collect::<Vec<_>>()
                .join(", ")
        };
        format!("{keys} (from {})", self.declared_in.display())
    }
}

/// The policy governing every member of `ws`, or `None` when its root declares
/// none.
///
/// One workspace has one policy, the root's (plan §3.6; DECISION_QUEUE
/// T7c-4): `Workspace` has already read the root's table strictly and refused
/// any member's own table, so the root's table is all there is to read. A
/// table that does not read is an error here too, never a missing policy.
pub fn workspace_trust_policy(ws: &Workspace<'_>) -> CargoResult<Option<WorkspaceTrustPolicy>> {
    let policy = ws.root_maybe().trust_policy()?;
    Ok(policy.map(|policy| WorkspaceTrustPolicy {
        policy,
        declared_in: ws.root_manifest().to_path_buf(),
    }))
}

/// Say so when a build that makes no proof claim is compiling sources whose
/// project declares a Trust policy.
///
/// The verified lane stays silent here: `targo trust` prints the level it is
/// proving at, and repeating it from underneath would give one run two
/// authorities on the same question.
pub fn report_policy_not_honored(ws: &Workspace<'_>) -> CargoResult<()> {
    if crate::trust_verified_targo() {
        return Ok(());
    }
    if ws.current_opt().is_none() {
        return Ok(());
    }
    let Some(policy) = workspace_trust_policy(ws)? else {
        return Ok(());
    };
    ws.gctx().shell().note(format!(
        "this project declares a Trust policy that an unverified build does not apply: {}",
        policy.summary()
    ))
}
