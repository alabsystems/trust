//! Trust: the project's `[trust]` policy, as targo sees it.
//!
//! targo is not the policy authority — `targo trust` decides what gets proved
//! and refuses to start on a policy it cannot read. targo needs the same table
//! for two other reasons: a build must be able to say which policy governs the
//! sources it is compiling, and the policy has to be reachable from a `Unit` so
//! it can eventually take part in the fingerprint that decides whether a unit
//! is fresh. Both need one parse of the table, shared with the manifest.

use std::path::{Path, PathBuf};

use cargo_util_schemas::manifest::TomlTrust;

use crate::core::{MaybePackage, Package, Workspace};
use crate::util::errors::CargoResult;

/// The policy governing one package, after workspace-wide defaults are folded
/// into the keys it left unwritten.
#[derive(Clone, Debug)]
pub struct EffectiveTrustPolicy {
    pub policy: TomlTrust,
    /// The manifest whose own `[trust]` table contributed, when it had one.
    pub declared_in: Option<PathBuf>,
    /// The workspace-root manifest that supplied defaults, when it did.
    pub workspace_defaults_from: Option<PathBuf>,
}

impl EffectiveTrustPolicy {
    /// One line naming the effective keys and where they came from.
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
        let mut summary = keys;
        if let Some(declared_in) = &self.declared_in {
            summary.push_str(&format!(" (from {})", declared_in.display()));
        }
        if let Some(workspace) = &self.workspace_defaults_from {
            summary.push_str(&format!(" (workspace defaults from {})", workspace.display()));
        }
        summary
    }
}

/// The policy governing `pkg` inside `ws`, or `None` when neither the package
/// nor its workspace root declares one.
pub fn effective_trust_policy(ws: &Workspace<'_>, pkg: &Package) -> Option<EffectiveTrustPolicy> {
    let member = pkg.manifest().trust_policy();
    let workspace = workspace_root_trust_policy(ws, pkg.manifest_path());

    if member.is_none() && workspace.is_none() {
        return None;
    }

    let mut policy = member.cloned().unwrap_or_default();
    if let Some((_, workspace_policy)) = &workspace {
        policy.fill_unset_from(workspace_policy);
    }

    Some(EffectiveTrustPolicy {
        policy,
        declared_in: member.map(|_| pkg.manifest_path().to_path_buf()),
        workspace_defaults_from: workspace.map(|(path, _)| path),
    })
}

/// The workspace root's own table, unless the root *is* this package — in which
/// case its table is already the member table and must not be applied twice.
fn workspace_root_trust_policy(
    ws: &Workspace<'_>,
    member_manifest: &Path,
) -> Option<(PathBuf, TomlTrust)> {
    let root_manifest = ws.root_manifest();
    if root_manifest == member_manifest {
        return None;
    }
    let policy = match ws.root_maybe() {
        MaybePackage::Package(pkg) => pkg.manifest().trust_policy()?,
        MaybePackage::Virtual(virtual_manifest) => virtual_manifest.trust_policy()?,
    };
    Some((root_manifest.to_path_buf(), policy.clone()))
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
    let Some(pkg) = ws.current_opt() else {
        return Ok(());
    };
    let Some(effective) = effective_trust_policy(ws, pkg) else {
        return Ok(());
    };
    ws.gctx().shell().note(format!(
        "this project declares a Trust policy that an unverified build does not apply: {}",
        effective.summary()
    ))
}
