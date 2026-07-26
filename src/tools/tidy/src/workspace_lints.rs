//! Trust: keep `[workspace.lints]` from being a decoration.
//!
//! A workspace lint table only reaches a crate when that crate writes
//! `[lints] workspace = true`. Without the opt-in, tightening the table changes
//! nothing anywhere and the next reader reasonably assumes the policy is live.
//! So the opt-in is a checked property of every Trust-owned member, ratcheted
//! against `trust-workspace-lints-ratchet.txt`: the count of members still
//! outside the table may fall, never rise. The ratchet is at zero, so it now
//! reads as a hard requirement — a new Trust crate that skips the opt-in fails
//! tidy immediately. The counter is kept rather than replaced by an assertion
//! so that a future split of the policy (a workspace whose members legitimately
//! opt out) can be recorded and then walked back down.
//!
//! Upstream members (`compiler/`, `library/`, `src/tools/*`) are deliberately
//! out of scope. Their manifests are upstream's, and an opt-in line in each
//! would be a merge conflict per crate bought for a policy Trust does not set
//! on them.

use std::path::Path;

use crate::diagnostics::{CheckId, TidyCtx};

const RATCHET: &str = "src/tools/tidy/trust-workspace-lints-ratchet.txt";

/// Workspace manifests that must carry a `[workspace.lints]` table, because a
/// Trust-owned member of theirs is expected to inherit from it.
const TRUST_WORKSPACES: &[&str] = &["Cargo.toml", "crates/Cargo.toml", "targo-trust/Cargo.toml"];

/// Does this manifest text contain a `[lints]` table whose `workspace` is true?
///
/// Deliberately a line scan: tidy has no TOML parser and the property is a
/// single unambiguous key, so a parser would be a dependency bought for one
/// question.
fn opts_into_workspace_lints(contents: &str) -> bool {
    let mut in_lints = false;
    for line in contents.lines() {
        let line = line.split('#').next().unwrap_or("").trim();
        if line.starts_with('[') {
            in_lints = line == "[lints]";
            continue;
        }
        if in_lints && line.replace(' ', "") == "workspace=true" {
            return true;
        }
    }
    false
}

fn declares_workspace_lints(contents: &str) -> bool {
    contents.lines().any(|line| {
        let line = line.split('#').next().unwrap_or("").trim();
        line == "[workspace.lints]" || line.starts_with("[workspace.lints.")
    })
}

/// Trust-owned member manifests, in a stable order.
fn trust_member_manifests(root_path: &Path) -> Vec<std::path::PathBuf> {
    let mut manifests = Vec::new();
    let targo_trust = root_path.join("targo-trust/Cargo.toml");
    if targo_trust.exists() {
        manifests.push(targo_trust);
    }
    if let Ok(entries) = std::fs::read_dir(root_path.join("crates")) {
        let mut crate_manifests: Vec<_> = entries
            .filter_map(|entry| entry.ok())
            .map(|entry| entry.path().join("Cargo.toml"))
            .filter(|path| path.is_file())
            .collect();
        crate_manifests.sort();
        manifests.extend(crate_manifests);
    }
    manifests
}

fn read_ratchet(root_path: &Path) -> Option<usize> {
    std::fs::read_to_string(root_path.join(RATCHET))
        .ok()?
        .lines()
        .map(|line| line.split('#').next().unwrap_or("").trim().to_string())
        .find(|line| !line.is_empty())?
        .parse()
        .ok()
}

fn write_ratchet(root_path: &Path, count: usize) {
    let contents = format!(
        "# Trust workspace-lint ratchet: how many Trust-owned member manifests\n\
         # still lack `[lints] workspace = true`. See src/tools/tidy/src/workspace_lints.rs.\n\
         # Only ever goes down. `x.py test tidy --bless` writes the current lower count.\n\
         {count}\n"
    );
    let path = root_path.join(RATCHET);
    if let Err(error) = std::fs::write(&path, contents) {
        panic!("could not write {}: {error}", path.display());
    }
}

pub fn check(root_path: &Path, tidy_ctx: TidyCtx) {
    let mut check = tidy_ctx.start_check(CheckId::new("workspace_lints"));

    for workspace in TRUST_WORKSPACES {
        let path = root_path.join(workspace);
        let Ok(contents) = std::fs::read_to_string(&path) else {
            check.error(format!("{workspace}: missing workspace manifest"));
            continue;
        };
        if !declares_workspace_lints(&contents) {
            check.error(format!(
                "{workspace} declares no `[workspace.lints]`, so a member that writes \
                 `[lints] workspace = true` cannot resolve it"
            ));
        }
    }

    let mut outstanding = Vec::new();
    for manifest in trust_member_manifests(root_path) {
        let Ok(contents) = std::fs::read_to_string(&manifest) else { continue };
        if !contents.contains("[package]") {
            continue;
        }
        if !opts_into_workspace_lints(&contents) {
            outstanding.push(
                manifest.strip_prefix(root_path).unwrap_or(&manifest).display().to_string(),
            );
        }
    }

    let found = outstanding.len();
    match read_ratchet(root_path) {
        None => check.error(format!(
            "{RATCHET} is missing or unparseable; without a recorded count the \
             opt-in ratchet enforces nothing. Record {found} with `--bless`."
        )),
        Some(allowed) if found > allowed => {
            for manifest in outstanding.iter().take(10) {
                check.warning(format!("{manifest}: no `[lints] workspace = true`"));
            }
            check.error(format!(
                "{found} Trust-owned manifests are outside `[workspace.lints]`, ratchet \
                 allows {allowed}. A new crate must opt in; the ratchet only goes down."
            ));
        }
        Some(allowed) if found < allowed => {
            if tidy_ctx.is_bless_enabled() {
                write_ratchet(root_path, found);
                check.warning(format!("workspace-lint ratchet lowered {allowed} -> {found}"));
            } else {
                check.warning(format!(
                    "{found} Trust-owned manifests are outside `[workspace.lints]`, ratchet \
                     still allows {allowed}. Lower it with `x.py test tidy --bless`."
                ));
            }
        }
        Some(_) => {}
    }
}
