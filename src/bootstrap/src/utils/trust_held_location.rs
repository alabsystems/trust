//! Trust: refuse, at Bootstrap's start, a build location that the held-input
//! rule refuses an hour later.
//!
//! Binding the final Targo compiler pairing (`tool/paired_compiler.rs`) holds the
//! stage-1 sysroot through `HeldProgram::open`, which walks every directory from
//! `/` to it and applies `owned()` (`crates/trust-resource-provenance`): owner
//! root or this account, no `HELD_FORBIDDEN_MODE` bit, no ACL entry granting
//! access. The resource controller and the trust-build-tree cache probe hold the
//! stage0 seed sysroot, package sources and the Cargo home under the same rule.
//! On 2026-11-13 a toolchain cut under `<shared>` (root, mode 1777) built
//! stage-1 trustc for 1h05m and then panicked there.
//!
//! This runs the provenance crate's own walk over the existing part of each such
//! path before any build work and refuses with the directory, its owner and mode,
//! and the rule. A pass grants nothing: the later capture still decides, and the
//! directories Bootstrap creates afterwards are not observed here. The held
//! captures exist only on Apple-silicon macOS (elsewhere they return
//! `Unsupported` and the pairing is not compiled), so this check does too.

use std::ffi::CStr;
use std::os::unix::fs::MetadataExt as _;
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};
use std::{fs, io};

use trust_resource_provenance::program::{
    DirectoryRefusal, HELD_FORBIDDEN_MODE, check_directory_ancestry,
};

use crate::core::config::Config;
use crate::utils::trust_preparation::PreparationScope;

/// The runbook bullet that explains this refusal.
pub(crate) const RUNBOOK: &str = "docs/CUTTING-A-TOOLCHAIN.md, the bullet \"No directory from \
     `/` down to the checkout, the seed sysroot or the cargo home may be group- or \
     world-writable or carry a special bit\"";

/// Check every location a held capture later walks for this request.
pub(crate) fn ensure(config: &Config, initial_sysroot: &Path) -> Result<(), String> {
    ensure_with_cargo_home(config, initial_sysroot, home::cargo_home().ok().as_deref())
}

fn ensure_with_cargo_home(
    config: &Config,
    initial_sysroot: &Path,
    cargo_home: Option<&Path>,
) -> Result<(), String> {
    // A dry run holds nothing (the pairing returns before it binds), and these
    // kinds produce nothing a held capture reads.
    if config.dry_run() || PreparationScope::for_config(config) == PreparationScope::NotProducer {
        return Ok(());
    }
    let mut locations = vec![
        ("checkout", config.src.as_path()),
        ("build directory", config.out.as_path()),
        ("stage0 seed sysroot", initial_sysroot),
    ];
    if let Some(home) = cargo_home {
        locations.push(("Cargo home", home));
    }
    check(&locations)
}

/// Refuse at the first location whose existing directories, from `/` down, the
/// held-input rule refuses. Each location is `(role, path)`.
pub(crate) fn check(locations: &[(&str, &Path)]) -> Result<(), String> {
    let deadline = Instant::now() + Duration::from_secs(30);
    for &(role, path) in locations {
        let existing = existing_prefix(path).map_err(|refusal| message(role, path, &refusal))?;
        check_directory_ancestry(&existing, deadline)
            .map_err(|refusal| message(role, path, &refusal))?;
    }
    Ok(())
}

/// The canonical form of `path`'s longest existing prefix. The pairing
/// canonicalizes before it walks, so a symlink on the way (such as `/tmp`) is
/// judged by the directory it names. A missing tail is created later by
/// Bootstrap and cannot be judged now.
fn existing_prefix(path: &Path) -> Result<PathBuf, DirectoryRefusal> {
    for ancestor in path.ancestors().filter(|ancestor| !ancestor.as_os_str().is_empty()) {
        match fs::canonicalize(ancestor) {
            Ok(found) => return Ok(found),
            Err(error) if error.kind() == io::ErrorKind::NotFound => {}
            Err(error) => {
                return Err(DirectoryRefusal {
                    directory: ancestor.to_owned(),
                    uid: None,
                    mode: None,
                    error,
                });
            }
        }
    }
    Err(DirectoryRefusal {
        directory: path.to_owned(),
        uid: None,
        mode: None,
        error: io::Error::new(io::ErrorKind::NotFound, "no existing absolute prefix"),
    })
}

fn message(role: &str, path: &Path, refusal: &DirectoryRefusal) -> String {
    // The walk decides; this lookup only describes a component it could not open.
    let described = match (refusal.uid, refusal.mode) {
        (Some(uid), Some(mode)) => Some((uid, mode)),
        _ => fs::symlink_metadata(&refusal.directory).ok().map(|meta| (meta.uid(), meta.mode())),
    };
    let (owner, mode) = match described {
        Some((uid, mode)) => (
            match account(uid) {
                Some(name) => format!("{name} (uid {uid})"),
                None => format!("uid {uid}"),
            },
            format!("{:04o}", mode & 0o7777),
        ),
        None => ("unknown".to_owned(), "unknown".to_owned()),
    };
    // SAFETY: geteuid only reads this process's effective account.
    let euid = unsafe { libc::geteuid() };
    format!(
        "Trust build location refused: {directory} (owner {owner}, mode {mode}) is on the path \
         to the {role} {path}: {error}.\n\
         Rule: every directory from / down to the checkout, the build directory, the stage0 \
         seed sysroot and the Cargo home must be owned by root or by this account (uid {euid}), \
         carry no setuid, setgid, sticky, group-write or world-write bit (mode & {mask:#o} == 0) \
         and have no ACL entry that grants access.\n\
         This is the held-program check (`owned()` in \
         crates/trust-resource-provenance/src/program.rs) that binds the final Targo compiler \
         pairing after stage-1 trustc is built, about an hour into a toolchain cut. It is \
         checked here before any build work and is not relaxed: keep the checkout, the seed and \
         CARGO_HOME beneath directories that meet it. See {RUNBOOK}.",
        directory = refusal.directory.display(),
        path = path.display(),
        error = refusal.error,
        mask = HELD_FORBIDDEN_MODE,
    )
}

/// The account name of `uid`, for the message only.
fn account(uid: u32) -> Option<String> {
    let mut buffer = vec![0 as libc::c_char; 4096];
    // SAFETY: passwd is plain C data; getpwuid_r fills it or leaves `result` null.
    let mut entry: libc::passwd = unsafe { std::mem::zeroed() };
    let mut result = std::ptr::null_mut();
    // SAFETY: every pointer names storage this frame owns, with its true length.
    let status = unsafe {
        libc::getpwuid_r(uid, &mut entry, buffer.as_mut_ptr(), buffer.len(), &mut result)
    };
    if status != 0 || result.is_null() || entry.pw_name.is_null() {
        return None;
    }
    // SAFETY: on success pw_name is a NUL-terminated string inside `buffer`.
    Some(unsafe { CStr::from_ptr(entry.pw_name) }.to_string_lossy().into_owned())
}

#[cfg(test)]
mod tests;
