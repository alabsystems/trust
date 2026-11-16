//! Trust: kernel-enforced input and output paths for a native build action.
//!
//! This is an execution boundary, not a complete action key or proof authority.
//! In particular, callers must still bind directory contents, environment,
//! platform inputs and inherited streams before claiming a reusable result.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

use anyhow::{Context, Result, bail};

/// A structured allowlist. Arbitrary policy text is deliberately not accepted.
#[derive(Clone, Debug, Default)]
pub struct ActionSandbox {
    read_files: BTreeSet<PathBuf>,
    read_directories: BTreeSet<PathBuf>,
    read_entries: BTreeSet<PathBuf>,
    write_directories: BTreeSet<PathBuf>,
    executables: BTreeSet<PathBuf>,
    // Reading a declared path may first read an ancestor symlink (/var on
    // macOS, for example). Permit that link itself, never its whole subtree.
    path_links: BTreeSet<PathBuf>,
}

impl ActionSandbox {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn read_file(&mut self, path: &Path) -> Result<&mut Self> {
        let resolved = plain_path(path, false)?;
        self.capture_path_links(path)?;
        self.read_files.insert(resolved);
        Ok(self)
    }

    pub fn read_directory(&mut self, path: &Path) -> Result<&mut Self> {
        let resolved = plain_path(path, true)?;
        self.capture_path_links(path)?;
        self.read_directories.insert(resolved);
        Ok(self)
    }

    pub fn write_directory(&mut self, path: &Path) -> Result<&mut Self> {
        let resolved = plain_path(path, true)?;
        self.capture_path_links(path)?;
        self.write_directories.insert(resolved);
        Ok(self)
    }

    /// Permit observing this directory itself, without reading its descendants.
    /// This is needed for getcwd when a workspace member compiles from its parent.
    pub fn read_directory_entry(&mut self, path: &Path) -> Result<&mut Self> {
        let resolved = plain_path(path, true)?;
        self.capture_path_links(path)?;
        self.read_entries.insert(resolved);
        Ok(self)
    }

    pub fn executable(&mut self, path: &Path) -> Result<&mut Self> {
        let resolved = plain_path(path, false)?;
        self.capture_path_links(path)?;
        self.read_files.insert(resolved.clone());
        self.executables.insert(resolved);
        Ok(self)
    }

    fn capture_path_links(&mut self, path: &Path) -> Result<()> {
        for ancestor in path.ancestors() {
            if std::fs::symlink_metadata(ancestor)?
                .file_type()
                .is_symlink()
            {
                self.path_links.insert(ancestor.to_path_buf());
            }
        }
        Ok(())
    }

    pub(crate) fn profile(&self) -> String {
        let mut policy = String::from(
            "(version 1)\n(deny default)\n(allow process-fork)\n\
             (allow signal (target self))\n\
             (allow file-read* file-write* (literal \"/dev/null\"))\n\
             (allow file-read* (literal \"/\"))\n\
             (allow system-fcntl (fcntl-command F_ADDFILESIGS_RETURN F_CHECK_LV F_GETPATH))\n\
             (with-filter (mac-policy-name \"Sandbox\") (allow system-mac-syscall (mac-syscall-number 2)))\n",
        );
        for name in crate::platform_inputs::PLATFORM_SYSCTLS {
            policy.push_str(&format!("(allow sysctl-read (sysctl-name \"{name}\"))\n"));
        }
        let mut parents = BTreeSet::new();
        for path in self
            .read_files
            .iter()
            .chain(&self.read_directories)
            .chain(&self.read_entries)
            .chain(&self.write_directories)
            .chain(&self.executables)
        {
            parents.extend(path.ancestors().skip(1).map(Path::to_path_buf));
        }
        for path in parents {
            rule(&mut policy, "file-read-metadata", "literal", &path);
        }
        for path in &self.read_files {
            rule(&mut policy, "file-read*", "literal", path);
        }
        for path in &self.read_entries {
            rule(&mut policy, "file-read*", "literal", path);
        }
        for path in &self.path_links {
            rule(&mut policy, "file-read*", "literal", path);
        }
        for path in &self.read_directories {
            rule(
                &mut policy,
                "file-read* file-map-executable",
                "subpath",
                path,
            );
        }
        for path in &self.write_directories {
            rule(&mut policy, "file-read* file-write*", "subpath", path);
        }
        for path in &self.executables {
            rule(
                &mut policy,
                "process-exec file-map-executable",
                "literal",
                path,
            );
        }
        policy
    }

    pub(crate) fn require_supported(&self) -> Result<()> {
        if !cfg!(target_os = "macos") {
            bail!("native action confinement is not implemented on this platform");
        }
        if self.executables.is_empty() || self.write_directories.is_empty() {
            bail!("a confined action requires an executable and an output directory");
        }
        Ok(())
    }
}

fn plain_path(path: &Path, directory: bool) -> Result<PathBuf> {
    if !path.is_absolute() {
        bail!("action sandbox paths must be absolute: {}", path.display());
    }
    let text = path.to_str().context("action sandbox path is not UTF-8")?;
    if text.chars().any(char::is_control) {
        bail!("action sandbox path contains a control character");
    }
    let path = path
        .canonicalize()
        .with_context(|| format!("action input {}", path.display()))?;
    let metadata = path.metadata()?;
    if directory != metadata.is_dir() || (!directory && !metadata.is_file()) {
        bail!("action sandbox path has the wrong type: {}", path.display());
    }
    let text = path.to_str().context("action sandbox path is not UTF-8")?;
    if text.chars().any(char::is_control) {
        bail!("action sandbox path contains a control character");
    }
    Ok(path)
}

fn rule(policy: &mut String, operation: &str, filter: &str, path: &Path) {
    let text = path.to_str().expect("validated sandbox path");
    let escaped = text.replace('\\', "\\\\").replace('"', "\\\"");
    policy.push_str(&format!("(allow {operation} ({filter} \"{escaped}\"))\n"));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg(unix)]
    #[test]
    fn profile_is_deterministic_and_rejects_policy_injection() {
        let temp = tempfile::tempdir().unwrap();
        let path = temp.path().join("quote\"(allow default)");
        std::fs::create_dir(&path).unwrap();
        let mut sandbox = ActionSandbox::new();
        sandbox.read_directory(&path).unwrap();
        assert!(sandbox.profile().contains("quote\\\"(allow default)"));
        assert!(sandbox.profile().starts_with("(version 1)\n(deny default)"));
        assert!(!sandbox.profile().contains("(allow network"));
        assert!(sandbox.read_directory(Path::new("relative")).is_err());
        let bad = temp.path().join("newline\n");
        std::fs::create_dir(&bad).unwrap();
        assert!(sandbox.read_directory(&bad).is_err());
    }
}
