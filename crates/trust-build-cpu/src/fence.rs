// SPDX-License-Identifier: MIT OR Apache-2.0
// Copyright 2026 Andrew Yates

use std::collections::BTreeMap;
use std::fs::{File, OpenOptions};
use std::io;
use std::os::unix::fs::{MetadataExt, OpenOptionsExt};
use std::path::Path;
use std::sync::Arc;

use crate::{invalid, unix};

/// Shared locks that keep legacy exclusive-slot launchers outside a native epoch.
/// Every executing descendant retains these actual open descriptions.
#[derive(Clone, Debug)]
pub struct LegacyFence {
    files: Vec<Arc<File>>,
}

impl LegacyFence {
    /// Validate and retain a complete fence inherited from a participating
    /// launcher or authenticated ancestor. This creates no files and never
    /// downgrades an old exclusive lock. A copied path or PID is insufficient.
    pub fn from_inherited(directory: &Path, slots: u32, files: Vec<File>) -> io::Result<Self> {
        if !directory.is_absolute() || slots == 0 || slots > 126 || files.len() > 127 {
            return Err(invalid("invalid legacy CPU fence size or directory"));
        }
        let _directory = unix::open_parent(directory)?;
        let mut names: Vec<_> = (0..slots).map(|slot| format!("slot-{slot}")).collect();
        names.push("admission.lock".into());
        for entry in std::fs::read_dir(directory)? {
            let name = entry?.file_name();
            let Some(name) = name.to_str() else { continue };
            if name.strip_prefix("slot-").is_some_and(|tail| {
                !tail.is_empty() && tail.bytes().all(|byte| byte.is_ascii_digit())
            }) && !names.iter().any(|known| known == name)
            {
                names.push(name.to_owned());
            }
        }
        if names.len() != files.len() || names.len() > 127 {
            return Err(invalid("inherited legacy fence is incomplete"));
        }
        let mut inherited = BTreeMap::new();
        for file in files {
            let meta = file.metadata()?;
            // SAFETY: geteuid only reads the process identity.
            if !meta.is_file()
                || meta.nlink() != 1
                || meta.mode() & 0o022 != 0
                || meta.uid() != unsafe { libc::geteuid() }
            {
                return Err(invalid("unsafe inherited legacy fence file"));
            }
            if inherited.insert((meta.dev(), meta.ino()), file).is_some() {
                return Err(invalid("duplicate inherited legacy fence descriptor"));
            }
        }
        let mut retained = Vec::with_capacity(names.len());
        for name in names {
            let path = directory.join(name);
            // The probe's lock only checks, so every exit unlocks it: a
            // concurrent spawn's copy of the descriptor would otherwise keep a
            // legacy launcher out of this slot until that copy closes.
            let probe = unix::Probe(
                OpenOptions::new()
                    .read(true)
                    .custom_flags(libc::O_NOFOLLOW | libc::O_CLOEXEC)
                    .open(&path)?,
            );
            let meta = probe.0.metadata()?;
            let file = inherited
                .remove(&(meta.dev(), meta.ino()))
                .ok_or_else(|| invalid("legacy fence path does not match inherited descriptor"))?;
            // A fresh description must be able to take SH. If the inherited
            // description held EX, even in this process, this refuses instead
            // of silently downgrading the legacy job's exclusion.
            probe
                .0
                .try_lock_shared()
                .map_err(|_| invalid("legacy exclusive job still owns a fence slot"))?;
            // Tests copy the descriptor table here, as a concurrent spawn can,
            // and fail as the inherited lock below can: every exit after the
            // probe's lock must unlock it.
            #[cfg(test)]
            tests::probe_locked()?;
            file.try_lock_shared().map_err(|_| invalid("inherited legacy fence is unavailable"))?;
            drop(probe);
            retained.push(Arc::new(file));
        }
        Ok(Self { files: retained })
    }

    /// Actual retained descriptors for an explicit exec or authenticated handoff.
    pub fn files(&self) -> &[Arc<File>] {
        &self.files
    }
}

#[cfg(test)]
mod tests;
