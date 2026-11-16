//! Module for managing build stamp files.
//!
//! Contains the core implementation of how bootstrap utilizes stamp files on build processes.

use std::path::{Path, PathBuf};
use std::{fs, io};

// Trust: this module has no codegen-backend-kind use.
use crate::core::builder::Builder;
use crate::core::compiler::Compiler;
use crate::core::config::TargetSelection;
use crate::core::session::Mode;
use crate::utils::helpers::{mtime, t};

#[cfg(test)]
mod tests;

/// Manages a stamp file to track build state. The file is created in the given
/// directory and can have custom content and name.
#[derive(Clone)]
pub struct BuildStamp {
    path: PathBuf,
    stamp: String,
}

impl BuildStamp {
    /// Creates a new `BuildStamp` for a given directory.
    ///
    /// By default, stamp will be an empty file named `.stamp` within the specified directory.
    pub fn new(dir: &Path) -> Self {
        // Avoid using `is_dir()` as the directory may not exist yet.
        // It is more appropriate to assert that the path is not a file.
        assert!(!dir.is_file(), "can't be a file path");
        Self::projected(dir)
    }

    /// Construct requested stamp data without observing the filesystem.
    /// Callers must validate their output namespace before any write or cleanup.
    pub(crate) fn projected(dir: &Path) -> Self {
        Self { path: dir.join(".stamp"), stamp: String::new() }
    }

    /// Returns path of the stamp file.
    pub fn path(&self) -> &Path {
        &self.path
    }

    /// Returns the value of the stamp.
    ///
    /// Note that this is empty by default and is populated using `BuildStamp::add_stamp`.
    /// It is not read from an actual file, but rather it holds the value that will be used
    /// when `BuildStamp::write` is called.
    pub fn stamp(&self) -> &str {
        &self.stamp
    }

    /// Adds specified stamp content to the current value.
    ///
    /// This method can be used incrementally e.g., `add_stamp("x").add_stamp("y").add_stamp("z")`.
    pub fn add_stamp<S: ToString>(mut self, stamp: S) -> Self {
        self.stamp.push_str(&stamp.to_string());
        self
    }

    /// Adds a prefix to stamp's name.
    ///
    /// Prefix cannot start or end with a dot (`.`).
    pub fn with_prefix(mut self, prefix: &str) -> Self {
        assert!(
            !prefix.starts_with('.') && !prefix.ends_with('.'),
            "prefix can not start or end with '.'"
        );

        let stamp_filename = self.path.file_name().unwrap().to_str().unwrap();
        let stamp_filename = stamp_filename.strip_prefix('.').unwrap_or(stamp_filename);
        self.path.set_file_name(format!(".{prefix}-{stamp_filename}"));

        self
    }

    /// Removes the stamp file if it exists.
    pub fn remove(&self) -> io::Result<()> {
        match fs::remove_file(&self.path) {
            Ok(()) => Ok(()),
            Err(e) => {
                if e.kind() == io::ErrorKind::NotFound {
                    Ok(())
                } else {
                    Err(e)
                }
            }
        }
    }

    /// Creates the stamp file.
    pub fn write(&self) -> io::Result<()> {
        fs::write(&self.path, &self.stamp)
    }

    /// Checks if the stamp file is up-to-date.
    ///
    /// It is considered up-to-date if file content matches with the stamp string.
    pub fn is_up_to_date(&self) -> bool {
        match fs::read(&self.path) {
            Ok(h) => self.stamp.as_bytes() == h.as_slice(),
            Err(e) if e.kind() == io::ErrorKind::NotFound => false,
            Err(e) => {
                panic!("failed to read stamp file `{}`: {}", self.path.display(), e);
            }
        }
    }
}

/// Clear out `dir` if `input` is newer.
///
/// After this executes, it will also ensure that `dir` exists.
pub fn clear_if_dirty(builder: &Builder<'_>, dir: &Path, input: &Path) -> bool {
    let stamp = BuildStamp::new(dir);
    let mut cleared = false;
    if mtime(stamp.path()) < mtime(input) {
        builder.do_if_verbose(|| {
            println!(
                "Removing dirty directory `{}` because `{}` changed",
                dir.display(),
                input.display(),
            )
        });
        let _ = fs::remove_dir_all(dir);
        cleared = true;
    } else if stamp.path().exists() {
        return cleared;
    }
    t!(fs::create_dir_all(dir));
    t!(fs::File::create(stamp.path()));
    cleared
}

/// Trust: retain std outputs only for the exact compiler runtime that built them.
/// An absent/legacy stamp is not a match. Never record a new identity after a
/// failed removal; Cargo's cached compiler query must disappear with old rmeta.
pub fn clear_if_identity_changed(dir: &Path, identity: &str) -> io::Result<bool> {
    if identity.is_empty() {
        return Err(io::Error::new(io::ErrorKind::InvalidInput, "empty compiler runtime identity"));
    }
    let exists = match fs::symlink_metadata(dir) {
        Ok(metadata) if metadata.is_dir() => true,
        Ok(_) => return Err(io::Error::other("compiler output is not a real directory")),
        Err(error) if error.kind() == io::ErrorKind::NotFound => false,
        Err(error) => return Err(error),
    };
    let stamp = BuildStamp::new(dir).add_stamp(identity);
    match fs::symlink_metadata(stamp.path()) {
        Ok(metadata) if metadata.is_file() => {
            if fs::read(stamp.path())? == identity.as_bytes() {
                return Ok(false);
            }
        }
        Ok(_) => return Err(io::Error::other("compiler runtime stamp is not a regular file")),
        Err(error) if error.kind() == io::ErrorKind::NotFound => {}
        Err(error) => return Err(error),
    }
    if exists {
        fs::remove_dir_all(dir)?;
    }
    fs::create_dir_all(dir)?;
    stamp.write()?;
    Ok(true)
}

/// Cargo's output path for the standard library in a given stage, compiled
/// by a particular `build_compiler` for the specified `target`.
pub fn libstd_stamp(
    builder: &Builder<'_>,
    build_compiler: Compiler,
    target: TargetSelection,
) -> BuildStamp {
    BuildStamp::new(&builder.cargo_out(build_compiler, Mode::Std, target)).with_prefix("libstd")
}

/// Cargo's output path for librustc in a given stage, compiled by a particular
/// `build_compiler` for the specified target.
pub fn librustc_stamp(
    builder: &Builder<'_>,
    build_compiler: Compiler,
    target: TargetSelection,
) -> BuildStamp {
    BuildStamp::new(&builder.cargo_out(build_compiler, Mode::Rustc, target)).with_prefix("librustc")
}
