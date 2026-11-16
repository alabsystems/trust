//! Basic validity of an executable declared by this actual Unit/output route.
//! Target-independent: no host execution, format, permission-bit or proof claim.

use std::fs;
use std::path::Path;

use anyhow::{Context as _, ensure};

use crate::CargoResult;

pub(super) fn require(path: &Path) -> CargoResult<()> {
    // Inspect the entry without following a symlink or opening a FIFO/device.
    // Existing output locks/owners remain responsible for producer exclusion;
    // this check supplies neither new custody nor a byte-integrity certificate.
    let metadata = fs::symlink_metadata(path).with_context(|| {
        format!(
            "could not inspect declared executable output `{}`",
            path.display()
        )
    })?;
    ensure!(
        metadata.is_file(),
        "declared executable output is not a regular file: `{}`",
        path.display()
    );
    ensure!(
        metadata.len() != 0,
        "declared executable output is empty: `{}`",
        path.display()
    );
    Ok(())
}
