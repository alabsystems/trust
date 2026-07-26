use std::fs::{File, OpenOptions};
use std::io;
use std::path::Path;

pub(crate) fn raw_path_toctou_boundary(path: &Path, replacement: &Path) -> io::Result<()> {
    let _metadata = std::fs::metadata(path)?;
    let _created = File::create(replacement)?;
    let _opened = OpenOptions::new().write(true).open(replacement)?;
    std::fs::rename(path, replacement)?;
    std::fs::remove_file(replacement)?;
    std::fs::remove_dir("target/hardened-fixture-empty-dir")
}

pub(crate) fn path_identity_boundary(path: &Path) -> bool {
    let canonical = std::fs::canonicalize(path).ok();
    path == Path::new("/") || canonical.as_deref() == Some(Path::new("/"))
}
