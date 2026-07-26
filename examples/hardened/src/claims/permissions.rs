use std::io;
use std::path::Path;

#[cfg(unix)]
use std::fs::{self, File};
#[cfg(unix)]
use std::os::unix::fs::PermissionsExt;

#[cfg(unix)]
pub(crate) fn permission_create_boundary(path: &Path) -> io::Result<()> {
    std::fs::create_dir(path)?;
    fs::create_dir_all("target/hardened-fixture-parent/child")?;
    Ok(())
}

#[cfg(not(unix))]
pub(crate) fn permission_create_boundary(_path: &Path) -> io::Result<()> {
    Ok(())
}

#[cfg(unix)]
pub(crate) fn permission_window_boundary(path: &Path) -> io::Result<()> {
    let _file = File::create(path)?;
    let permissions = fs::Permissions::from_mode(0o600);
    fs::set_permissions(path, permissions.clone())?;
    std::fs::set_permissions(path, permissions)?;
    chown(path);
    Ok(())
}

#[cfg(not(unix))]
pub(crate) fn permission_window_boundary(_path: &Path) -> io::Result<()> {
    Ok(())
}

#[cfg(unix)]
fn chown(_path: &Path) {}
