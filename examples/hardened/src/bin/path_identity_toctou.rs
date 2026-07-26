#[cfg(unix)]
use std::ffi::OsStr;
#[cfg(unix)]
use std::fs;
#[cfg(unix)]
use std::io;
#[cfg(unix)]
use std::path::Path;

#[cfg(unix)]
use hardened_regression_fixtures::{ScratchDir, unix_file_id};

#[cfg(unix)]
fn main() -> io::Result<()> {
    let scratch = ScratchDir::new("path-identity-toctou")?;
    let safe = scratch.write_file(OsStr::new("safe.txt"), b"safe\n")?;
    let swapped = scratch.write_file(OsStr::new("swapped.txt"), b"swapped\n")?;
    let checked = scratch.path_for(OsStr::new("checked"))?;
    let staged = scratch.path_for(OsStr::new("staged"))?;

    std::os::unix::fs::symlink(Path::new("safe.txt"), &checked)?;
    std::os::unix::fs::symlink(Path::new("swapped.txt"), &staged)?;

    let pre_link = fs::read_link(&checked)?;
    let pre_canonical = fs::canonicalize(&checked)?;
    let pre_id = unix_file_id(&checked)?;

    fs::rename(&staged, &checked)?;

    let post_link = fs::read_link(&checked)?;
    let post_canonical = fs::canonicalize(&checked)?;
    let post_id = unix_file_id(&checked)?;
    let observed = fs::read_to_string(&checked)?;

    if pre_id == post_id {
        return Err(io::Error::new(
            io::ErrorKind::Other,
            "rename did not change the followed file identity",
        ));
    }
    if pre_canonical == post_canonical {
        return Err(io::Error::new(
            io::ErrorKind::Other,
            "rename did not change the canonical target",
        ));
    }
    if observed != "swapped\n" {
        return Err(io::Error::new(
            io::ErrorKind::Other,
            "unchanged path did not read the swapped file",
        ));
    }

    println!("walkthrough=path_identity_toctou");
    println!("scratch={}", scratch.path().display());
    println!("checked_path={}", checked.display());
    println!("safe_file={}", safe.display());
    println!("swapped_file={}", swapped.display());
    println!("pre_link={}", pre_link.display());
    println!("post_link={}", post_link.display());
    println!("pre_file_id={pre_id}");
    println!("post_file_id={post_id}");
    println!("observed={}", observed.trim_end());
    println!("result=toctou-demonstrated");

    Ok(())
}

#[cfg(not(unix))]
fn main() {
    println!("walkthrough=path_identity_toctou");
    println!("unsupported=non-unix");
}
