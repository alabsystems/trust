// SPDX-License-Identifier: MIT OR Apache-2.0
// Copyright 2026 Andrew Yates

#![cfg(target_os = "macos")]

use std::fs::{self, File, OpenOptions};
use std::io::{Read, Write};
use std::os::unix::fs::{MetadataExt, OpenOptionsExt, PermissionsExt, symlink};
use std::path::Path;

use anyhow::ensure;
use cargo_util::paths::link_or_copy;
use filetime::FileTime;

fn world() -> anyhow::Result<tempfile::TempDir> {
    let base = Path::new("/tmp/.ubd/targo-unchanged-publication.noindex");
    fs::create_dir_all(base)?;
    let world = tempfile::Builder::new()
        .permissions(fs::Permissions::from_mode(0o700))
        .tempdir_in(base)?;
    ensure!(fs::metadata(world.path())?.permissions().mode() & 0o077 == 0);
    Ok(world)
}

fn write(path: &Path, bytes: &[u8], mode: u32) -> anyhow::Result<()> {
    let mut file = OpenOptions::new()
        .write(true)
        .create_new(true)
        .mode(mode)
        .open(path)?;
    file.write_all(bytes)?;
    file.set_permissions(fs::Permissions::from_mode(mode))?;
    Ok(())
}

fn identity(metadata: &fs::Metadata) -> (u64, u64) {
    (metadata.dev(), metadata.ino())
}

#[test]
fn identical_independent_executable_preserves_its_original_published_inode_and_mtime()
-> anyhow::Result<()> {
    let world = world()?;
    let source = world.path().join("source");
    let destination = world.path().join("published");
    let bytes = b"unchanged executable publication\n";
    write(&source, bytes, 0o755)?;
    write(&destination, bytes, 0o755)?;
    let mut held = File::open(&destination)?;
    let original = held.metadata()?;
    ensure!(
        identity(&original) != identity(&fs::metadata(&source)?),
        "fixture files must be independent"
    );
    link_or_copy(&source, &destination)?;
    let current = fs::metadata(&destination)?;
    ensure!(
        identity(&current) == identity(&original),
        "unchanged publication replaced its inode"
    );
    ensure!(
        current.modified()? == original.modified()?,
        "unchanged publication changed its mtime"
    );
    ensure!(
        held.metadata()?.nlink() == 1,
        "the pinned original inode was unlinked"
    );
    ensure!(current.permissions().mode() & 0o777 == 0o755);
    let mut observed = Vec::new();
    held.read_to_end(&mut observed)?;
    ensure!(observed == bytes && fs::read(&destination)? == bytes);
    Ok(())
}

/// A relinked executable that came out byte-identical (as `rustc-main` does
/// whenever only `librustc_driver` changed) is a newer output: the kept
/// publication takes its time, as a fresh copy would, so whatever compares the
/// published file's time (bootstrap's stale-std check, the `rustc -vV` cache)
/// sees the rebuild. It keeps its inode, and an older source never moves the
/// published time back.
#[test]
fn identical_rebuilt_executable_keeps_its_inode_and_takes_the_newer_time() -> anyhow::Result<()> {
    let world = world()?;
    let source = world.path().join("source");
    let destination = world.path().join("published");
    let bytes = b"relinked to the same bytes\n";
    write(&destination, bytes, 0o755)?;
    write(&source, bytes, 0o755)?;
    let published = FileTime::from_unix_time(1_700_000_000, 0);
    let rebuilt = FileTime::from_unix_time(1_800_000_000, 0);
    filetime::set_file_times(&destination, published, published)?;
    filetime::set_file_times(&source, rebuilt, rebuilt)?;
    let original = fs::metadata(&destination)?;

    link_or_copy(&source, &destination)?;
    let current = fs::metadata(&destination)?;
    ensure!(
        identity(&current) == identity(&original),
        "unchanged publication replaced its inode"
    );
    ensure!(
        FileTime::from_last_modification_time(&current) == rebuilt,
        "the published executable looks older than the output it publishes"
    );
    ensure!(fs::read(&destination)? == bytes);

    filetime::set_file_times(&source, published, published)?;
    link_or_copy(&source, &destination)?;
    let after = fs::metadata(&destination)?;
    ensure!(identity(&after) == identity(&original));
    ensure!(
        FileTime::from_last_modification_time(&after) == rebuilt,
        "an older source moved the published time back"
    );
    Ok(())
}

#[test]
fn equal_length_difference_after_multiple_comparison_buffers_is_repaired() -> anyhow::Result<()> {
    let world = world()?;
    let source = world.path().join("source");
    let destination = world.path().join("published");
    let bytes = (0..(3 * 128 * 1024 + 17))
        .map(|index| (index % 251) as u8)
        .collect::<Vec<_>>();
    let mut damaged = bytes.clone();
    *damaged.last_mut().unwrap() ^= 0x80;
    ensure!(bytes.len() == damaged.len() && bytes[..128 * 1024] == damaged[..128 * 1024]);
    write(&source, &bytes, 0o755)?;
    write(&destination, &damaged, 0o755)?;
    link_or_copy(&source, &destination)?;
    ensure!(
        fs::read(&destination)? == bytes,
        "tail corruption survived publication"
    );
    ensure!(fs::read(&source)? == bytes);
    Ok(())
}

#[test]
fn identical_bytes_with_wrong_execute_permissions_are_repaired() -> anyhow::Result<()> {
    let world = world()?;
    let source = world.path().join("source");
    let destination = world.path().join("published");
    let bytes = b"same bytes with different executable mode\n";
    write(&source, bytes, 0o755)?;
    write(&destination, bytes, 0o644)?;
    link_or_copy(&source, &destination)?;
    ensure!(fs::read(&destination)? == bytes);
    ensure!(fs::metadata(&destination)?.permissions().mode() & 0o777 == 0o755);
    Ok(())
}

#[test]
fn destination_symlink_to_identical_independent_file_is_replaced_without_changing_its_target()
-> anyhow::Result<()> {
    let world = world()?;
    let source = world.path().join("source");
    let independent = world.path().join("independent");
    let destination = world.path().join("published");
    let bytes = b"identical content does not authorize retaining a symlink\n";
    write(&source, bytes, 0o755)?;
    write(&independent, bytes, 0o755)?;
    symlink(&independent, &destination)?;
    let held = File::open(&independent)?;
    let original = held.metadata()?;
    ensure!(identity(&original) != identity(&fs::metadata(&source)?));
    link_or_copy(&source, &destination)?;
    ensure!(
        fs::symlink_metadata(&destination)?.file_type().is_file(),
        "publication retained the destination symlink"
    );
    ensure!(fs::read(&destination)? == bytes);
    let after = fs::metadata(&independent)?;
    ensure!(identity(&after) == identity(&original));
    ensure!(
        after.modified()? == original.modified()?
            && after.permissions().mode() == original.permissions().mode()
    );
    ensure!(held.metadata()?.nlink() == 1 && fs::read(&independent)? == bytes);
    Ok(())
}
