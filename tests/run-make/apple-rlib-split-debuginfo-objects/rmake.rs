//! Trust: keep Darwin's upstream-compatible default object-retention check here.
//! An rlib-only build with unpacked split debuginfo leaves its loose objects
//! beside the rlib, matching the object members it archives.
//! The optional Trust cleanup controls live in the sibling
//! `trust-apple-rlib-split-debuginfo-objects` fixture.

//@ only-apple
//@ ignore-cross-compile (the binaries run on the host)

use run_make_support::object::read::archive::ArchiveFile;
use run_make_support::{has_extension, rfs, rustc, shallow_find_files};

/// The loose object files in `dir`, sorted.
fn objects_in(dir: &str) -> Vec<String> {
    let mut objects: Vec<String> = shallow_find_files(dir, |path| has_extension(path, "o"))
        .iter()
        .map(|path| path.file_name().unwrap().to_string_lossy().into_owned())
        .collect();
    objects.sort();
    objects
}

/// The object members of the archive at `path`.
fn archive_objects(path: &str) -> Vec<String> {
    let data = rfs::read(path);
    let archive = ArchiveFile::parse(&*data).unwrap();
    archive
        .members()
        .map(|member| String::from_utf8_lossy(member.unwrap().name()).into_owned())
        .filter(|name| name.ends_with(".o"))
        .collect()
}

const DEBUGINFO: [&str; 3] =
    ["-Cdebuginfo=line-tables-only", "-Csplit-debuginfo=unpacked", "-Ccodegen-units=2"];

fn main() {
    rfs::write(
        "dep.rs",
        "#[inline(never)]\n\
         pub fn dep_backtrace() -> String {\n\
         \x20   std::backtrace::Backtrace::force_capture().to_string()\n\
         }\n",
    );
    // Default, as upstream: the rlib-only compilation leaves beside the rlib exactly the
    // objects the rlib holds as members.
    rfs::create_dir("kept");
    rustc().input("dep.rs").crate_type("rlib").args(DEBUGINFO).out_dir("kept").run();
    let mut kept_members = archive_objects("kept/libdep.rlib");
    kept_members.sort();
    assert!(!kept_members.is_empty(), "the rlib holds no objects");
    assert_eq!(
        objects_in("kept"),
        kept_members,
        "an rlib-only build must retain the loose objects upstream preserves",
    );
}
