//! Trust (2026-10-17): the managed typeck-witness lane (`-Ztrust-witness=auto`, the default)
//! keeps its store as one flat `<StableCrateId>.twit` FILE in the `--out-dir`, never as a
//! directory there.
//!
//! Under Cargo the out-dir is `target/<profile>/deps`, and a tool that copies it file by file
//! may require it to hold no directories. rustc-build-sysroot's `copy_files` asserts exactly
//! that, so with the store at `<out-dir>/trust-witness/` every `targo-miri miri setup` on a
//! main stage 1 panicked with "cargo out dir must not contain directories" and Miri could not
//! build its sysroot (measured 2026-10-17, `x.py run src/tools/miri --stage 1`).
//!
//! The recipe compiles a crate whose bodies clear the router's node threshold twice into one
//! out-dir, with no witness flag:
//!  * after each compile the out-dir holds no directory;
//!  * the cold compile minted the store: at least one `.twit` file in the out-dir;
//!  * the warm compile read it back: at least one `TRUST_REPLAY ACCEPT` root;
//!  * a third compile reads it back as well: the warm compile's rewrite of the store keeps the
//!    roots it replayed (it once kept only the roots it typechecked, so a full hit emptied the
//!    store and the next build replayed nothing);
//!  * the warm compile's rmeta is byte-identical to a `-Ztrust-witness=off` build's, which
//!    writes no `.twit` file.
//! Empty AUTO collections create no file and preserve an existing populated store;
//! explicit empty minting continues to publish its empty measurement store.

use std::path::Path;

use run_make_support::{rfs, rustc};

/// `x + 1 + 1 + ...`: hundreds of HIR nodes, far above the router's default threshold of 64.
fn chain(len: usize) -> String {
    let mut e = String::from("x");
    for _ in 0..len {
        e.push_str(" + 1");
    }
    e
}

fn compile(src: &str, out: &str, lane: Option<&str>) -> String {
    let mut cmd = rustc();
    cmd.input(src)
        .crate_type("lib")
        .edition("2021")
        .emit("metadata,dep-info")
        .out_dir(out)
        .arg("-Zthreads=1")
        .arg("-Ztrust-verify=off")
        .env("TRUST_WITNESS_STATS", "1")
        .env_remove("TRUST_WITNESS_MIN_NODES");
    if let Some(lane) = lane {
        cmd.arg(format!("-Ztrust-witness={lane}"));
    }
    cmd.run().stderr_utf8()
}

fn entries(dir: &str) -> (Vec<String>, Vec<String>) {
    let (mut dirs, mut twits) = (Vec::new(), Vec::new());
    for entry in std::fs::read_dir(dir).unwrap() {
        let entry = entry.unwrap();
        let name = entry.file_name().to_string_lossy().into_owned();
        if entry.file_type().unwrap().is_dir() {
            dirs.push(name);
        } else if Path::new(&name).extension().is_some_and(|e| e == "twit") {
            twits.push(name);
        }
    }
    (dirs, twits)
}

// Trust: cleanup ownership names only the potential managed basename in this
// output directory, including off and explicitly located witness modes.
fn declared_store(out: &str) -> String {
    let deps = rfs::read_to_string(format!("{out}/heavy.d"));
    let stores = deps.lines().filter_map(|line| line.strip_prefix("# trust-witness-output-v1:")).collect::<Vec<_>>();
    assert_eq!(stores.len(), 1, "compiler omitted exact managed cache ownership");
    let store = stores[0];
    assert_eq!(store.len(), 21);
    assert!(store.ends_with(".twit"));
    assert!(store[..16].bytes().all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b)));
    store.to_owned()
}

fn main() {
    rfs::write("empty.rs", "");
    rfs::create_dir("empty-auto");
    compile("empty.rs", "empty-auto", None);
    let (dirs, twits) = entries("empty-auto");
    assert!(dirs.is_empty() && twits.is_empty(), "empty AUTO wrote a store: {dirs:?} {twits:?}");

    rfs::create_dir("empty-explicit");
    compile("empty.rs", "empty-explicit", Some("mint:empty-explicit"));
    let (dirs, twits) = entries("empty-explicit");
    assert!(dirs.is_empty(), "explicit mint left a directory: {dirs:?}");
    assert_eq!(twits.len(), 1, "explicit empty mint did not write its store: {twits:?}");
    let explicit = rfs::read(Path::new("empty-explicit").join(&twits[0]));
    assert_eq!(explicit.len(), 12, "explicit empty mint contains unexpected entries");
    assert_eq!(&explicit[..8], b"TWSTORE2", "explicit mint changed its store format");
    assert_eq!(&explicit[8..], &[0; 4], "explicit empty mint contains a nonzero entry count");

    let body = chain(120);
    let mut src: String =
        (0..8).map(|i| format!("pub fn g{i}(x: i64) -> i64 {{ {body} }}\n")).collect();
    // Trust: retain the arithmetic bodies, and add roots admitted by the
    // current conservative reconstruction grammar. A zero-entry store cannot
    // satisfy the cold/warm checks below. These bodies also exceed 64 HIR nodes.
    let tuple = std::iter::repeat_n("true", 120).collect::<Vec<_>>().join(", ");
    for i in 0..8 {
        src.push_str(&format!("pub fn h{i}() {{ let _ = ({tuple}); }}\n"));
    }
    rfs::write("heavy.rs", src);

    rfs::create_dir("auto");
    compile("heavy.rs", "auto", None);
    let (dirs, twits) = entries("auto");
    assert!(dirs.is_empty(), "the managed witness store left a directory in --out-dir: {dirs:?}");
    assert!(!twits.is_empty(), "the cold compile minted no flat .twit store in --out-dir");
    let managed = declared_store("auto");
    assert_eq!(twits, vec![managed.clone()]);
    let cold_stores: Vec<_> = twits
        .iter()
        .map(|name| (name.clone(), rfs::read(Path::new("auto").join(name))))
        .collect();
    let mut entry_count = 0u32;
    for (_, bytes) in &cold_stores {
        assert!(bytes.len() >= 12, "truncated cold witness store");
        assert_eq!(&bytes[..8], b"TWSTORE2", "unexpected witness store header");
        entry_count += u32::from_le_bytes(bytes[8..12].try_into().unwrap());
    }
    assert!(entry_count > 0, "a zero-entry file is not a cold witness mint");

    let warm = compile("heavy.rs", "auto", None);
    assert_eq!(declared_store("auto"), managed);
    let (dirs, _) = entries("auto");
    assert!(dirs.is_empty(), "the warm compile left a directory in --out-dir: {dirs:?}");
    let accepts = warm.lines().filter(|l| l.starts_with("TRUST_REPLAY ACCEPT")).count();
    assert!(accepts > 0, "the warm compile replayed no root from the flat store:\n{warm}");
    assert!(
        warm.lines().any(|line| line.starts_with("TRUST_REPLAY ACCEPT") && line.contains("::h0)")),
        "the admitted tuple root did not replay:\n{warm}"
    );
    // Trust: the incoming arithmetic-only fixture required an arithmetic root to replay.
    // Retain that coverage beside the pre-existing tuple and empty-store controls.
    assert!(
        warm.lines().any(|line| line.starts_with("TRUST_REPLAY ACCEPT") && line.contains("::g0)")),
        "the arithmetic root did not replay:\n{warm}"
    );
    for (name, bytes) in cold_stores {
        assert_eq!(
            rfs::read(Path::new("auto").join(name)),
            bytes,
            "an empty warm mint replaced the populated store"
        );
    }
    let third = compile("heavy.rs", "auto", None);
    assert_eq!(declared_store("auto"), managed);
    assert!(
        third.lines().any(|line| line.starts_with("TRUST_REPLAY ACCEPT")),
        "the next warm compile lost the populated store:\n{third}"
    );

    let (dirs, _) = entries("auto");
    assert!(dirs.is_empty(), "the third compile left a directory in --out-dir: {dirs:?}");
    let again = third.lines().filter(|l| l.starts_with("TRUST_REPLAY ACCEPT")).count();
    assert_eq!(again, accepts, "the warm compile's store lost the roots it replayed:\n{third}");

    rfs::create_dir("off");
    compile("heavy.rs", "off", Some("off"));
    let (dirs, twits) = entries("off");
    assert!(dirs.is_empty() && twits.is_empty(), "the off lane wrote a store: {dirs:?} {twits:?}");
    assert_eq!(declared_store("off"), managed, "off must not forget an earlier managed cache");
    rfs::create_dir("explicit-mint");
    compile("heavy.rs", "explicit-mint", Some("mint:caller-store"));
    assert_eq!(declared_store("explicit-mint"), managed);
    assert!(entries("explicit-mint").1.is_empty());
    assert_eq!(entries("caller-store").1, vec![managed.clone()]);
    rfs::create_dir("explicit-replay");
    compile("heavy.rs", "explicit-replay", Some("replay:caller-store"));
    assert_eq!(declared_store("explicit-replay"), managed);
    assert!(entries("explicit-replay").1.is_empty());
    assert_eq!(entries("caller-store").1, vec![managed]);
    // Trust: dep-info is written before analysis, so even failed type-checks
    // retain exact ownership of an earlier managed cache in this directory.
    rfs::create_dir("failed");
    let prior = rfs::read(format!("auto/{}", declared_store("auto")));
    rfs::write(format!("failed/{}", declared_store("auto")), &prior);
    rfs::write("broken.rs", "pub fn broken() -> MissingType { 0 }");
    rustc().input("broken.rs").crate_name("heavy").crate_type("lib")
        .edition("2021").emit("metadata,dep-info").out_dir("failed")
        .arg("-Ztrust-verify=off").run_fail()
        .assert_stderr_contains("cannot find type");
    assert_eq!(declared_store("failed"), declared_store("auto"));
    assert_eq!(rfs::read(format!("failed/{}", declared_store("failed"))), prior);
    assert_eq!(
        rfs::read("auto/libheavy.rmeta"),
        rfs::read("off/libheavy.rmeta"),
        "the replayed rmeta differs from the witness-off build's"
    );
}
