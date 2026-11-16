// Trust (spawn census, P2 review): a proc-macro crate that sits in the sysroot's target
// library directory (rustc-dev ships `librustc_macros` there) is in the crate graph of a
// crate that loads it, and counts as sysroot-resident. The census scans every
// sysroot-resident crate's monomorphic bodies for the `dyn` values they mint, and asked
// `def_kind` of every index first; a proc-macro crate's metadata encodes a `def_kind`
// for its root and its macros only, so the decoder hit `bug!` and the compiler aborted
// (SIGABRT) with verification on, `trustc`'s default. Proc-macro crates link into
// nothing the crate runs, and an index without MIR is skipped before its `def_kind` is
// read.
//
// The sysroot is mirrored into a scratch directory (symlinks), the proc-macro is built
// into the mirror's target library directory, and a crate that loads it is compiled
// against the mirror.

//@ ignore-cross-compile
//@ needs-dynamic-linking

use std::path::{Path, PathBuf};

use run_make_support::{bin_name, cmd, rfs, rustc_path, target};

const TRUST_VANILLA_REAL_RUSTC_ENV: &str = "__COMPILETEST_TRUST_VANILLA_REAL_RUSTC";

const PROC_MACRO: &str = r#"extern crate proc_macro;
use proc_macro::TokenStream;
#[proc_macro]
pub fn answer(_input: TokenStream) -> TokenStream { "42u32".parse().unwrap() }
"#;

const USER: &str = r#"extern crate pmx;
pub fn answer() -> u32 { pmx::answer!() }
pub fn launch() { let _handle = std::thread::spawn(|| {}); }
pub fn wrapper() { launch(); }
"#;

/// Mirror `from` into `to`: a directory on the path to `keep` is recreated and walked;
/// every other entry is a symlink to the original.
fn mirror(from: &Path, to: &Path, keep: &Path) {
    rfs::create_dir_all(to);
    rfs::read_dir_entries(from, |entry| {
        let name = entry.file_name().expect("a directory entry has a name");
        let link = to.join(name);
        if keep.starts_with(entry) && entry.is_dir() {
            mirror(entry, &link, keep);
        } else if entry.is_dir() {
            rfs::symlink_dir(entry, &link);
        } else {
            rfs::symlink_file(entry, &link);
        }
    });
}

fn main() {
    let rustc = PathBuf::from(rustc_path());
    let trustc = rustc.with_file_name(bin_name("trustc"));
    let trustc = if trustc.exists() { trustc } else { rustc };
    if std::env::var_os(TRUST_VANILLA_REAL_RUSTC_ENV).is_some() {
        // The upstream compiler does not know Trust's policy options.
        return;
    }
    let sysroot = PathBuf::from(cmd(&trustc).arg("--print=sysroot").run().stdout_utf8().trim());
    let target_lib = sysroot.join("lib").join("rustlib").join(target()).join("lib");
    let mirror_root = std::env::current_dir().expect("cwd").join("mirror");
    mirror(&sysroot, &mirror_root, &target_lib);
    let mirror_lib = mirror_root.join("lib").join("rustlib").join(target()).join("lib");

    rfs::write("pmx.rs", PROC_MACRO);
    cmd(&trustc)
        .arg("--edition=2021")
        .arg("--crate-type=proc-macro")
        .arg("--crate-name=pmx")
        .arg("-Ztrust-verify=off")
        .arg("--out-dir")
        .arg(&mirror_lib)
        .arg("pmx.rs")
        .run();

    rfs::write("user.rs", USER);
    let output = cmd(&trustc)
        .arg("--edition=2021")
        .arg("--crate-type=lib")
        .arg("--emit=metadata")
        .arg("--sysroot")
        .arg(&mirror_root)
        .arg("-Ztrust-verify=on")
        .arg("-Ztrust-policy=advisory")
        .arg("user.rs")
        .env_remove("TRUST_NO_VERIFY")
        .run();
    let stderr = output.stderr_utf8();
    for forbidden in ["panicked", "internal compiler error", "missing def_kind"] {
        assert!(!stderr.contains(forbidden), "`{forbidden}` in:\n{stderr}");
    }
    // The census still ran: `wrapper` is refused as reaching `launch`'s spawn.
    assert!(
        stderr.contains("local callee reaches a std thread spawn through calls and drops"),
        "the spawn census did not refuse `wrapper`:\n{stderr}"
    );
}
