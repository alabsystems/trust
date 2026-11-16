//! Trust: a proc-macro dylib's Mach-O install name must identify the CRATE BUILD,
//! never its location on disk.
//!
//! `LC_ID_DYLIB` is the key dyld uses for its already-loaded registry, and a
//! proc-macro dylib is `dlopen`ed by absolute path and never linked against, so
//! that registry is its only consumer. When the install name is left as the build
//! output path — the linker's default — any COPY of the file goes on claiming the
//! original path. Loading such a copy in a process then poisons that path: a later
//! `dlopen` of it returns the copy, and `dlsym` of this build's
//! `__rustc_proc_macro_decls_*` misses.
//!
//! That is not hypothetical. Bootstrap copies proc-macro dylibs into several
//! sysroots, and because `CFG_VERSION` feeds `StableCrateId`, two revisions' builds
//! of one crate export different declarations symbols under one file name. Measured
//! 2026-09-13: sixteen copies of a single `libdisplaydoc-*.dylib` all claiming one
//! path that a different binary occupied, and three crates per build failing to
//! load with `dlsym(...): symbol not found`.
//!
//! This test pins the property that makes the aliasing impossible: two builds with
//! different crate identities, written to the same file name, must not share an
//! install name.

//@ only-apple
//@ ignore-cross-compile
//@ needs-crate-type: proc-macro

use run_make_support::{cmd, rfs, rustc};

/// The `LC_ID_DYLIB` install name recorded in the Mach-O header.
fn install_name(path: &str) -> String {
    let out = cmd("otool").arg("-D").arg(path).run().stdout_utf8();
    // `otool -D` prints the file name, then the install name on the next line.
    out.lines().last().unwrap().trim().to_string()
}

/// The `__rustc_proc_macro_decls_*` symbol this build exports, which is what a
/// consumer will `dlsym` for. Two builds sharing an install name but exporting
/// different symbols here is exactly the failure being prevented.
fn decls_symbol(path: &str) -> String {
    let out = cmd("nm").arg("-m").arg(path).run().stdout_utf8();
    out.lines()
        .filter(|l| l.contains("rustc_proc_macro_decls"))
        .map(|l| l.split_whitespace().last().unwrap().to_string())
        .next()
        .expect("no proc-macro declarations symbol in the dylib")
}

/// Build `macro.rs` under a forced rustc version, into `<dir>/libtestmac.dylib`.
///
/// The file name is deliberately identical across builds: it is the version, and
/// only the version, that distinguishes the two identities here.
fn build(dir: &str, forced_version: &str) -> String {
    rfs::create_dir_all(dir);
    let out = format!("{dir}/libtestmac.dylib");
    rustc().env("RUSTC_FORCE_RUSTC_VERSION", forced_version).input("macro.rs").output(&out).run();
    out
}

fn main() {
    let a = build("a", "trust-install-name-test-a");
    let b = build("b", "trust-install-name-test-b");

    let (name_a, name_b) = (install_name(&a), install_name(&b));
    let (sym_a, sym_b) = (decls_symbol(&a), decls_symbol(&b));

    // Non-vacuity: the two builds really are different crate identities. If this
    // ever stops holding, the assertion below would pass for the wrong reason.
    assert_ne!(
        sym_a, sym_b,
        "the two builds exported the same declarations symbol, so this test proves nothing",
    );

    // The install name must be identity-derived, not the output path.
    for (name, path) in [(&name_a, &a), (&name_b, &b)] {
        assert!(
            name.starts_with("rustc-proc-macro/"),
            "proc-macro dylib {path} has install name {name:?}, which is not identity-derived; \
             a copy of this file would claim {path:?} and hijack `dlopen` of it",
        );
    }

    // The property that makes dyld aliasing impossible.
    assert_ne!(
        name_a, name_b,
        "two different crate identities share the install name {name_a:?}; loading one would \
         make `dlopen` of the other return the wrong image and `dlsym` of {sym_b} miss",
    );
}
