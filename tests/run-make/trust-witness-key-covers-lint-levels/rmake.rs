//! Trust (LINUX-SELF-HOST-1, 2026-11-12): a typeck root minted under one set of command-line
//! lint levels is never replayed into a compile run under another, and a root minted in one
//! run still replays in a run that differs only by its verification nonce.
//!
//! The witness key hashed `dep_tracking_hash(true)`, the crate-hash subset of the options, which
//! leaves out `lint_opts` and `lint_cap`. The mint gate admits a root only when its typeck
//! emitted no diagnostic, but it judges that under the minting compile's levels. So:
//!  * `cast.rs`: minted under the default levels (`trivial_numeric_casts` is allow), replayed
//!    under `-Dtrivial_numeric_casts`, the warm compile succeeded where a cold one fails;
//!  * `deprecated.rs`: minted under `--cap-lints allow` (as bootstrap compiles registry crates),
//!    replayed uncapped, the warm compile lost the `deprecated` warning a cold one prints.
//! Both were measured on 82bb867edd and 6762badf3c (GB10). The key now hashes the whole
//! `[TRACKED]` fingerprint (docs/TYPECK_MOONSHOT.md, A3) less the per-run freshness values
//! (`Options::witness_tracking_hash`; rustc_interface's unit test covers verification on).
//!
//! Each case runs a positive control first: the same warm compile under the minting levels,
//! with a different `-Ztrust-verify-session` nonce, does replay `big`. So a pass cannot come
//! from a store that replays nothing, and the nonce is shown not to enter the key.
//!
//! `-Ztrust-verify=off`: the lint behaviour is a frontend property; this test checks diagnostics.

//@ needs-target-std

use run_make_support::{rfs, rustc};

const ACCEPT: &str = "TRUST_REPLAY ACCEPT";
const MISS: &str = "TRUST_REPLAY MISS-nokey";

fn compile(src: &str, out: &str, extra: &[&str]) -> run_make_support::Rustc {
    let mut cmd = rustc();
    cmd.input(src)
        .crate_type("lib")
        .edition("2021")
        .emit("metadata,link")
        .out_dir(out)
        .arg("-Zthreads=1")
        .arg("-Ztrust-verify=off")
        .env("TRUST_WITNESS_STATS", "1")
        .env_remove("TRUST_WITNESS_MIN_NODES");
    for arg in extra {
        cmd.arg(arg);
    }
    cmd
}

/// Mint `src` into a fresh out-dir under `mint` levels, then copy the store into two more
/// fresh out-dirs: one for the control, one for the case. Returns those two.
fn minted(name: &str, src: &str, mint: &[&str]) -> (String, String) {
    let base = format!("{name}-mint");
    rfs::create_dir(&base);
    let cold = compile(src, &base, mint).run().stderr_utf8();
    assert!(!cold.contains(ACCEPT), "{name}: the minting compile found a store:\n{cold}");
    let stores: Vec<_> = rfs::read_dir(&base)
        .filter_map(|entry| {
            let path = entry.unwrap().path();
            (path.extension().is_some_and(|ext| ext == "twit")).then_some(path)
        })
        .collect();
    assert_eq!(stores.len(), 1, "{name}: the minting compile left {} stores", stores.len());
    let file = stores[0].file_name().unwrap().to_owned();
    let (control, case) = (format!("{name}-control"), format!("{name}-case"));
    for dir in [&control, &case] {
        rfs::create_dir(dir);
        rfs::copy(&stores[0], std::path::Path::new(dir).join(&file));
    }
    (control, case)
}

fn with_nonce<'a>(levels: &[&'a str]) -> Vec<&'a str> {
    let mut args = levels.to_vec();
    args.push("-Ztrust-verify-session=another-run");
    args
}

fn main() {
    // 1. `-D` a lint the minting compile allowed.
    let (control, case) = minted("cast", "cast.rs", &[]);
    let warm = compile("cast.rs", &control, &with_nonce(&[])).run().stderr_utf8();
    assert!(warm.contains(ACCEPT), "cast: the control replayed no root:\n{warm}");
    let denied = compile("cast.rs", &case, &["-Dtrivial_numeric_casts"])
        .run_fail()
        .assert_exit_code(1)
        .stderr_utf8();
    assert!(
        denied.contains("trivial numeric cast"),
        "cast: the -D compile failed without the lint's error:\n{denied}"
    );
    assert!(
        !denied.contains(ACCEPT),
        "cast: a root minted under other levels was replayed:\n{denied}"
    );
    assert!(denied.contains(MISS), "cast: the -D compile did not miss on the key:\n{denied}");

    // 2. Lift a cap the minting compile ran under.
    let capped = ["--cap-lints", "allow"];
    let (control, case) = minted("deprecated", "deprecated.rs", &capped);
    let warm = compile("deprecated.rs", &control, &with_nonce(&capped)).run().stderr_utf8();
    assert!(warm.contains(ACCEPT), "deprecated: the control replayed no root:\n{warm}");
    let uncapped = compile("deprecated.rs", &case, &[]).run().stderr_utf8();
    assert!(
        uncapped.contains("use of deprecated method"),
        "deprecated: the uncapped compile lost the deprecation warning:\n{uncapped}"
    );
    assert!(
        !uncapped.contains(ACCEPT),
        "deprecated: a root minted under --cap-lints allow was replayed:\n{uncapped}"
    );
    assert!(
        uncapped.contains(MISS),
        "deprecated: the uncapped compile did not miss on the key:\n{uncapped}"
    );
}
