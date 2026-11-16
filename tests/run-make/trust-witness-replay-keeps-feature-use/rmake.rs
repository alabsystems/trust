//! Trust (2026-11-12): a rebuild into the same `--out-dir` reports no enabled feature as unused
//! that the first build used.
//!
//! A replayed typeck root skips typeck, and so skips the `TRACK_FEATURE` calls its method
//! lookup makes. `feature.rs` uses `wrapping_next_power_of_two` only inside `big`, a body the
//! default `-Ztrust-witness=auto` lane mints. Compiled twice into one out-dir with `-Dwarnings`,
//! the second compile replayed `big` and failed with "feature `wrapping_next_power_of_two` is
//! declared but not used" where the first passed (measured on 6762badf3c, GB10). The mint gate
//! now refuses a root whose cold typeck marked a feature used
//! (`GlobalCtxt::trust_witness_feature_epoch`).
//!
//! `stable.rs` is the same body without the unstable method: its second compile must still
//! replay `big`, so a pass here cannot come from a lane that replays nothing.

//@ needs-target-std

use run_make_support::{rfs, rustc};

const ACCEPT: &str = "TRUST_REPLAY ACCEPT";

fn compile(src: &str, out: &str) -> String {
    rustc()
        .input(src)
        .crate_type("lib")
        .edition("2021")
        .emit("metadata,link")
        .out_dir(out)
        .arg("-Zthreads=1")
        .arg("-Ztrust-verify=off")
        .arg("-Dwarnings")
        .env("TRUST_WITNESS_STATS", "1")
        .env_remove("TRUST_WITNESS_MIN_NODES")
        .run()
        .stderr_utf8()
}

fn main() {
    rfs::create_dir("stable");
    let first = compile("stable.rs", "stable");
    assert!(!first.contains(ACCEPT), "stable: the first compile found a store:\n{first}");
    let second = compile("stable.rs", "stable");
    assert!(second.contains(ACCEPT), "stable: the rebuild replayed nothing:\n{second}");

    rfs::create_dir("feature");
    let first = compile("feature.rs", "feature");
    assert!(!first.contains("declared but not used"), "feature: the first compile:\n{first}");
    // `run()` asserts exit status 0: under `-Dwarnings` the lint is an error.
    let second = compile("feature.rs", "feature");
    assert!(
        !second.contains("declared but not used"),
        "feature: the rebuild reported a used feature as unused:\n{second}"
    );
}
