// Trust (T6, 2026-10-09): a dependency's Cargo speed row no longer decides its
// dependents' verdicts.
//
// Every unit of a Trust proof session — the verified subject, and each
// verification-off dependency carrying `-Ztrust-verify-session` — runs the -O0
// MIR pipeline at every `-Copt-level`, and the subject reads the dependency's
// ENCODED MIR for the calls it makes into a declared crate
// (`-Ztrust-bundle-foreign-crate`). So:
//
//   * the dependency built inside the session at `-Copt-level=0` and at
//     `-Copt-level=2` must give the subject IDENTICAL rows (channel (a) of T6:
//     before it, the `-O2` build ran GVN and the MIR inliner over the bodies the
//     subject bundles). Both builds keep `-Cdebug-assertions` and
//     `-Coverflow-checks` on, as a Cargo dev profile's speed row does, so the
//     only input that moves is the opt-level;
//   * the dependency built at `-Copt-level=2` OUTSIDE a session (a vanilla rmeta)
//     carries the inliner's MIR, and its crate metadata says so
//     (`trust_crate_mir_is_proof_session_pipeline` is false): the subject must
//     decline to bundle its bodies, naming that reason — the control that shows
//     this program's rows are sensitive to the MIR shape the test holds fixed.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use run_make_support::serde_json::{self, Value};
use run_make_support::{bin_name, cmd, rfs, rustc_path};

const TRUST_VANILLA_REAL_RUSTC_ENV: &str = "__COMPILETEST_TRUST_VANILLA_REAL_RUSTC";
const SESSION: &str = "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef";
const NOT_PIPELINE: &str = "reason=foreign-member-not-proof-session-mir";

fn build_dep(trustc: &Path, dir: &str, flags: &[&str]) -> PathBuf {
    rfs::create_dir_all(dir);
    cmd(trustc)
        .arg("--edition=2021")
        .arg("--crate-type=rlib")
        .arg("--crate-name=session_dep")
        .arg("-Cdebug-assertions=on")
        .arg("-Coverflow-checks=on")
        .arg("-Ztrust-verify=off")
        .arg("-Zalways-encode-mir")
        .args(flags)
        .arg("--out-dir")
        .arg(dir)
        .arg("dep.rs")
        .env_remove("TRUST_NO_VERIFY")
        .run();
    PathBuf::from(dir).join("libsession_dep.rlib")
}

/// The subject's stderr, compiled against the dependency at `rlib`.
fn check_subject(trustc: &Path, rlib: &Path, out: &str) -> String {
    rfs::create_dir_all(out);
    cmd(trustc)
        .arg("--edition=2021")
        .arg("--crate-type=lib")
        .arg("--crate-name=subject")
        .arg("--emit=metadata")
        .arg("-Ztrust-verify=on")
        .arg("-Ztrust-policy=advisory")
        .arg("-Ztrust-verify-output=json")
        .arg("-Ztrust-bundle-foreign-crate=session_dep")
        .arg("--extern")
        .arg(format!("session_dep={}", rlib.display()))
        .arg("--out-dir")
        .arg(out)
        .arg("subject.rs")
        .env("TRUST_BUNDLE_TRACE", "1")
        .env("TRUST_BUNDLE_MEMBERS", "1")
        .env_remove("TRUST_NO_VERIFY")
        .run()
        .stderr_utf8()
}

/// `function -> its rows`, each row projected to what a verdict is: kind,
/// description, outcome and location (never a wall-clock time).
fn rows(stderr: &str) -> BTreeMap<String, Vec<Value>> {
    let mut out = BTreeMap::new();
    for line in stderr.lines() {
        let Some(payload) = line.strip_prefix("TRUST_JSON:") else { continue };
        let row: Value = serde_json::from_str(payload).expect("TRUST_JSON payload is JSON");
        if row["type"] != "function_result" {
            continue;
        }
        let function = row["function"].as_str().expect("a row names its function").to_string();
        let results = row["results"]
            .as_array()
            .expect("a function row has results")
            .iter()
            .map(|r| {
                serde_json::json!({
                    "kind": r["kind"],
                    "description": r["description"],
                    "outcome": r["outcome"],
                    "location": r["location"],
                })
            })
            .collect();
        out.insert(function, results);
    }
    out
}

fn main() {
    if std::env::var_os(TRUST_VANILLA_REAL_RUSTC_ENV).is_some() {
        // The upstream compiler does not know Trust's options.
        return;
    }
    let rustc = PathBuf::from(rustc_path());
    let trustc = rustc.with_file_name(bin_name("trustc"));
    let trustc = if trustc.exists() { trustc } else { rustc };
    let session = format!("-Ztrust-verify-session={SESSION}");

    let o0 = build_dep(&trustc, "dep-o0", &["-Copt-level=0", session.as_str()]);
    let o2 = build_dep(&trustc, "dep-o2", &["-Copt-level=2", session.as_str()]);
    let vanilla = build_dep(&trustc, "dep-vanilla-o2", &["-Copt-level=2"]);

    let at_o0 = check_subject(&trustc, &o0, "subject-o0");
    let at_o2 = check_subject(&trustc, &o2, "subject-o2");
    let at_vanilla = check_subject(&trustc, &vanilla, "subject-vanilla");

    for (label, stderr) in [("-Copt-level=0", &at_o0), ("-Copt-level=2", &at_o2)] {
        assert!(
            !stderr.contains(NOT_PIPELINE),
            "the dependency built in the proof session at {label} is the -O0 pipeline's: {stderr}"
        );
    }
    let session_rows = rows(&at_o0);
    for function in ["subject::sum", "subject::halves"] {
        assert!(session_rows.contains_key(function), "no rows for {function}: {at_o0}");
    }
    // The members ARE bundled in the session, so their encoded MIR is what the
    // rows rest on; otherwise this test would compare two declines. The bundle
    // census (`TRUST_BUNDLE_MEMBERS`) names each root's final members. The trace
    // names every candidate the foreign drain considers (`reason=mono-candidate`,
    // not a drop), so a drop is any OTHER reason naming the callee.
    let members = [
        ("subject::sum", "session_dep::clamp_sum"),
        ("subject::halves", "session_dep::quarters"),
    ];
    for (label, stderr) in [("-Copt-level=0", &at_o0), ("-Copt-level=2", &at_o2)] {
        for (root, callee) in members {
            let member = format!("[BUNDLE_MEMBER] root={root} name={callee} def_path={callee}");
            assert!(
                stderr.lines().any(|line| line == member),
                "the session's {label} dependency member `{callee}` was not bundled: {stderr}"
            );
            let considered = format!("[BUNDLE_DROP] reason=mono-candidate callee={callee}");
            let dropped = stderr.lines().any(|line| {
                line.starts_with("[BUNDLE_DROP] ")
                    && line.ends_with(&format!(" callee={callee}"))
                    && line != considered
            });
            assert!(
                !dropped,
                "the session's {label} dependency member `{callee}` was dropped: {stderr}"
            );
        }
    }
    assert_eq!(
        session_rows,
        rows(&at_o2),
        "the dependency's -Copt-level moved the verified dependent's rows inside a proof session"
    );

    for callee in ["session_dep::clamp_sum", "session_dep::quarters"] {
        assert!(
            at_vanilla.contains(&format!("{NOT_PIPELINE} callee={callee}")),
            "a vanilla -O2 dependency's `{callee}` was not declined for its MIR pipeline: \
             {at_vanilla}"
        );
    }
    assert_ne!(
        session_rows,
        rows(&at_vanilla),
        "declining the vanilla dependency's bodies must change the dependent's rows"
    );
}
