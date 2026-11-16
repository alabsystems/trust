//! Trust (R8-SEAM, `docs/DECISION_QUEUE.md`, taken 2026-10-05): the crate-seam differential
//! computes from ONE working copy of the assembled crate module what it computed from copies of
//! the WHOLE module — one per UC probe sample leg (`row1_uc_probe`), one per drop-bearing closure
//! (`module_without_drops`) and one per pointer-lane comparison
//! (`differential::build_pointee_wrapper`), which measured on `core` were most of the direct
//! producer's cost (docs/design/2026-10-02-step2-inc6-trust-ir-in-metadata.md, step 6.0).
//!
//! The TEST-ONLY `-Ztrust-ir-seam-reference=<report>` option (unset in every real build) runs the
//! pre-R8-SEAM seam, kept verbatim in `crates/trust-thir-lower/src/crate_module/seam_reference.rs`,
//! over the pre-R8-SEAM differential, kept verbatim in
//! `crates/trust-thir-lower/src/differential/compare_entries_reference.rs` — the old code of BOTH
//! frozen files — beside the live one at crate finalization, compares every verdict and every
//! traced UC probe outcome field for field, checks the working copy is the assembled module again
//! after the pass, and fails finalization on any difference. The report says what was compared.
//!
//! This subject exercises the sites real code reaches: a body whose only callee is a bodyless
//! `extern "C"` function (the UC probe's sample legs, substituted as block patches) and a
//! call-bearing body that reads a `&u32` parameter (the pointer lane's materialized-referent
//! wrappers, appended to the working copy and removed). Each must be reached, or the check is
//! vacuous. The third site, the drop removal, is reached by no subject measured: `drops` below
//! stops at step 7 (`oracle-panic-model`: its oracle bundle carries an `Assert(const false)`)
//! before any comparison, and all of `core` makes 0 drop-bearing comparisons; `crate_module/seam_scratch_tests.rs` pins that lane against
//! `module_without_drops` directly. `drops` stays in the subject so a change that lets it through
//! is compared like the rest. The census, effect-conservation and generic-instance fixtures run
//! the same check on their own subjects.
//@ ignore-cross-compile

use run_make_support::{rfs, rustc};

const LANES: &str = r#"#![crate_type = "lib"]
unsafe extern "C" {
    fn ext_scalar(x: u32) -> u32;
}

/// The UC probe: the closure's one callee is bodyless, with scalar parameter and return.
pub fn uc_caller(x: u32) -> u32 {
    unsafe { ext_scalar(x) ^ 1 }
}

pub struct Guard(pub u32);

impl Drop for Guard {
    fn drop(&mut self) {}
}

/// The drop removal's subject: the body drops a `Guard`, which defers it to the seam (where it
/// is skipped at step 7 today; see the module docs).
pub fn drops(x: u32) -> u32 {
    let g = Guard(x);
    g.0 ^ 3
}

#[inline(never)]
pub fn inner(x: u32) -> u32 {
    x ^ 5
}

/// The pointer lane: a call-bearing body whose one parameter is read through a sole load.
pub fn ptr_caller(x: &u32) -> u32 {
    inner(*x)
}
"#;

/// Compile `file` with the direct producer on and the cross-check hook; return the report after
/// checking the compile raised no cross-check error and the report found no difference.
fn cross_check(file: &str, tag: &str) -> String {
    let report = format!("seam-reference-{tag}.txt");
    let out = rustc()
        .input(file)
        .crate_type("lib")
        .edition("2021")
        .arg("-Copt-level=0")
        .arg("-Ztrust-verify=off")
        .arg("-Ztrust-ir-lower")
        .arg("--emit=metadata")
        .out_dir(format!("out-{tag}"))
        .arg(format!("-Ztrust-ir-seam-reference={report}"))
        .run();
    let stderr = out.stderr_utf8();
    assert!(!stderr.contains("seam cross-check"), "{tag}: the seams differ:\n{stderr}");
    let text = rfs::read_to_string(&report);
    for line in ["differences 0", "restored true"] {
        assert!(text.lines().any(|l| l == line), "{tag}: the report lacks `{line}`:\n{text}");
    }
    text
}

/// The count a report gives for `key` (`key <n>` on its own line).
fn count(text: &str, key: &str) -> usize {
    text.lines()
        .find_map(|l| l.strip_prefix(&format!("{key} ")))
        .and_then(|n| n.parse().ok())
        .unwrap_or_else(|| panic!("the report has no `{key}`:\n{text}"))
}

fn lanes() {
    rfs::write("lanes.rs", LANES);
    let text = cross_check("lanes.rs", "lanes");
    assert!(count(&text, "verdicts") >= 3, "every deferred body has a verdict:\n{text}");
    assert_eq!(count(&text, "copies"), 1, "one working copy for the whole pass:\n{text}");
    for lane in ["uc-legs", "wrapped"] {
        assert!(count(&text, lane) > 0, "the subject must reach `{lane}`:\n{text}");
    }
}

fn main() {
    lanes();
}

/// The recipe under libtest as well as compiletest (the frozen-file waiver cites it).
#[test]
fn the_one_working_copy_seam_is_the_reference_seam_on_every_lane() {
    main();
}
