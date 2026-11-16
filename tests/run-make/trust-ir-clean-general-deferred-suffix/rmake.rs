//! CLEAN-GENERAL-DEFERRED-1: the general Clean lane's recorded reason for a `def` in the
//! DEFERRED island suffix must say why it is skipped, not report a compiler
//! defect.
//!
//! The lane (`collect_general_clean_ir`, compiler/rustc_mir_transform/src/
//! clean_origin_ir.rs) compiles from `clean_crate_environment`, which holds only
//! the islands before the first that names `trust_import_*`
//! (E9-DEFERRED-SUFFIX-ENV-1). It took names from every island, so each `def`
//! of the suffix missed that environment and its row in
//! `clean_origin.general[]` of the coverage sidecar read "declared in an island
//! but absent from the kernel environment — report this". The suffix's
//! declarations are kernel-checked after program admission (the stderr note
//! pinned below); nothing is missing.
//!
//! Pins:
//!  * the two deferred defs are `skipped` with the `deferred-island:` reason
//!    and its option, and no row anywhere carries the "absent … report this"
//!    text. `suffixRank`'s island names no `trust_import_*` itself, so the row
//!    follows the authored-suffix rule, not the island's own text;
//!  * CONTROL, the same shape in the prefix: `prefixRank` compiles, so the lane
//!    ran and its prefix lookup works;
//!  * the deferred theorem stays `not-computational`: the proof-side kind
//!    decides before placement;
//!  * the suffix really is deferred and kernel-checked: the compiler's
//!    post-admission note names each deferred declaration.
//!
//! On the compiler before the fix the first pin fails: both deferred rows carry
//! the "absent from the kernel environment — report this" reason.

use std::path::Path;

use run_make_support::{rfs, rustc, serde_json};

const TRUST_NO_VERIFY_ENV: &str = "TRUST_NO_VERIFY";

/// `trust_check_deferred_island_suffix`'s note for an accepted deferred island.
const POST_ADMISSION_NOTE: &str = "Clean island kernel-checked after program admission";

/// Whether a post-admission note of `stderr` names `declaration`.
fn noted_after_admission(stderr: &str, declaration: &str) -> bool {
    stderr.lines().any(|line| line.contains(POST_ADMISSION_NOTE) && line.contains(declaration))
}

/// The option the deferred reason must carry (v7/D3: a refusal names its fix).
const DEFERRED_OPTION: &str = "Options: move the declaration into an island placed before the \
    first island that names `trust_import_*`";

fn main() {
    let dir = Path::new("emit-on");
    rfs::create_dir(&dir);
    let output = rustc()
        .input("foo.rs")
        .crate_type("lib")
        .emit("trust-ir")
        .out_dir(&dir)
        .arg("-Ztrust-verify=on")
        // Bootstrap may deauthorize its own nested compiler processes through
        // this inherited override; the recipe's explicit flag must win.
        .env_remove(TRUST_NO_VERIFY_ENV)
        .run();
    let stderr = output.stderr_utf8();

    // ── the partition is the compiler's: islands 2 and 3 are deferred ────────
    for name in ["firstKeeps", "namingRank", "suffixRank"] {
        assert!(
            noted_after_admission(&stderr, name),
            "`{name}` must be registered by the post-admission suffix check:\n{stderr}"
        );
    }
    assert!(
        !noted_after_admission(&stderr, "prefixRank"),
        "`prefixRank` is in the pre-admission prefix, never the deferred suffix:\n{stderr}"
    );

    let coverage = rfs::read_to_string(dir.join("foo.trust-ir.coverage.json"));
    let json: serde_json::Value =
        serde_json::from_str(&coverage).expect("coverage sidecar must be valid JSON");
    assert_eq!(
        json["clean_origin"]["recorded"], true,
        "clean_origin section must record under verification:\n{coverage}"
    );
    let general =
        json["clean_origin"]["general"].as_array().expect("clean_origin.general array").clone();
    let row = |name: &str| -> serde_json::Value {
        let rows: Vec<&serde_json::Value> =
            general.iter().filter(|row| row["clean_name"] == name).collect();
        assert_eq!(rows.len(), 1, "`{name}` must have exactly one general row:\n{coverage}");
        rows[0].clone()
    };

    // ── CONTROL: the same shape in the prefix compiles ───────────────────────
    let prefix = row("prefixRank");
    assert_eq!(prefix["tier"], "general", "{prefix}");
    assert_eq!(
        prefix["disposition"], "compiled",
        "the prefix twin must compile, or the deferred rows below measure nothing: {prefix}"
    );

    // ── the proof-side kind decides before placement ─────────────────────────
    let theorem = row("firstKeeps");
    assert_eq!(theorem["disposition"], "not-computational", "{theorem}");
    assert!(theorem.get("reason").is_none(), "a theorem row carries no skip reason: {theorem}");

    // ── the fix: a deferred def is skipped with its own, true reason ─────────
    for name in ["namingRank", "suffixRank"] {
        let deferred = row(name);
        assert_eq!(deferred["tier"], "general", "{deferred}");
        assert_eq!(deferred["disposition"], "skipped", "{name} is not compiled yet: {deferred}");
        let reason = deferred["reason"].as_str().expect("a skipped row carries a string reason");
        assert!(
            reason.starts_with("deferred-island: "),
            "{name} must be skipped by placement, not by a failed lookup: {reason}"
        );
        assert!(reason.contains(DEFERRED_OPTION), "{name}'s reason must name its fix: {reason}");
        assert!(
            !reason.contains("report this") && !reason.contains("absent from the kernel"),
            "{name}'s reason must not claim a compiler defect: {reason}"
        );
    }
    assert!(
        !coverage.contains("absent from the kernel environment"),
        "no general row may report a missing declaration here:\n{coverage}"
    );
}
