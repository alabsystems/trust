//! REAL-MIR pin: monotone-counter bounds (`callee_summaries::local_value_monotone_bounds`).
//!
//! `tests/fixtures/monotone_counter_tables_mir.json` is the stage-1 compiler's
//! extraction (`trustc --edition 2021 --crate-type lib -Ztrust-verify=on
//! -Ztrust-dump=mir:<dir>`) of astream_wire's `crc32_tables` shape:
//!
//! ```text
//! pub const fn tables() -> [u32; 8] {
//!     let mut t = [0u32; 8]; let mut k = 1usize;
//!     while k < 8 { t[k] = t[k - 1] ^ 1; k += 1; }
//!     t
//! }
//! ```
//!
//! `k`'s definitions are `1` and the `.0` of a checked `k + 1` whose block ends in
//! rustc's overflow `Assert`, so `k >= 1` at every read and `k - 1` cannot underflow
//! (it refuted with `k = 0` before). The negative control removes that `Assert`: an
//! unguarded checked tuple is how `overflowing_add` lowers once inlined, and its `.0`
//! wraps, so the bound must not be claimed and `k - 1` must refute again.
use trust_types::{VcKind, VerifiableFunction, VerificationResult};

#[path = "support/test_router.rs"]
mod test_router;

const SOLVER_STACK_BYTES: usize = 64 * 1024 * 1024;

fn load() -> serde_json::Value {
    let path =
        concat!(env!("CARGO_MANIFEST_DIR"), "/tests/fixtures/monotone_counter_tables_mir.json");
    serde_json::from_str(&std::fs::read_to_string(path).expect("fixture")).expect("parse")
}

/// The verdict of the `Sub` overflow row.
fn sub_rows(json: serde_json::Value) -> Vec<String> {
    let func: VerifiableFunction = serde_json::from_value(json).expect("deserialize");
    std::thread::Builder::new()
        .stack_size(SOLVER_STACK_BYTES)
        .spawn(move || {
            let vcs = trust_vcgen::generate_vcs(&func);
            let router = test_router::deterministic_test_router();
            vcs.iter()
                .filter(|vc| {
                    matches!(&vc.kind, VcKind::ArithmeticOverflow { op, .. } if format!("{op:?}") == "Sub")
                })
                .map(|vc| match router.verify_all(std::slice::from_ref(vc)).remove(0).1 {
                    VerificationResult::Proved { .. } => "PROVED".to_string(),
                    VerificationResult::Failed { .. } => "REFUTED".to_string(),
                    other => format!("{other:?}").chars().take(24).collect(),
                })
                .collect()
        })
        .expect("spawn")
        .join()
        .expect("join")
}

#[test]
fn the_counter_is_at_least_its_initial_value() {
    assert_eq!(sub_rows(load()), ["PROVED"]);
}

/// Replace the overflow `Assert` that guards `k += 1` with a plain `Goto` to its
/// target: the checked tuple's `.0` may now wrap, so no lower bound.
#[test]
fn an_unguarded_checked_add_gives_no_bound() {
    let mut json = load();
    let blocks = json["body"]["blocks"].as_array_mut().expect("blocks");
    let mut patched = 0;
    for b in blocks.iter_mut() {
        let is_add_guard = b["stmts"].as_array().is_some_and(|stmts| {
            stmts
                .iter()
                .any(|s| s["Assign"]["rvalue"]["CheckedBinaryOp"][0].as_str() == Some("Add"))
        }) && b["terminator"].get("Assert").is_some();
        if is_add_guard {
            let target = b["terminator"]["Assert"]["target"].clone();
            b["terminator"] = serde_json::json!({ "Goto": target });
            patched += 1;
        }
    }
    assert_eq!(patched, 1, "exactly the `k += 1` guard is replaced");
    assert_eq!(sub_rows(json), ["REFUTED"]);
}
