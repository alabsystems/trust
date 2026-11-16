//! REAL-MIR pin: a lossless std conversion between primitive integers keeps its
//! argument's value (TRUST-09 triage).
//!
//! # What was wrong
//!
//! Triaging the strict-lane failures of ordinary registry crates, a table lookup
//! `TABLE[usize::from(byte)]` over a `[u8; 256]` was reported
//!
//! ```text
//! [bounds] FAILED (ay-in-process); counterexample: … (the index is 256)
//! ```
//!
//! while `TABLE[byte as usize]` proved. `usize::from(byte)` is the call
//! `<usize as core::convert::From<u8>>::from`, whose destination was havoc'd;
//! every std `From`/`Into` between primitive integers is lossless and no other
//! crate may implement one, so the index is `byte`, at most 255.
//! `semantic_guard` now states `dest == arg` for exactly those calls
//! (`call_facts::is_std_int_from_into_call`).
//!
//! # The matrix
//!
//! | fixture | expectation |
//! |---|---|
//! | `rank_from` (`RANK[usize::from(byte)]`, `byte: u8`) | `[bounds]` not REFUTED |
//! | `rank_from_u16` (`RANK[usize::from(x)]`, `x: u16`) | `[bounds]` REFUTED — index 256..65535 is real |
//!
//! # Fixtures
//!
//! `tests/fixtures/int_from_*_mir.json` are the compiler's own extraction of the
//! source below, captured with
//!
//! ```text
//! trustc --edition 2021 --crate-type lib -Ztrust-policy=advisory \
//!        -Ztrust-dump=mir-only:<dir> int_from.rs
//! ```
//!
//! ```text
//! pub const RANK: [u8; 256] = [0; 256];
//! pub fn rank_from(byte: u8) -> u8 { RANK[usize::from(byte)] }
//! pub fn rank_from_u16(x: u16) -> u8 { RANK[usize::from(x)] }
//! ```
//!
//! The table is a `const`, as memchr's `RANK` is: that is the shape whose row was
//! REFUTED. With the table as a `&[u8; 256]` parameter the unfixed generator emits
//! no `[bounds]` row at all (measured 2026-09-24), so that shape would pin the
//! modelled conversion and not the false refutation. The `Into` spelling is
//! pinned on the recognizer (`generate/ord_method_tests.rs`).
use trust_types::{VcKind, VerifiableFunction, VerificationResult};

#[path = "support/test_router.rs"]
mod test_router;

/// Stack for the generation/solver thread; real extracted MIR carries deep
/// recursive `Formula` walks (the same allowance the other realmir files make).
const SOLVER_STACK_BYTES: usize = 64 * 1024 * 1024;

fn load(name: &str) -> VerifiableFunction {
    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/fixtures/int_from_");
    let text = std::fs::read_to_string(format!("{path}{name}_mir.json"))
        .unwrap_or_else(|e| panic!("fixture `{name}` must be readable: {e}"));
    serde_json::from_str(&text).unwrap_or_else(|e| panic!("fixture `{name}` must deserialize: {e}"))
}

/// The verdict of every `[bounds]` row of `name`, each dispatched to the
/// deterministic in-process ay the bridge uses.
fn bounds_rows(name: &str) -> Vec<String> {
    let func = load(name);
    std::thread::Builder::new()
        .stack_size(SOLVER_STACK_BYTES)
        .spawn(move || {
            let vcs = trust_vcgen::generate_vcs(&func);
            let router = test_router::deterministic_test_router();
            let mut rows = Vec::new();
            for vc in &vcs {
                if !matches!(vc.kind, VcKind::IndexOutOfBounds) {
                    continue;
                }
                let verdict = match router
                    .verify_all(std::slice::from_ref(vc))
                    .into_iter()
                    .next()
                    .expect("one verdict per VC")
                    .1
                {
                    VerificationResult::Proved { .. } => "PROVED".to_string(),
                    VerificationResult::Failed { .. } => "REFUTED".to_string(),
                    other => format!("{other:?}").chars().take(24).collect(),
                };
                rows.push(verdict);
            }
            rows
        })
        .expect("spawn analysis thread")
        .join()
        .expect("analysis thread must not panic")
}

#[test]
fn a_table_lookup_through_usize_from_u8_is_not_refuted() {
    let rows = bounds_rows("rank_from");
    assert!(!rows.is_empty(), "the fixture must produce a `[bounds]` row");
    assert!(
        rows.iter().all(|v| v != "REFUTED"),
        "`usize::from(byte)` is at most 255 < 256; a refutation is a counterexample over \
         a havocked lossless conversion: {rows:?}"
    );
}

#[test]
fn a_real_out_of_bounds_index_through_usize_from_u16_stays_refuted() {
    let rows = bounds_rows("rank_from_u16");
    assert!(
        rows.iter().any(|v| v == "REFUTED"),
        "`usize::from(x)` for `x: u16` reaches 65535 >= 256; this must stay refuted: {rows:?}"
    );
}
