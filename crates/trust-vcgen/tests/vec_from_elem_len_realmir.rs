//! REAL-MIR pin: VEC_FROM_ELEM_LEN (`generate::call_facts::vec_from_elem_len_facts`).
//!
//! `tests/fixtures/vec_from_elem_{idx,last}_mir.json` are the stage-1 compiler's extraction
//! (`trustc --edition 2021 --crate-type lib -Ztrust-verify=on -Ztrust-dump=mir:<dir>`) of
//!
//! ```text
//! pub fn idx(n: usize, i: usize) -> u8 { let v = vec![7u8; n]; if i < n { v[i] } else { 0 } }
//! pub fn last(n: usize) -> u8 { let v = vec![7u8; n]; if n > 0 { v[n - 1] } else { 0 } }
//! ```
//!
//! Both index rows were `[slice] FAILED` before: the row reads `v`'s length as the join
//! token `v#e_s0_t` (a later `Drop(v)` writes the descendant name `v*`), and nothing tied
//! it to `n`.
use trust_types::{VcKind, VerifiableFunction, VerificationResult};

#[path = "support/test_router.rs"]
mod test_router;

const SOLVER_STACK_BYTES: usize = 64 * 1024 * 1024;

fn load(name: &str) -> serde_json::Value {
    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/fixtures/vec_from_elem_");
    let text = std::fs::read_to_string(format!("{path}{name}_mir.json")).expect("fixture");
    serde_json::from_str(&text).expect("parse")
}

/// The verdicts of every index / slice bounds row.
fn bounds_rows(json: serde_json::Value) -> Vec<String> {
    let func: VerifiableFunction = serde_json::from_value(json).expect("deserialize");
    std::thread::Builder::new()
        .stack_size(SOLVER_STACK_BYTES)
        .spawn(move || {
            let vcs = trust_vcgen::generate_vcs(&func);
            let router = test_router::deterministic_test_router();
            vcs.iter()
                .filter(|vc| matches!(vc.kind, VcKind::IndexOutOfBounds | VcKind::SliceBoundsCheck))
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

fn from_elem_call(json: &mut serde_json::Value) -> &mut serde_json::Value {
    json["body"]["blocks"]
        .as_array_mut()
        .expect("blocks")
        .iter_mut()
        .find_map(|b| {
            let call = b["terminator"].get_mut("Call")?;
            call["func"].as_str()?.contains("from_elem").then_some(call)
        })
        .expect("a from_elem call")
}

#[test]
fn the_length_of_vec_from_elem_is_its_count() {
    for name in ["idx", "last"] {
        assert_eq!(bounds_rows(load(name)), ["PROVED"], "{name}");
    }
}

/// An untagged or non-sysroot `from_elem` gives no fact.
#[test]
fn an_unauthenticated_from_elem_gives_no_fact() {
    let mut json = load("idx");
    from_elem_call(&mut json)["callee_key"].as_object_mut().expect("key").remove("sysroot_item");
    assert_eq!(bounds_rows(json), ["REFUTED"]);
    let mut json = load("idx");
    from_elem_call(&mut json)["callee_key"]["krate_is_real_sysroot"] = false.into();
    assert_eq!(bounds_rows(json), ["REFUTED"]);
}

/// The fact is `len == n`, not more: weakening `idx`'s guard to `i <= n` must refute
/// (`i == n` is out of bounds).
#[test]
fn an_off_by_one_guard_still_refutes() {
    let mut json = load("idx");
    let mut patched = 0;
    for b in json["body"]["blocks"].as_array_mut().expect("blocks") {
        for s in b["stmts"].as_array_mut().expect("stmts") {
            if let Some(op) = s["Assign"]["rvalue"].get_mut("BinaryOp")
                && op[0].as_str() == Some("Lt")
            {
                op[0] = "Le".into();
                patched += 1;
            }
        }
    }
    assert_eq!(patched, 1, "exactly the `i < n` guard is weakened");
    assert_eq!(bounds_rows(json), ["REFUTED"]);
}
