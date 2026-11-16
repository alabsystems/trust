//! REAL-MIR pin: the `<[T]>::get` Some-index bound through the `?` operator.
//!
//! `slice.get(i)` returning `Some` implies `i < slice.len()`
//! (`guards::slice_get_some_index_bound_definitions`). The lane used to seed the
//! fact only when `get`'s direct target switched on the `Option`; the `?` spelling
//! puts core's `Try::branch` between them, so `let c = *b.get(i)?; i + 1` and the
//! a3d_wire `Parser::bump` shape (`*self.b.get(self.i)?; self.i += 1`) refuted the
//! increment at `i = usize::MAX`. The `Continue` arm of `branch` is reached only
//! from `Some`, and now carries the fact.
//!
//! # Fixtures
//!
//! `tests/fixtures/slice_get_try_*_mir.json`, the stage-1 compiler's extraction
//! (`trustc --edition 2021 --crate-type lib -Ztrust-verify=on -Ztrust-dump=mir:<dir>`) of
//!
//! ```text
//! pub struct P<'a> { pub b: &'a [u8], pub i: usize }
//! impl P<'_> {
//!     pub fn bump(&mut self) -> Option<u8> {
//!         let c = *self.b.get(self.i)?;
//!         self.i += 1;
//!         Some(c)
//!     }
//! }
//! pub fn local_get_q(b: &[u8], i: usize) -> Option<usize> {
//!     let _c = b.get(i)?;
//!     Some(i + 1)
//! }
//! ```
//!
//! Both `Add` rows were FAILED with `i = 18446744073709551615` on that stage 1.
//!
//! `slice_get_try_join_{match,try}_mir.json` are the same compiler's extraction of
//!
//! ```text
//! pub fn join_get(c: bool, a: &[u8], b: &[u8], i: usize, j: usize) -> u8 {
//!     let o = if c { a.get(i) } else { b.get(j) };
//!     match o { Some(_) => a[i], None => 0 }
//! }
//! pub fn join_get_q(c: bool, a: &[u8], b: &[u8], i: usize, j: usize) -> Option<u8> {
//!     let _x = if c { a.get(i) } else { b.get(j) }?;
//!     Some(a[i])
//! }
//! ```
//!
//! Both `get` calls target ONE switch block, so the lane seeded `i < len(a)` AND
//! `j < len(b)` at the `Some` arm and `a[i]` PROVED at -O0 — a false proof
//! (`c = false, a = [], b = [1]` panics). Every hop block must now be entered only
//! from the previous hop.
//!
//! `slice_get_try_dup_target_mir.json` (VARIANT-ARM-DUP-EDGE-1, 2026-10-06) is the
//! extraction, by a stage 1 reporting `0c4b132ee` (an ancestor of `origin/main`), of
//!
//! ```text
//! pub fn dup_target(a: &[u8], i: usize) -> u8 {
//!     match a.get(i) { Some(_) => {}, None => {} }
//!     a[i]
//! }
//! ```
//!
//! rustc -O0 lowers the match to `switchInt(d) -> [0: bb3, 1: bb3, otherwise: bb2]`.
//! The predecessor relation deduplicated the two edges, so `bb3` — which `None` also
//! enters — counted as the `Some` arm, was seeded `i < len(a)`, and `a[i]` PROVED on
//! that stage 1 (`2 proved, 0 failed`; `a = [], i = 0` panics). The arm must now be
//! the only one of the switch's edges into it.
use trust_types::{VcKind, VerifiableFunction, VerificationResult};

#[path = "support/test_router.rs"]
mod test_router;

const SOLVER_STACK_BYTES: usize = 64 * 1024 * 1024;

fn load(name: &str) -> serde_json::Value {
    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/fixtures/slice_get_try_");
    let text = std::fs::read_to_string(format!("{path}{name}_mir.json"))
        .unwrap_or_else(|e| panic!("fixture `{name}` must be readable: {e}"));
    serde_json::from_str(&text).unwrap_or_else(|e| panic!("fixture `{name}` must parse: {e}"))
}

/// The verdicts of every `Add` overflow row of the fixture.
fn add_rows(json: serde_json::Value) -> Vec<String> {
    rows_of(json, |kind| matches!(kind, VcKind::ArithmeticOverflow { .. }))
}

/// The verdicts of every index/slice bounds row of the fixture.
fn bounds_rows(json: serde_json::Value) -> Vec<String> {
    rows_of(json, |kind| matches!(kind, VcKind::IndexOutOfBounds | VcKind::SliceBoundsCheck))
}

fn rows_of(json: serde_json::Value, keep: fn(&VcKind) -> bool) -> Vec<String> {
    let func: VerifiableFunction = serde_json::from_value(json).expect("fixture must deserialize");
    std::thread::Builder::new()
        .stack_size(SOLVER_STACK_BYTES)
        .spawn(move || {
            let vcs = trust_vcgen::generate_vcs(&func);
            let router = test_router::deterministic_test_router();
            vcs.iter()
                .filter(|vc| keep(&vc.kind))
                .map(|vc| {
                    match router
                        .verify_all(std::slice::from_ref(vc))
                        .into_iter()
                        .next()
                        .expect("one verdict per VC")
                        .1
                    {
                        VerificationResult::Proved { .. } => "PROVED".to_string(),
                        VerificationResult::Failed { .. } => "REFUTED".to_string(),
                        other => format!("{other:?}").chars().take(24).collect(),
                    }
                })
                .collect()
        })
        .expect("spawn analysis thread")
        .join()
        .expect("analysis thread must not panic")
}

fn branch_call(json: &mut serde_json::Value) -> &mut serde_json::Value {
    json["body"]["blocks"]
        .as_array_mut()
        .expect("blocks")
        .iter_mut()
        .find_map(|b| {
            let call = b["terminator"].get_mut("Call")?;
            call["func"].as_str()?.contains("Try>::branch").then_some(call)
        })
        .expect("a Try::branch call")
}

#[test]
fn the_question_mark_spelling_proves_the_increment() {
    for name in ["local", "field"] {
        assert_eq!(add_rows(load(name)), ["PROVED"], "{name}");
    }
}

/// An unauthenticated `branch` (no `TryBranch` tag, or not the real sysroot)
/// carries nothing.
#[test]
fn an_unauthenticated_branch_carries_nothing() {
    for name in ["local", "field"] {
        let mut json = load(name);
        branch_call(&mut json)["callee_key"].as_object_mut().expect("key").remove("sysroot_item");
        assert_eq!(add_rows(json), ["REFUTED"], "{name}: untagged");
        let mut json = load(name);
        branch_call(&mut json)["callee_key"]["krate_is_real_sysroot"] = false.into();
        assert_eq!(add_rows(json), ["REFUTED"], "{name}: not the sysroot");
    }
}

/// The fact rides the `Continue` arm only: with the switch's arms swapped, the
/// increment sits on the `Break` (None) arm and must refute.
#[test]
fn the_break_arm_learns_nothing() {
    let mut json = load("local");
    let branch_target = branch_call(&mut json)["target"].as_u64().expect("target") as usize;
    let switch = json["body"]["blocks"][branch_target]["terminator"]
        .get_mut("SwitchInt")
        .expect("the branch target switches");
    let targets = switch["targets"].as_array_mut().expect("targets");
    let (a, b) = (targets[0][1].clone(), targets[1][1].clone());
    targets[0][1] = b;
    targets[1][1] = a;
    assert_eq!(add_rows(json), ["REFUTED"]);
}

/// Two `get` calls joining into ONE switch: the `Some` arm learns neither bound.
#[test]
fn a_shared_switch_block_learns_no_bound() {
    for name in ["join_match", "join_try"] {
        let rows = bounds_rows(load(name));
        assert!(!rows.is_empty() && rows.iter().all(|v| v == "REFUTED"), "{name}: {rows:?}");
    }
}

fn dup_switch(json: &mut serde_json::Value) -> &mut serde_json::Value {
    json["body"]["blocks"][1]["terminator"].get_mut("SwitchInt").expect("bb1 switches on the tag")
}

/// VARIANT-ARM-DUP-EDGE-1: `Some` and `None` both reach the join `bb3`, so `bb3` learns
/// no bound and `a[i]` refutes. The `Some`-only rails show the gate is the cause: with
/// `None` routed to the unreachable block the join IS the `Some` arm and proves, and
/// with `bb3` the `Some` target AND the `otherwise` target it refutes again (fail-closed:
/// the gate never reasons about which tags are inhabited).
#[test]
fn a_join_both_variants_reach_learns_no_bound() {
    let json = load("dup_target");
    assert_eq!(
        json["body"]["blocks"][1]["terminator"]["SwitchInt"]["targets"],
        serde_json::json!([[0, 3], [1, 3]]),
        "the fixture is rustc's duplicate-target lowering"
    );
    assert_eq!(json["body"]["blocks"][1]["terminator"]["SwitchInt"]["otherwise"], 2);
    assert_eq!(bounds_rows(json), ["REFUTED"], "both variants reach bb3");

    let mut some_only = load("dup_target");
    dup_switch(&mut some_only)["targets"] = serde_json::json!([[0, 2], [1, 3]]);
    assert_eq!(bounds_rows(some_only), ["PROVED"], "bb3 is the Some arm alone");

    let mut some_and_otherwise = load("dup_target");
    let sw = dup_switch(&mut some_and_otherwise);
    sw["targets"] = serde_json::json!([[0, 2], [1, 3]]);
    sw["otherwise"] = 3.into();
    sw["exhaustive_enum_unreachable"] = false.into();
    assert_eq!(bounds_rows(some_and_otherwise), ["REFUTED"], "otherwise also enters bb3");
}
