//! REAL-MIR pin: STR_BYTES_POSITION_BOUND (docs/TCB.md). The `Some(i)` of
//! `s.bytes().position(..)` satisfies `i + 1 <= len(s)`, so `i + 1` cannot overflow;
//! it is NOT a char boundary, so a str range-slice on it stays unproved; and the
//! fact is guarded by the discriminant, so the `None` arm learns nothing.
//!
//! # Fixtures
//!
//! `tests/fixtures/str_bytes_position_*_mir.json` are the stage-1 compiler's own
//! extraction (with the `StrBytes` / `IteratorPosition` tags it now mints) of
//!
//! ```text
//! pub fn tail(rest: &str) -> &str {
//!     match rest.bytes().position(|b| b == b'/') {
//!         Some(i) => &rest[i + 1..],
//!         None => rest,
//!     }
//! }
//! pub fn plus_one(rest: &str) -> usize {
//!     match rest.bytes().position(|b| b == b'/') {
//!         Some(i) => i + 1,
//!         None => 0,
//!     }
//! }
//! pub fn none_arm(r: &str) -> u8 {
//!     match r.bytes().position(|b| b == b'/') {
//!         Some(_) => 0,
//!         None => r.as_bytes()[0],
//!     }
//! }
//! ```
//!
//! captured with `trustc --edition 2021 --crate-type lib -Ztrust-verify=on
//! -Ztrust-dump=mir:<dir> bp.rs`. Before the fact, `plus_one`'s and `tail`'s `Add`
//! rows were FAILED with `i = usize::MAX` (measured on that stage 1).
use trust_types::{BlockId, VcKind, VerifiableFunction, VerificationResult};
use trust_vcgen::VcgenContext;

#[path = "support/test_router.rs"]
mod test_router;

const SOLVER_STACK_BYTES: usize = 64 * 1024 * 1024;

fn load(name: &str) -> serde_json::Value {
    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/fixtures/str_bytes_position_");
    let text = std::fs::read_to_string(format!("{path}{name}_mir.json"))
        .unwrap_or_else(|e| panic!("fixture `{name}` must be readable: {e}"));
    serde_json::from_str(&text).unwrap_or_else(|e| panic!("fixture `{name}` must parse: {e}"))
}

fn func(json: serde_json::Value) -> VerifiableFunction {
    serde_json::from_value(json).expect("fixture must deserialize")
}

/// `(kind, verdict)` for every overflow and bounds row of `f`.
fn rows(f: VerifiableFunction) -> Vec<(String, String)> {
    rows_with(f, None)
}

/// [`rows`] under a `VcgenContext` (STR_BYTE_POSITION premises), when given.
fn rows_with(f: VerifiableFunction, context: Option<VcgenContext>) -> Vec<(String, String)> {
    std::thread::Builder::new()
        .stack_size(SOLVER_STACK_BYTES)
        .spawn(move || {
            let vcs = match &context {
                Some(context) => trust_vcgen::generate_vcs_with_context(&f, context),
                None => trust_vcgen::generate_vcs(&f),
            };
            let router = test_router::deterministic_test_router();
            let mut out = Vec::new();
            for vc in &vcs {
                let kind = match &vc.kind {
                    VcKind::ArithmeticOverflow { .. } => "overflow",
                    VcKind::IndexOutOfBounds | VcKind::SliceBoundsCheck => "bounds",
                    // Since the class-10 merge (RANGE-DECLINE, 2026-10-08) a str
                    // range-slice whose endpoint is not a credited char boundary is the
                    // declined `str-range-char-boundary-unmodeled` row (Unknown), and an
                    // unresolved range the declined `slice-range-*` row: still the
                    // range-slice's charge, never proved. It was a refutable
                    // `SliceBoundsCheck` on `Bool(true)`.
                    VcKind::UnsupportedMir { kind, .. }
                        if kind.starts_with("str-range-") || kind.starts_with("slice-range-") =>
                    {
                        "bounds"
                    }
                    _ => continue,
                };
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
                out.push((kind.to_string(), verdict));
            }
            out
        })
        .expect("spawn analysis thread")
        .join()
        .expect("analysis thread must not panic")
}

fn verdicts(rows: &[(String, String)], kind: &str) -> Vec<String> {
    rows.iter().filter(|(k, _)| k == kind).map(|(_, v)| v.clone()).collect()
}

/// Rewrite the callee key of every call whose rendered callee contains `needle`.
fn edit_call_key(
    json: &mut serde_json::Value,
    needle: &str,
    edit: impl Fn(&mut serde_json::Value),
) {
    let mut hit = false;
    for block in json["body"]["blocks"].as_array_mut().expect("blocks") {
        if let Some(call) = block["terminator"].get_mut("Call")
            && call["func"].as_str().is_some_and(|f| f.contains(needle))
        {
            edit(&mut call["callee_key"]);
            hit = true;
        }
    }
    assert!(hit, "no call to `{needle}` in the fixture");
}

#[test]
fn the_payload_plus_one_is_proved() {
    let rows = rows(func(load("plus_one")));
    assert_eq!(verdicts(&rows, "overflow"), ["PROVED"], "{rows:?}");
}

/// The bound proves `i + 1`, and the str range-slice on `i + 1` stays unproved:
/// a byte position is not a char boundary.
#[test]
fn the_tail_add_is_proved_and_its_str_slice_is_not() {
    let rows = rows(func(load("tail")));
    assert_eq!(verdicts(&rows, "overflow"), ["PROVED"], "{rows:?}");
    let bounds = verdicts(&rows, "bounds");
    assert!(!bounds.is_empty(), "the str range-slice row must exist: {rows:?}");
    assert!(bounds.iter().all(|v| v != "PROVED"), "no char-boundary credit: {rows:?}");
}

/// The vacuity rail: on the `None` arm of `r = ""` the index really panics.
#[test]
fn the_none_arm_learns_nothing() {
    let rows = rows(func(load("none_arm")));
    assert_eq!(verdicts(&rows, "bounds"), ["REFUTED"], "{rows:?}");
}

/// Impersonators: an unauthenticated `position` or `bytes` gives no fact.
#[test]
fn an_unauthenticated_callee_gives_no_fact() {
    for (needle, edit) in [
        (
            "position",
            (|k: &mut serde_json::Value| k["krate_is_real_sysroot"] = false.into()) as fn(&mut _),
        ),
        ("position", |k| {
            k.as_object_mut().expect("key").remove("sysroot_item");
        }),
        ("bytes", |k| k["krate_is_real_sysroot"] = false.into()),
        ("bytes", |k| {
            k.as_object_mut().expect("key").remove("sysroot_item");
        }),
        ("bytes", |k| *k = serde_json::Value::Null),
    ] {
        let mut json = load("plus_one");
        edit_call_key(&mut json, needle, edit);
        let rows = rows(func(json));
        assert_eq!(verdicts(&rows, "overflow"), ["REFUTED"], "{needle}: {rows:?}");
    }
}

/// A `SetDiscriminant` of the destination after the call (a second write) gives
/// no fact: the payload is no longer the call's.
#[test]
fn a_rewritten_destination_gives_no_fact() {
    let mut json = load("plus_one");
    let blocks = json["body"]["blocks"].as_array_mut().expect("blocks");
    let target = blocks
        .iter()
        .find_map(|b| {
            let call = b["terminator"].get("Call")?;
            call["func"].as_str()?.contains("position").then(|| call["target"].as_u64())?
        })
        .expect("the position call has a target") as usize;
    let span = blocks[target]["stmts"][0]["Assign"]["span"].clone();
    blocks[target]["stmts"].as_array_mut().expect("stmts").insert(
        0,
        serde_json::json!({"SetDiscriminant": {"place": {"local": 2, "projections": []}, "variant_index": 1, "span": span}}),
    );
    let rows = rows(func(json));
    assert_eq!(verdicts(&rows, "overflow"), ["REFUTED"], "{rows:?}");
}

/// STR_BYTE_POSITION: `{position call block: K}`, as the compiler installs it.
fn premise(owner: &str, k: u8) -> VcgenContext {
    VcgenContext::for_function(owner.to_string())
        .with_ascii_eq_bytes_position_calls([(BlockId(1), k)].into_iter().collect())
}

/// With the compiler's premise for the `position` call, `tail`'s str range-slice
/// `&rest[i + 1..]` proves: `i` is an exact one-byte ASCII match.
#[test]
fn the_premise_proves_the_tail_slice() {
    let f = func(load("tail"));
    let owner = f.def_path.clone();
    let rows = rows_with(f, Some(premise(&owner, b'/')));
    assert_eq!(verdicts(&rows, "overflow"), ["PROVED"], "{rows:?}");
    let bounds = verdicts(&rows, "bounds");
    assert!(!bounds.is_empty() && bounds.iter().all(|v| v == "PROVED"), "{rows:?}");
}

/// The premise is owner-checked and re-checked: another function's premise, an
/// empty map, and a non-ASCII `K` credit nothing.
#[test]
fn a_foreign_empty_or_non_ascii_premise_credits_nothing() {
    for context in [
        premise("bp::someone_else", b'/'),
        VcgenContext::for_function(func(load("tail")).def_path.clone()),
        premise(&func(load("tail")).def_path.clone(), 0xC3),
    ] {
        let rows = rows_with(func(load("tail")), Some(context));
        let bounds = verdicts(&rows, "bounds");
        assert!(bounds.iter().all(|v| v != "PROVED"), "{rows:?}");
    }
}
