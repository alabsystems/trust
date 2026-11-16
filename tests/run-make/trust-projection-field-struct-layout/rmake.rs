//! fix10/core-refusals (L1, L3): a local struct whose field is a MONOMORPHIC associated-type
//! projection, or which reaches a local ADT under a fn-pointer binder, gets its layout, so a
//! body whose signature names it is no longer refused as "signature reaches a layout-less
//! struct".
//!
//! The #48 layout funnel (`trust_mir_extract::ctfe_reentrancy::every_reached_type`) declined
//! both: `Atomicish<u8>`'s field `UnsafeCell<<u8 as Prim>::Storage>` carries an alias flag, and
//! `Fm<'^0>` reached inside `fn(&mut Fm<'_>)` was instantiated with an escaping bound region.
//! In `core` these are `Atomic<T>` (L1) and `NonNull<fmt::rt::Argument<'_>>` (L3). The funnel
//! now reads what the selected impl WROTE for a monomorphic projection when that value carries
//! no alias (no opaque, no projection, no unevaluated constant) and the selection is over types
//! that themselves pass the funnel, and erases free regions before instantiating fields.
//!
//! Measured on the pre-change compiler (stage 1 of `825437bfeb`) with these flags: `new_u8`,
//! `by_value` and `h` were refused as "signature reaches a layout-less struct". The controls pin
//! the declines that keep the funnel's argument: `by_value_call` (an impl value whose
//! unevaluated constant calls a const fn) stays refused before or during splicing, and the opaque's
//! defining scope compiles at all (no E0391) — the compile itself is the check. fix11 (L2):
//! `by_value_const`, the decline control until then, now splices — its constant's whole CTFE
//! closure is leaf (a literal), which the funnel evaluates.

use run_make_support::{cmd, rfs, rustc_path, serde_json};

// OpaqueAnalysis can refuse the non-leaf RHS during THIR type mapping, before
// a lowered body exists. Pin that exact producer provenance, not an arbitrary
// unsupported row. Only the compiler's four-digit crate hash is incidental.
fn is_early_call_projection_refusal(row: &serde_json::Value) -> bool {
    let Some(details) = row["unsupported_details"].as_object() else { return false };
    let Some(detail) = details.get("Ty").and_then(|v| v.as_array()) else { return false };
    let projection = detail.first().and_then(|v| v.as_str()).and_then(|v| {
        v.strip_prefix(
            "Alias(No, Alias { kind: Projection { def_id: DefId(0:6 ~ projection_field[",
        )
        .and_then(|v| v.strip_suffix(
            "]::Prim::Storage) }, args: [i16], .. })",
        ))
    });
    row["def_path"] == "by_value_call"
        && row["kind"] == "fn"
        && row["lowered"] == false
        && row["symbolic"] == false
        && row["spliced"] == false
        && row.get("func_id") == Some(&serde_json::Value::Null)
        && row.get("splice_refusal") == Some(&serde_json::Value::Null)
        && row["unsupported"] == serde_json::json!([["Ty", 2]])
        && row["collect_primary"] == serde_json::json!([["Ty", 2]])
        && row["collect_cascade"] == serde_json::json!([])
        && details.len() == 1
        && detail.len() == 1
        && projection.is_some_and(|hash| {
            hash.len() == 4 && hash.bytes().all(|b| b.is_ascii_hexdigit())
        })
}

fn check_early_refusal_controls() {
    let projection = "Alias(No, Alias { kind: Projection { def_id: DefId(0:6 ~ projection_field[6ee6]::Prim::Storage) }, args: [i16], .. })";
    let row = serde_json::json!({
        "def_path": "by_value_call", "kind": "fn", "lowered": false,
        "symbolic": false, "spliced": false, "func_id": null, "splice_refusal": null,
        "unsupported": [["Ty", 2]], "collect_primary": [["Ty", 2]], "collect_cascade": [],
        "unsupported_details": {"Ty": [projection]},
    });
    assert!(is_early_call_projection_refusal(&row));
    for (pointer, replacement) in [
        ("/def_path", serde_json::json!("other")),
        ("/kind", serde_json::json!("closure")),
        ("/lowered", serde_json::json!(true)),
        ("/symbolic", serde_json::json!(true)),
        ("/spliced", serde_json::json!(true)),
        ("/func_id", serde_json::json!(0)),
        ("/splice_refusal", serde_json::json!("Splice(signature reaches a layout-less struct)")),
        ("/unsupported", serde_json::json!([["Expr", 2]])),
        ("/unsupported", serde_json::json!([["Ty", 1]])),
        ("/unsupported", serde_json::json!([["Ty", 3]])),
        ("/unsupported", serde_json::json!([["Ty", 2], ["Expr", 1]])),
        ("/collect_primary", serde_json::json!([["Ty", 1]])),
        ("/collect_cascade", serde_json::json!([["Ty", 1]])),
        ("/unsupported_details", serde_json::json!({"Ty": [projection], "Expr": []})),
        ("/unsupported_details/Ty", serde_json::json!([projection, projection])),
    ] {
        let mut wrong = row.clone();
        *wrong.pointer_mut(pointer).unwrap() = replacement;
        assert!(!is_early_call_projection_refusal(&wrong), "accepted {pointer}: {wrong}");
    }
    for wrong in [
        projection.replace("[i16]", "[u16]"),
        projection.replace("::Prim::Storage", "::Other::Storage"),
        projection.replace("::Prim::Storage", "::Prim::Other"),
        projection.replace("projection_field[", "other_crate["),
        projection.replace("Projection", "Opaque"),
        projection.replace("6ee6", "not-a-hash"),
        format!("unrelated {projection}"),
        format!("{projection} unrelated"),
    ] {
        let mut wrong_row = row.clone();
        wrong_row["unsupported_details"]["Ty"][0] = serde_json::json!(wrong);
        assert!(!is_early_call_projection_refusal(&wrong_row), "accepted {wrong_row}");
    }
    for missing in ["func_id", "splice_refusal"] {
        let mut wrong = row.clone();
        wrong.as_object_mut().unwrap().remove(missing);
        assert!(!is_early_call_projection_refusal(&wrong), "accepted missing {missing}");
    }
}

fn main() {
    if std::env::var_os("__COMPILETEST_TRUST_VANILLA_REAL_RUSTC").is_some() {
        return; // Stock rustc has no Trust-IR artifact interface.
    }
    check_early_refusal_controls();
    cmd(rustc_path())
        .args([
            "projection_field.rs",
            "--edition=2021",
            "--crate-type=lib",
            "--crate-name=projection_field",
            "--emit=metadata",
            "-Zthreads=1",
            "-Ztrust-verify=off",
            "-Ztrust-ir-lower=on",
            "-Ztrust-dump=ir:ir",
        ])
        .env("TRUST_COVERAGE_DETAIL_CAP", "0")
        .run();
    let report: serde_json::Value =
        serde_json::from_slice(&rfs::read("ir/projection_field.coverage.json")).unwrap();
    let rows = report["bodies"].as_array().unwrap();
    let row = |name: &str| {
        let found: Vec<_> = rows.iter().filter(|r| r["def_path"] == name).collect();
        assert_eq!(found.len(), 1, "missing/duplicate body {name}");
        found[0].clone()
    };
    const LAYOUT_LESS: &str = "Splice(signature reaches a layout-less struct)";
    for name in ["new_u8", "by_value", "h", "by_value_const"] {
        let r = row(name);
        assert_ne!(r["splice_refusal"], LAYOUT_LESS, "{name}: {r}");
        assert_eq!(r["spliced"], true, "{name} must splice: {r}");
    }
    let r = row("by_value_call");
    if r["lowered"] == true {
        assert_eq!(r["splice_refusal"], LAYOUT_LESS, "a const-fn-call constant in the impl value: {r}");
    } else {
        assert!(
            is_early_call_projection_refusal(&r),
            "the i16 Prim::Storage const-fn-call RHS must be refused before lowering: {r}",
        );
    }
}
