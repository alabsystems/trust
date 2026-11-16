//! Keep opaque tuple payloads visible without extracting fields from a unit carrier.
//! This regression checks valid module assembly and controls that carry real fields;
//! it does not claim tuple-payload layout support or a refinement proof.
//!
//! Two fail-closed checks refuse a field read of an opaque payload. Each carrier body pins
//! the one field refusal that names it, and only that one:
//!
//!   * `Field(opaque carrier base)`: the `Field` arm's check keyed on the LOCAL (crystal
//!     U14, 891671eebef). An opaque match binds its payload binding to the fact-free carrier
//!     at the unit placeholder type, so a read through that local is refused before the
//!     operand is lowered, rebound or not. `scalar_payload` and `fat_payload` were refused
//!     before U14 too, under the value tag below; U14 only runs first. `joined_payload` and
//!     `havoc_payload` rebind the local (an `if` join parameter, a `for` havoc) to values the
//!     carrier ledger does not name. Before U14 both lowered to an `ExtractField` over `()`,
//!     final module validation rejected the module, and no coverage was published.
//!   * `Field(opaque aggregate carrier)`: `lower_field_aggregate`'s check keyed on the
//!     carrier VALUE (2350e94697b). `rebound_payload`'s `let alias = pair` is not a carrier
//!     local, so only the value ledger catches its read.
//!
//! Each refused arm also files `EnumMatch(opaque arm no value)`, the match's consequence of
//! the refused read; it predates U14 and is not what this recipe pins. Not pinned either: a
//! straight-line `pair = (7, 8); pair.1` lowered and spliced before U14 and is refused by it
//! now. That is an over-refusal, not an intended inventory row.

use std::collections::BTreeSet;
use std::path::PathBuf;

use run_make_support::{bin_name, cmd, rfs, rustc_path, serde_json};

fn main() {
    if std::env::var_os("__COMPILETEST_TRUST_VANILLA_REAL_RUSTC").is_some() {
        return;
    }
    let rustc = PathBuf::from(rustc_path());
    let trustc = rustc.with_file_name(bin_name("trustc"));
    let trustc = if trustc.exists() { trustc } else { rustc };
    for lane in ["off", "on"] {
        let mut compiler = cmd(&trustc);
        compiler
            .arg("fields.rs")
            .arg("--edition=2021")
            .arg("--crate-type=lib")
            .arg("--crate-name=fields")
            .arg("--emit=link")
            .arg("-Copt-level=3")
            .arg("-Cdebug-assertions=off")
            .arg("-Ztrust-verify=off")
            .arg("-Ztrust-policy=strict")
            .arg(format!("-Ztrust-ir-lower={lane}"))
            .arg("-o")
            .arg(format!("fields-{lane}.rlib"));
        if lane == "on" {
            compiler.arg("-Ztrust-dump=ir:fields-ir").arg("-Ztrust-ir-flip=yes");
        }
        compiler.run();
    }

    let coverage: serde_json::Value =
        serde_json::from_slice(&rfs::read("fields-ir/fields.coverage.json"))
            .expect("published coverage must be valid JSON");
    assert_eq!(coverage["schema"], "trust.thir-lower.crate-module.coverage.v2");
    assert_eq!(coverage["publication"]["commit_marker"], true);
    let bodies = coverage["bodies"].as_array().expect("complete body inventory");
    let expected = BTreeSet::from([
        "scalar_payload",
        "fat_payload",
        "rebound_payload",
        "struct_payload",
        "direct_tuple",
        "direct_struct",
        "joined_payload",
        "havoc_payload",
    ]);
    let actual = bodies
        .iter()
        .map(|body| body["def_path"].as_str().expect("body identity"))
        .collect::<BTreeSet<_>>();
    assert_eq!(actual, expected, "no missing or substituted body rows");
    assert_eq!(bodies.len(), expected.len(), "no duplicate body rows");
    assert_eq!(coverage["totals"]["bodies"].as_u64(), Some(expected.len() as u64));

    for body in bodies {
        let name = body["def_path"].as_str().expect("body identity");
        let unsupported = body["unsupported"].as_array().expect("unsupported inventory");
        let refusal = match name {
            "scalar_payload" | "fat_payload" | "joined_payload" | "havoc_payload" => {
                Some("Field(opaque carrier base)")
            }
            // Trust (2026-10-02): `let alias = pair;` binds the `()` carrier into a local
            // mapped at the payload's real type, so the body is now refused at the binding
            // (KNOWN_HAZARDS "an opaque-carrier binding ALIASED into a new local and then
            // rebound"), one step before the value-ledger field check it used to reach.
            "rebound_payload" => Some("Let(opaque carrier at a real type)"),
            _ => None,
        };
        if let Some(refusal) = refusal {
            assert_eq!(body["lowered"], false, "carrier must be refused: {body}");
            assert_eq!(body["spliced"], false, "carrier must not splice: {body}");
            assert!(
                unsupported.contains(&serde_json::json!([refusal, 2])),
                "both arms must retain the refusal {refusal}: {body}"
            );
            let field_rows = unsupported
                .iter()
                .filter(|row| row[0].as_str().is_some_and(|tag| tag.starts_with("Field(")))
                .collect::<Vec<_>>();
            assert_eq!(field_rows.len(), 1, "exactly one field check names the refusal: {body}");
        } else {
            assert_eq!(body["lowered"], true, "real aggregate must lower: {body}");
            assert!(unsupported.is_empty(), "control acquired a refusal: {body}");
        }
    }
}
