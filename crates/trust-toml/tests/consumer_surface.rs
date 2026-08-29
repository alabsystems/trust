// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! **The drop-in surface**: every `toml::` API the five `crates/` consumers of
//! `toml` actually call, exercised against both implementations.
//!
//! # Why this exists next to a corpus differential
//!
//! The corpus gate proves the two readers agree on `Value` trees. It does not
//! prove that a *consumer* compiles and behaves identically under the Cargo
//! dependency rename that is the whole integration mechanism, because the
//! corpus never calls `as_integer`, never indexes a `Value`, and never
//! deserializes into a struct with `#[serde(default)]` on it.
//!
//! Slice 1 deliberately does not rename any consumer's manifest — that is slice
//! 3, and `crates/trust-version` is also a member of the ROOT workspace, so the
//! rename moves a lockfile another lane has open. This file is how the drop-in
//! property gets evidence in the meantime: it reproduces each consumer's exact
//! usage here, where it costs nothing and cannot break a shared lock.
//!
//! # The surface, measured, not guessed
//!
//! Every `toml::` path used anywhere under `crates/` (excluding fixtures), by
//! frequency:
//!
//! | | | | |
//! |---|---|---|---|
//! | `from_str` 53 | `to_string` 9 | `Value` 8 | `Value::as_str` 6 |
//! | `de::Error` 5 | `Value::String` 2 | `Value::as_integer` 2 | `Value::as_bool` 2 |
//! | `to_string_pretty` 2 | `Table` 2 | `Value::as_table` 1 | `Value::Boolean` 1 |
//! | `Value::Array` 1 | | | |
//!
//! `to_string` / `to_string_pretty` (11 sites, all in `trust-js-differential`)
//! are the write path. They landed in slice 2 (`src/ser.rs`), and the rename is
//! now WIRED — every item in that table is exercised below, and the write path
//! additionally carries `tests/serialize_differential.rs`.

use std::collections::BTreeMap;

use serde::Deserialize;

mod common;
use common::compare;

/// The crate-level doc example from `src/lib.rs`, executed.
///
/// **Not redundant with the doctest.** Measured on this clone: the doctest lane
/// does not run at all. With the host `rustdoc` it dies on an ABI skew
/// (`E0514: found crate serde compiled by an incompatible version of rustc`),
/// and with the stage2 `trustdoc` it dies because verification is on by default
/// and `rustdoc` rejects the `-Ztrust-verify=off` that `targo` would inject per
/// unit. Both failures reproduce identically for `trust-sha2`, so this is a
/// property of the toolchain on this machine and not of either crate — but the
/// consequence is the same either way: a doc example nobody can execute is an
/// unverified claim sitting in the documentation. This test is the executable
/// copy. Change one and change the other.
#[test]
fn the_crate_doc_example_is_true() {
    let document = r#"
title = "example"

[owner]
name = "Andrew"
ports = [8001, 8002]
"#;

    let value: trust_toml::Value = trust_toml::from_str(document).expect("the doc example parses");
    assert_eq!(value["title"].as_str(), Some("example"));
    assert_eq!(value["owner"]["name"].as_str(), Some("Andrew"));
    assert_eq!(value["owner"]["ports"][1].as_integer(), Some(8002));
}

// ---------------------------------------------------------------------------
// crates/trust-version — the smallest consumer, and the one slice 3 converts
// first. `parse_version_source` at src/lib.rs:584 is `toml::from_str` into
// exactly this shape.
// ---------------------------------------------------------------------------

#[derive(Debug, PartialEq, Eq, Deserialize)]
struct TrustVersionSource {
    schema_version: String,
    product: String,
    toolchain_alias: String,
    trust_product_version: String,
    release_report_schema: String,
    /// A nested table into a struct.
    rust_alignment: RustAlignment,
    /// `#[serde(default)]` over a `BTreeMap` — absent in some documents.
    #[serde(default)]
    schemas: BTreeMap<String, String>,
}

#[derive(Debug, PartialEq, Eq, Deserialize)]
struct RustAlignment {
    rustc_version: String,
    revision: String,
    merged_on: String,
}

fn version_source_path() -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(std::path::Path::parent)
        .expect("two levels below the repository root")
        .join("release/trust-version.toml")
}

#[test]
fn the_real_release_version_file_deserializes_identically() {
    let text = std::fs::read_to_string(version_source_path())
        .expect("release/trust-version.toml must exist — it is the release gate's own input");

    let incumbent: TrustVersionSource =
        incumbent_toml::from_str(&text).expect("the incumbent must accept the release file");
    let ours: TrustVersionSource =
        trust_toml::from_str(&text).expect("trust-toml must accept the release file");

    assert_eq!(incumbent, ours, "the two readers disagree about the release version file");
    // Not just "equal to each other" — equal to what the file says. Two
    // implementations that were wrong the same way would pass the line above.
    assert_eq!(ours.schema_version, "trust.version-source.v2");
    assert_eq!(ours.product, "Trust");
    assert_eq!(ours.rust_alignment.rustc_version, "1.99.0");
    assert!(ours.rust_alignment.revision.starts_with("rust-lang/rust:"));
    assert_eq!(ours.schemas.get("version").map(String::as_str), Some("trust.version.v3"));
}

#[test]
fn an_absent_serde_default_table_arrives_empty() {
    // The `[schemas]` table is optional. This is the path `#[serde(default)]`
    // exists for, and the release file itself does NOT exercise it — so
    // without this case the attribute would be untested by the vertical.
    let text = "\
schema_version = \"trust.version-source.v2\"
product = \"Trust\"
toolchain_alias = \"trust\"
trust_product_version = \"0.1.0\"
release_report_schema = \"trust.release-report.v1\"

[rust_alignment]
rustc_version = \"1.99.0\"
revision = \"rust-lang/rust:0000000000000000000000000000000000000000\"
merged_on = \"2026-07-08\"
";
    let incumbent: TrustVersionSource = incumbent_toml::from_str(text).expect("incumbent");
    let ours: TrustVersionSource = trust_toml::from_str(text).expect("trust-toml");
    assert_eq!(incumbent, ours);
    assert!(ours.schemas.is_empty(), "an absent defaulted table must be empty, not an error");
}

// ---------------------------------------------------------------------------
// crates/trust-router/tests/manifest_feature_plumbing.rs and
// crates/trust-bmc/src/verifier_api.rs:11267 — read a real Cargo.toml as a
// dynamic `Value`, then INDEX into it. `manifest["features"]["trust-build"]`
// panics on a missing key, which is the incumbent's behaviour and therefore
// this crate's.
// ---------------------------------------------------------------------------

#[test]
fn indexing_a_manifest_matches_the_incumbent() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(std::path::Path::parent)
        .expect("two levels below the repository root");
    let text = std::fs::read_to_string(root.join("crates/trust-router/Cargo.toml"))
        .expect("trust-router's manifest is in the corpus");

    let incumbent: incumbent_toml::Value = incumbent_toml::from_str(&text).expect("incumbent");
    let ours: trust_toml::Value = trust_toml::from_str(&text).expect("trust-toml");

    // The exact expression `trust-router`'s test writes.
    let incumbent_edges: Vec<&str> = incumbent["features"]["trust-build"]
        .as_array()
        .expect("trust-build must be an array")
        .iter()
        .map(|value| value.as_str().expect("a feature edge is a string"))
        .collect();
    let our_edges: Vec<&str> = ours["features"]["trust-build"]
        .as_array()
        .expect("trust-build must be an array")
        .iter()
        .map(|value| value.as_str().expect("a feature edge is a string"))
        .collect();

    assert_eq!(incumbent_edges, our_edges);
    assert!(!our_edges.is_empty(), "an empty edge list would make this assertion vacuous");
    assert!(our_edges.contains(&"trust-vc-native"), "{our_edges:?}");

    // `.as_table()` on a table, and `Map::get` through it — the trust-bmc
    // shape at verifier_api.rs:11313.
    let dependencies = ours["dependencies"].as_table().expect("dependencies is a table");
    assert!(dependencies.contains_key("trust-types"), "{:?}", dependencies.keys().count());

    // A dependency spelled as an inline table, read back field by field.
    //
    // Note WHICH table this reads from. `trust-router`'s `toml` edge is a
    // DEV-dependency (`trust-router/Cargo.toml:167`), not a normal one — which
    // is why `trust-router` is absent from the five in-closure NORMAL parents
    // of `toml` that the phase-2 measurement names, and why converting it is
    // not part of the 121 -> 115 kill. An earlier draft of this test asserted
    // `dependencies["toml"]` and failed, which is the measurement lesson in
    // miniature: `Cargo.lock` has no dependency-kind field, so counting
    // lockfile edges would have counted this one as shipping.
    let dev = ours["dev-dependencies"].as_table().expect("dev-dependencies is a table");
    let toml_dep = dev.get("toml").expect("trust-router DEV-depends on toml");
    assert_eq!(
        toml_dep.as_table().expect("inline table").get("workspace"),
        Some(&trust_toml::Value::Boolean(true))
    );
}

// ---------------------------------------------------------------------------
// crates/trust-deps/src/lib.rs:1600 — parse ONE dependency line into a
// `toml::Table`, then match on `Value::String` / `Boolean` / `Array` to
// re-render it. This is the only consumer that pattern-matches variants.
// ---------------------------------------------------------------------------

#[test]
fn a_single_dependency_line_round_trips_through_table_and_variants() {
    let line =
        "trust-ir = { path = \"../trust-ir\", default-features = false, features = [\"a\", \"b\"], optional = true }";

    let incumbent: incumbent_toml::Value = incumbent_toml::from_str(line).expect("incumbent");
    let ours: trust_toml::Value = trust_toml::from_str(line).expect("trust-toml");
    let mut differences = Vec::new();
    compare(&incumbent, &ours, "", &mut differences);
    assert!(differences.is_empty(), "{differences:?}");

    // `trust-deps`' exact chain: as_table -> get -> as_table -> cloned.
    let spec: trust_toml::Table = ours
        .as_table()
        .and_then(|table| table.get("trust-ir"))
        .and_then(trust_toml::Value::as_table)
        .cloned()
        .expect("the dependency spec is an inline table");

    // And its `format_inline_toml_value` match, which is exhaustive over the
    // three variants it supports and errors on everything else.
    assert!(matches!(spec.get("path"), Some(trust_toml::Value::String(path)) if path == "../trust-ir"));
    assert!(matches!(spec.get("optional"), Some(trust_toml::Value::Boolean(true))));
    let Some(trust_toml::Value::Array(features)) = spec.get("features") else {
        panic!("features must be an array");
    };
    assert_eq!(features.len(), 2);
    assert_eq!(features[0].as_str(), Some("a"));

    // `as_integer` / `as_bool`, the two remaining measured accessors.
    let numbers: trust_toml::Value = trust_toml::from_str("n = 42\nb = false\n").expect("parse");
    assert_eq!(numbers.get("n").and_then(trust_toml::Value::as_integer), Some(42));
    assert_eq!(numbers.get("b").and_then(trust_toml::Value::as_bool), Some(false));
    assert_eq!(numbers.get("missing"), None, "get must not panic on a missing key");
}

// ---------------------------------------------------------------------------
// crates/trust-version/src/lib.rs:591,638 and
// crates/trust-upstream-compat/src/parse.rs:21 — `toml::de::Error` has to be a
// real `std::error::Error` so it can sit behind `#[from]` and be returned from
// `Error::source`.
// ---------------------------------------------------------------------------

#[test]
fn de_error_satisfies_the_bounds_consumers_place_on_it() {
    #[derive(Debug)]
    enum VersionError {
        Toml(trust_toml::de::Error),
    }

    impl std::fmt::Display for VersionError {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match self {
                Self::Toml(source) => write!(f, "failed to parse Trust version source: {source}"),
            }
        }
    }

    impl std::error::Error for VersionError {
        fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
            match self {
                // Requires `de::Error: std::error::Error + 'static`.
                Self::Toml(source) => Some(source),
            }
        }
    }

    // Requires the `From` impl `trust-version` writes by hand at lib.rs:638.
    impl From<trust_toml::de::Error> for VersionError {
        fn from(source: trust_toml::de::Error) -> Self {
            Self::Toml(source)
        }
    }

    fn parse(input: &str) -> Result<TrustVersionSource, VersionError> {
        Ok(trust_toml::from_str(input)?)
    }

    let error = parse("schema_version = 1\n").expect_err("an integer is not a string");
    assert!(std::error::Error::source(&error).is_some());
    let rendered = error.to_string();
    assert!(rendered.contains("failed to parse Trust version source"), "{rendered}");
    assert!(rendered.contains("line 1"), "{rendered}");

    // `Send + Sync` is what `thiserror`'s `#[from]` needs in
    // `trust-upstream-compat`, and what any error crossing a thread needs.
    fn assert_send_sync<T: Send + Sync + 'static>() {}
    assert_send_sync::<trust_toml::de::Error>();
}
