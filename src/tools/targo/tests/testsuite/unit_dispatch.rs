// Trust: real scheduler output, independent of human package progress deduplication.
use crate::prelude::*;
use cargo_test_support::project;
use serde_json::Value;
use std::collections::BTreeSet;

fn messages(bytes: &[u8]) -> Vec<Value> {
    std::str::from_utf8(bytes)
        .unwrap()
        .lines()
        .map(|line| serde_json::from_str(line).expect("stdout must remain JSON-lines"))
        .collect()
}

fn dispatched(messages: &[Value]) -> Vec<&Value> {
    messages
        .iter()
        .filter(|message| message["reason"] == "compilation-unit-dispatched")
        .collect()
}

#[cargo_test]
fn exact_units_dispatch_before_package_dedup_and_join_only_their_artifacts() {
    let p = project()
        .file(
            "Cargo.toml",
            "[package]\nname='dispatch_probe'\nversion='0.0.1'\nedition='2024'\n",
        )
        .file(
            "src/lib.rs",
            "pub fn value() -> &'static str { env!(\"DISPATCH_SECRET\") }\n",
        )
        .file(
            "src/main.rs",
            "fn main() { let _ = dispatch_probe::value(); }\n",
        )
        .build();
    let targo = snapbox::cmd::cargo_bin!("targo");
    let run = |secret: &str| {
        p.process(targo)
            .args(&[
                "--unverified",
                "build",
                "--offline",
                "--message-format=json",
            ])
            .env("CARGO_TARGET_DIR", p.build_dir())
            .env("CARGO_BUILD_BUILD_DIR", p.root().join("build.noindex"))
            .env("DISPATCH_SECRET", secret)
            .exec_with_output()
            .unwrap()
    };
    let mut previous_ids = None;
    for (secret, fresh) in [
        ("PRIVATE_VALUE_ONE", false),
        ("PRIVATE_VALUE_ONE", true),
        ("PRIVATE_VALUE_TWO", false),
    ] {
        let output = run(secret);
        let messages = messages(&output.stdout);
        let events = dispatched(&messages);
        assert_eq!(
            events.len(),
            2,
            "the library and binary share a package but not an exact unit"
        );
        let ids: BTreeSet<_> = events
            .iter()
            .map(|event| {
                event["trust_unit_identity_sha256"]
                    .as_str()
                    .unwrap()
                    .to_owned()
            })
            .collect();
        assert_eq!(ids.len(), 2);
        if let Some(previous) = &previous_ids {
            assert_eq!(
                &ids, previous,
                "unchanged logical units retain exact graph identities across invocations"
            );
        }
        previous_ids = Some(ids);
        if secret == "PRIVATE_VALUE_TWO" {
            assert!(
                events
                    .iter()
                    .any(|event| event["dirty_reason"] == "changed-env")
            );
        }
        for event in events {
            assert_eq!(event["schema"], "targo.compilation-unit-dispatched.v1");
            assert_eq!(event["fresh"], fresh);
            assert_eq!(event["trust_compile_mode"], "build");
            assert!(matches!(
                event["trust_compile_kind"].as_str(),
                Some("host" | "target")
            ));
            assert_eq!(event["dirty_reason"].is_null(), fresh);
            let encoded = event.to_string();
            assert!(!encoded.contains("PRIVATE_VALUE"));
            assert!(!encoded.contains("DISPATCH_SECRET"));
            assert!(!encoded.contains(p.root().to_str().unwrap()));
            let id = event["trust_unit_identity_sha256"].as_str().unwrap();
            assert_eq!(id.len(), 64);
            let artifacts: Vec<_> = messages
                .iter()
                .filter(|message| {
                    message["reason"] == "compiler-artifact"
                        && message["trust_unit_identity_sha256"] == id
                })
                .collect();
            assert_eq!(
                artifacts.len(),
                1,
                "only this exact unit can complete its dispatch"
            );
            assert_eq!(artifacts[0]["fresh"], fresh);
        }
    }
    // Trust: an unreadable/unparseable prior fingerprint is classified FreshBuild,
    // even though this fixture demonstrably has already built both units.
    let mut corrupted = 0;
    for entry in walkdir::WalkDir::new(p.root().join("build.noindex")) {
        let entry = entry.unwrap();
        let path = entry.path();
        if matches!(
            path.file_name().and_then(|name| name.to_str()),
            Some("lib-dispatch_probe" | "bin-dispatch_probe")
        ) {
            std::fs::write(&path, "invalid prior hash").unwrap();
            std::fs::write(path.with_extension("json"), "{not-json").unwrap();
            corrupted += 1;
        }
    }
    assert_eq!(corrupted, 2);
    let rebuilt = run("PRIVATE_VALUE_TWO");
    let rebuilt_messages = messages(&rebuilt.stdout);
    let rebuilt_events = dispatched(&rebuilt_messages);
    assert_eq!(rebuilt_events.len(), 2);
    assert!(
        rebuilt_events
            .iter()
            .all(|event| event["fresh"] == false && event["dirty_reason"] == "fresh-build")
    );
}

#[cargo_test]
fn exact_graph_identity_preserves_dependency_features_and_extern_renames() {
    let manifest = |name: &str, feature: bool| {
        format!(
            "[package]\nname='graph_probe'\nversion='0.0.1'\nedition='2024'\n\
         [dependencies]\n{name}={{package='graph_dep',path='dep',features=[{}]}}\n",
            if feature { "'selected'" } else { "" },
        )
    };
    let source = |name: &str| format!("fn main() {{ let _ = {name}::value(); }}");
    let p = project()
        .file("Cargo.toml", &manifest("left", false))
        .file("src/main.rs", &source("left"))
        .file("dep/Cargo.toml", "[package]\nname='graph_dep'\nversion='0.0.1'\nedition='2024'\n[features]\nselected=[]\n")
        .file("dep/src/lib.rs", "pub fn value() -> u8 { 1 }\n")
        .build();
    let targo = snapbox::cmd::cargo_bin!("targo");
    let run = || {
        let output = p
            .process(targo)
            .args(&[
                "--unverified",
                "build",
                "--offline",
                "--message-format=json",
            ])
            .env("CARGO_TARGET_DIR", p.build_dir())
            .env("CARGO_BUILD_BUILD_DIR", p.root().join("build.noindex"))
            .exec_with_output()
            .unwrap();
        let records = messages(&output.stdout);
        let identity = |name: &str| {
            let artifact = records
                .iter()
                .find(|record| {
                    record["reason"] == "compiler-artifact" && record["target"]["name"] == name
                })
                .unwrap();
            let id = artifact["trust_unit_identity_sha256"]
                .as_str()
                .unwrap()
                .to_owned();
            assert_eq!(
                dispatched(&records)
                    .iter()
                    .filter(|event| event["trust_unit_identity_sha256"] == id)
                    .count(),
                1
            );
            id
        };
        (identity("graph_probe"), identity("graph_dep"))
    };
    let original = run();
    assert_eq!(
        run(),
        original,
        "a no-op retains both exact graph identities"
    );
    p.change_file("Cargo.toml", &manifest("left", true));
    let featured = run();
    assert_ne!(
        original.1, featured.1,
        "the selected dependency feature changes its unit"
    );
    assert_ne!(
        original.0, featured.0,
        "the parent binds its dependency's exact unit"
    );
    p.change_file("Cargo.toml", &manifest("right", true));
    p.change_file("src/main.rs", &source("right"));
    let renamed = run();
    assert_eq!(
        featured.1, renamed.1,
        "the dependency unit itself is unchanged"
    );
    assert_ne!(
        featured.0, renamed.0,
        "the parent binds its extern edge rename"
    );
    assert_eq!(run(), renamed, "the renamed graph is stable on reuse");
}
