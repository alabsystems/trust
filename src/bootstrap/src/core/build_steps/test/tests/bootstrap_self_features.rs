//! Trust: Bootstrap's own builds allow exactly the std features its library test
//! target and the native controller client it links enable (BOOTSTRAP-SELF-INHERIT-FDS-1).
//!
//! `x.py test src/bootstrap` stopped compiling on 2026-11-08: Bootstrap began linking
//! `trust-resource-controller` with `client` (32e722797d), whose library enables
//! `trust_process_inherit_fds` under Trust's std, and the Mode::ToolBootstrap feature
//! sandbox refused it (E0725) before any Bootstrap test ran. `x.py check src/bootstrap`
//! checks `--all-targets`, so it also compiles the library test target, whose self-test
//! entry enables its runner features (8275d9821f); its sandbox refused those too.
//!
//! The features are read from the two crates' own sources. A feature either crate adds
//! later therefore fails here, not in a gate.

use std::collections::HashSet;
use std::path::{Path, PathBuf};

use super::{BOOTSTRAP_SELF_ALLOW_FEATURES, bootstrap_self_test_cargo};
use crate::core::builder::Builder;

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn read(root: &Path, path: &str) -> String {
    std::fs::read_to_string(root.join(path)).unwrap_or_else(|e| panic!("{path} is readable: {e}"))
}

/// Whether Bootstrap's manifest enables the controller's `client` feature.
fn bootstrap_links_the_controller_client(root: &Path) -> bool {
    read(root, "src/bootstrap/Cargo.toml").lines().any(|line| {
        line.trim_start().starts_with("trust-resource-controller") && line.contains("\"client\"")
    })
}

/// The names inside every `feature(...)` of `text`.
fn feature_lists(text: &str) -> Vec<String> {
    let mut features = Vec::new();
    let mut tail = text;
    while let Some(found) = tail.find("feature(") {
        let open = found + "feature(".len();
        let close = open + tail[open..].find(')').expect("feature(...) closes");
        features.extend(
            tail[open..close].split(',').map(str::trim).filter(|f| !f.is_empty()).map(String::from),
        );
        tail = &tail[close..];
    }
    features
}

/// The features a crate root enables at crate level: every `#![feature(...)]`, and
/// every `#![cfg_attr(<condition>, feature(...))]` whose condition `select` accepts.
fn crate_level_features(source: &str, select: impl Fn(&str) -> bool) -> Vec<String> {
    let mut features = Vec::new();
    let mut rest = source;
    while let Some(at) = rest.find("#![feature(") {
        let start = at + "#![".len();
        let end = start + rest[start..].find(")]").expect("a crate-level feature closes");
        features.extend(feature_lists(&rest[start..=end]));
        rest = &rest[end..];
    }
    let mut rest = source;
    while let Some(at) = rest.find("#![cfg_attr(") {
        let start = at + "#![cfg_attr(".len();
        let end = start + rest[start..].find(")]").expect("a crate-level cfg_attr closes");
        let attr = &rest[start..end];
        // The condition is everything before the first comma outside parentheses.
        let mut depth = 0usize;
        let split = attr
            .char_indices()
            .find(|&(_, c)| {
                match c {
                    '(' => depth += 1,
                    ')' => depth = depth.saturating_sub(1),
                    _ => {}
                }
                c == ',' && depth == 0
            })
            .map(|(i, _)| i)
            .expect("a crate-level cfg_attr has a condition and attributes");
        if select(attr[..split].trim()) {
            features.extend(feature_lists(&attr[split + 1..]));
        }
        rest = &rest[end..];
    }
    features
}

/// Whether a cfg condition mentions the `test` cfg.
fn names_test(condition: &str) -> bool {
    condition.split(|c: char| !(c.is_alphanumeric() || c == '_')).any(|word| word == "test")
}

/// What Bootstrap's own builds must allow: the controller client's features and those
/// of Bootstrap's library under `cfg(test)`. Each census has a control: it must find what
/// is there, or an empty answer would pass every row below.
fn wanted() -> HashSet<String> {
    let root = repo_root();
    assert!(
        bootstrap_links_the_controller_client(&root),
        "src/bootstrap/Cargo.toml no longer enables trust-resource-controller/client; \
         retire its feature from BOOTSTRAP_SELF_ALLOW_FEATURES and these tests together"
    );
    let client = crate_level_features(
        &read(&root, "crates/trust-resource-controller/src/lib.rs"),
        |condition| condition.contains("feature = \"client\""),
    );
    assert!(
        client.iter().any(|f| f == "trust_process_inherit_fds"),
        "the census did not find the controller's client feature: {client:?}"
    );
    let library = crate_level_features(&read(&root, "src/bootstrap/src/lib.rs"), names_test);
    assert!(
        library.iter().any(|f| f == "custom_test_frameworks"),
        "the census did not find the self-test entry's runner features: {library:?}"
    );
    client.into_iter().chain(library).collect()
}

#[test]
fn the_census_reads_conditions_and_unconditional_features() {
    let source = "#![feature(a, b)]\n#![cfg_attr(test, feature(c))]\n\
                  #![cfg_attr(all(feature = \"client\", x), feature(d))]\n\
                  #![cfg_attr(not(test), feature(e))]\n#![cfg_attr(test, test_runner(f))]";
    let mut found = crate_level_features(source, names_test);
    found.sort();
    // `not(test)` names the test cfg too; the census over-reports rather than miss one.
    assert_eq!(found, ["a", "b", "c", "e"]);
    let client = crate_level_features(source, |c| c.contains("feature = \"client\""));
    assert_eq!(client, ["a", "b", "d"]);
}

#[test]
fn bootstrap_self_test_build_allows_what_its_test_target_and_client_enable() {
    let wanted = wanted();
    let context = crate::utils::tests::TestCtx::new();
    let build = crate::core::session::Session::new(context.config("test").create_config());
    let builder = Builder::new(&build);
    let mut command = bootstrap_self_test_cargo(&builder).into_cmd();
    command.mark_as_executed();
    let features = command
        .get_envs()
        .find(|(key, _)| *key == "RUSTC_ALLOW_FEATURES")
        .and_then(|(_, value)| value)
        .expect("a ToolBootstrap build keeps an explicit feature sandbox")
        .to_str()
        .unwrap()
        .to_owned();
    let allowed: HashSet<&str> = features.split(',').collect();
    for feature in &wanted {
        assert!(allowed.contains(feature.as_str()), "{feature} is refused: {features}");
    }
    // It is still a sandbox: what neither the self-test entry nor the client asks for
    // stays refused.
    assert!(!allowed.contains("specialization"), "{features}");
    assert!(!allowed.contains("allocator_api"), "{features}");
}

#[test]
fn bootstrap_self_allowance_is_exactly_what_its_targets_enable() {
    let allowed: HashSet<String> =
        BOOTSTRAP_SELF_ALLOW_FEATURES.split(',').map(String::from).collect();
    assert_eq!(allowed, wanted(), "{BOOTSTRAP_SELF_ALLOW_FEATURES}");
}

#[test]
fn bootstrap_check_step_allows_what_its_test_build_allows() {
    // The check step is a `tool_check_step!` table entry, built only by running it; its
    // sandbox is the expression the entry names.
    let check = read(&repo_root(), "src/bootstrap/src/core/build_steps/check.rs");
    let start = check.find("tool_check_step!(Bootstrap {").expect("Bootstrap has a check step");
    let entry = &check[start..start + check[start..].find("});").expect("the entry closes")];
    assert!(
        entry.contains("path: \"src/bootstrap\"")
            && entry.contains("allow_features: super::test::BOOTSTRAP_SELF_ALLOW_FEATURES"),
        "{entry}"
    );
}
