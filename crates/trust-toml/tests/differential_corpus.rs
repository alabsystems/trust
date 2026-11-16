// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! **The acceptance gate**: `trust-toml` against the incumbent `toml 0.8`, over
//! every TOML document checked into this repository.
//!
//! # Why a differential and not a fixture suite
//!
//! A TOML reader's characteristic bug is silent: a construct it misunderstands
//! yields a *different configuration*, not an error. A hand-written suite can
//! only cover the constructs its author remembered, and the constructs an
//! author forgets are precisely the ones that then fail without a symptom. The
//! corpus does not forget — it contains whatever this repository actually
//! writes, including the idioms nobody would think to write a fixture for.
//!
//! # Three tests, three separable failures
//!
//! * [`corpus_membership_matches_the_pinned_manifest`] — the sample cannot
//!   shift, and above all cannot silently shrink.
//! * [`corpus_still_exercises_every_measured_construct`] — the sample still
//!   contains the constructs it is supposed to be exercising.
//! * [`trust_toml_agrees_with_the_incumbent_over_the_pinned_corpus`] — the
//!   differential itself.
//!
//! Splitting them matters: a corpus that quietly lost every dotted key would
//! keep the differential green while testing nothing about dotted keys, which
//! is exactly the shape of failure this crate is meant not to have.
//!
//! # What the differential asserts
//!
//! For every document: both implementations **accept** it or both **reject**
//! it, and on acceptance the two `Value` trees are equal — recursively, by
//! value, **and by key iteration order**. The ordering clause is separate on
//! purpose. Key *sets* can match while iteration order differs, and iteration
//! order is observable: it decides the bytes of anything digested or re-emitted
//! from a table. A test comparing only sets would pass an implementation that
//! had quietly become insertion-ordered.
//!
//! # What it does NOT assert
//!
//! Error message text. See `src/error.rs`: agreement on *whether* to reject is
//! a contract; agreement on another crate's prose is not, and asserting it
//! would make the incumbent's next release a build break here.
//!
//! # The dev-dependency is renamed, and that is load-bearing
//!
//! `incumbent-toml = { package = "toml", version = "0.8.23" }` — an explicit
//! version, never `workspace = true` and never reached through
//! `[patch.crates-io]`. Both of those are graph-wide and would capture this
//! dependency too, so this file would compare `trust-toml` against ITSELF and
//! report green. That is not hypothetical: it is what happened to the `sha2`
//! swap; the finding remains in the historical workspace's commented-out
//! `[patch.crates-io] sha2` block (`992ace2954^:crates/Cargo.toml`).

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use std::process::Command;

mod common;
use common::compare;

const MANIFEST: &str = include_str!("corpus_manifest.txt");

fn repository_root() -> PathBuf {
    // crates/trust-toml -> crates -> repository root.
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("the crate lives two levels below the repository root")
        .to_path_buf()
}

fn manifest_paths() -> Vec<String> {
    MANIFEST
        .lines()
        .map(str::trim)
        .filter(|line| !line.starts_with('#') && !line.is_empty())
        .map(str::to_string)
        .collect()
}

#[test]
fn corpus_membership_matches_the_pinned_manifest() {
    let root = repository_root();
    // Recomputed with exactly the command the manifest header documents, so
    // the check and the regeneration recipe cannot drift apart.
    let output = Command::new("git")
        .args(["ls-files", "--", "*.toml"])
        .current_dir(&root)
        .output()
        .expect("`git ls-files` must be runnable from the repository root");
    assert!(output.status.success(), "git ls-files failed: {:?}", output.status);
    let on_disk: BTreeSet<String> = String::from_utf8(output.stdout)
        .expect("git paths are UTF-8 in this repository")
        .lines()
        .filter(|path| !path.starts_with("first-party/") && !path.starts_with("vendor/"))
        .map(str::to_string)
        .collect();

    let pinned: BTreeSet<String> = manifest_paths().into_iter().collect();

    let vanished: Vec<&String> = pinned.difference(&on_disk).collect();
    let appeared: Vec<&String> = on_disk.difference(&pinned).collect();
    assert!(
        vanished.is_empty() && appeared.is_empty(),
        "the corpus SAMPLE has shifted. This is a reviewable event, not a test to silence — a \
         corpus that silently shrinks reads as a green run.\n  no longer present ({}): {:?}\n  \
         newly present ({}): {:?}\n  refresh with the command in tests/corpus_manifest.txt",
        vanished.len(),
        vanished,
        appeared.len(),
        appeared
    );
    assert!(
        pinned.len() > 1000,
        "the pinned corpus holds {} documents; a sample this small is not the gate that was \
         designed",
        pinned.len()
    );
    println!("corpus membership: {} pinned documents, exactly matching the tree", pinned.len());
}

/// Constructs this crate implements, with a floor on how many corpus documents
/// must still contain each one.
///
/// The floors are set below the values measured when the corpus was pinned (in
/// the comment beside each) so that ordinary churn does not trip them, but a
/// construct disappearing from the corpus entirely does. This is what a
/// per-file digest was really a proxy for, made direct: a digest says bytes
/// changed, this says whether the differential still exercises dotted keys.
///
/// Detection is textual and deliberately independent of `trust_toml`'s own
/// parser — a coverage check that used the implementation under test to decide
/// what the corpus contains would agree with itself by construction.
const CONSTRUCT_FLOORS: &[(&str, usize, fn(&str) -> bool)] = &[
    ("inline table", 400, |line| line.contains("= {") || line.contains("={")), // 471
    ("dotted key", 120, is_dotted_key_line),                                   // 148
    ("array of tables", 110, |line| line.trim_start().starts_with("[[")),      // 132
    ("multi-line array", 100, |line| line.trim_end().ends_with("= [")),        // 129
    ("literal string", 15, |line| line.contains("= '")),                       // 19
    ("multi-line basic string", 10, |line| line.contains("\"\"\"")),           // 14
    ("quoted key", 8, is_quoted_key_line),                                     // 11
    ("multi-line literal string", 1, |line| line.contains("'''")),             // 3
    ("radix integer", 1, is_radix_integer_line),                               // 3
];

fn is_dotted_key_line(line: &str) -> bool {
    let trimmed = line.trim_start();
    if trimmed.starts_with('#') || trimmed.starts_with('[') {
        return false;
    }
    let Some((key, _)) = trimmed.split_once('=') else { return false };
    let key = key.trim();
    !key.is_empty()
        && key.contains('.')
        && key
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'_' | b'-' | b'.'))
}

fn is_quoted_key_line(line: &str) -> bool {
    let trimmed = line.trim_start();
    trimmed.starts_with('"') && trimmed.contains('=')
}

fn is_radix_integer_line(line: &str) -> bool {
    ["= 0x", "= 0o", "= 0b"].iter().any(|prefix| line.contains(prefix))
}

#[test]
fn corpus_still_exercises_every_measured_construct() {
    let root = repository_root();
    let mut counts = vec![0usize; CONSTRUCT_FLOORS.len()];

    for path in manifest_paths() {
        let Ok(text) = std::fs::read_to_string(root.join(&path)) else { continue };
        for (index, (_, _, detect)) in CONSTRUCT_FLOORS.iter().enumerate() {
            if text.lines().any(|line| detect(line)) {
                counts[index] += 1;
            }
        }
    }

    let mut starved = Vec::new();
    for (index, (name, floor, _)) in CONSTRUCT_FLOORS.iter().enumerate() {
        println!("  {name:26} {} documents (floor {floor})", counts[index]);
        if counts[index] < *floor {
            starved.push(format!("{name}: {} documents, floor {floor}", counts[index]));
        }
    }
    assert!(
        starved.is_empty(),
        "the corpus no longer exercises constructs this crate implements, so the differential is \
         green about less than it appears to be:\n  {}",
        starved.join("\n  ")
    );
}

#[test]
fn trust_toml_agrees_with_the_incumbent_over_the_pinned_corpus() {
    let root = repository_root();
    let paths = manifest_paths();

    let mut accepted = 0usize;
    let mut rejected_by_both = 0usize;
    let mut disagreements: Vec<String> = Vec::new();

    for path in &paths {
        let text = std::fs::read_to_string(root.join(path))
            .unwrap_or_else(|error| panic!("{path}: {error}"));

        let incumbent = incumbent_toml::from_str::<incumbent_toml::Value>(&text);
        let ours = trust_toml::from_str::<trust_toml::Value>(&text);

        match (&incumbent, &ours) {
            (Ok(incumbent), Ok(ours)) => {
                accepted += 1;
                let mut differences = Vec::new();
                compare(incumbent, ours, "", &mut differences);
                if !differences.is_empty() {
                    disagreements
                        .push(format!("TREES DIFFER  {path}\n    {}", differences.join("\n    ")));
                }
            }
            (Err(_), Err(_)) => rejected_by_both += 1,
            (Ok(_), Err(error)) => {
                disagreements.push(format!("ONLY TRUST-TOML REJECTS  {path}\n    {error}"));
            }
            (Err(error), Ok(_)) => {
                disagreements.push(format!("ONLY THE INCUMBENT REJECTS  {path}\n    {error}"));
            }
        }
    }

    println!(
        "corpus differential: {} documents — {accepted} accepted by both, {rejected_by_both} \
         rejected by both, {} disagreements",
        paths.len(),
        disagreements.len()
    );
    assert!(
        disagreements.is_empty(),
        "the corpus differential found {} disagreement(s). Each one is either a defect in \
         `trust-toml` or a measured difference that must be written down at its site — never \
         waved through.\n\n{}",
        disagreements.len(),
        disagreements.join("\n")
    );
}
