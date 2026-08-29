// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! **The write path's acceptance gate**: `trust-toml`'s emitter against the
//! incumbent `toml 0.8`, over every TOML document checked into this repository.
//!
//! # The load-bearing test, and why it re-reads with the *incumbent*
//!
//! [`emitted_text_reread_by_the_incumbent_equals_the_incumbents_own_tree`] runs
//! the whole write path across the implementation boundary:
//!
//! ```text
//!   document ──trust-toml::from_str──▶ our tree ──trust-toml::to_string──▶ text
//!       │                                                                   │
//!       └──incumbent::from_str──▶ incumbent tree  ◀──incumbent::from_str────┘
//!                                        ≟
//! ```
//!
//! The re-read is deliberately done by the *incumbent*, not by us. A round trip
//! that goes out and back through one implementation cannot see a **symmetric**
//! bug: an emitter that writes `\q` for a tab paired with a parser that reads
//! `\q` as a tab round-trips flawlessly and produces a file every other TOML
//! reader in the world rejects or misreads. Only a foreign parser can catch that
//! class, and catching it is the entire reason the incumbent is still a
//! dev-dependency.
//!
//! # Why the gate is *not* byte-identity with the incumbent's emitter
//!
//! Because that would be reverse-engineering a private heuristic. `toml 0.8`
//! chooses among four string spellings — basic, literal, multi-line basic,
//! multi-line literal — to minimise escaping, and measurement (see
//! `src/emit.rs`) shows the choice is not reducible to a short rule. Nothing in
//! this repository depends on which spelling is used; everything depends on the
//! value being preserved. So the contract is value preservation, and byte-level
//! agreement is asserted where it actually holds and matters:
//! [`emitted_text_is_byte_identical_to_the_incumbent_on_the_shapes_this_tree_writes`]
//! covers the eleven real `toml::to_string*` call sites' data shapes, and
//! [`byte_agreement_over_the_whole_corpus_holds_at_the_measured_floor`] pins the
//! corpus-wide rate so a *regression* in agreement is visible even though
//! perfect agreement is not required.
//!
//! # Three tests, three separable failures
//!
//! Split for the same reason the read-path gate is split: a corpus that quietly
//! lost every array-of-tables would keep a merged test green while testing
//! nothing about arrays of tables.

use std::path::{Path, PathBuf};

mod common;
use common::compare_incumbent;

const MANIFEST: &str = include_str!("corpus_manifest.txt");

fn repository_root() -> PathBuf {
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

/// The corpus documents both implementations accept, as `(path, text)`.
///
/// Documents the incumbent rejects are skipped rather than failed: agreement on
/// *rejection* is the read path's gate (`differential_corpus.rs`), and a write
/// path has nothing to say about a document that was never read.
fn readable_corpus() -> Vec<(String, String)> {
    let root = repository_root();
    manifest_paths()
        .into_iter()
        .filter_map(|path| {
            let text = std::fs::read_to_string(root.join(&path)).ok()?;
            incumbent_toml::from_str::<incumbent_toml::Value>(&text).ok()?;
            Some((path, text))
        })
        .collect()
}

#[test]
fn emitted_text_reread_by_the_incumbent_equals_the_incumbents_own_tree() {
    let corpus = readable_corpus();
    assert!(
        corpus.len() > 1000,
        "the corpus holds {} readable documents; a sample this small is not the gate that was \
         designed",
        corpus.len()
    );

    let mut failures: Vec<String> = Vec::new();
    for (path, text) in &corpus {
        let expected = incumbent_toml::from_str::<incumbent_toml::Value>(text)
            .expect("readable_corpus filtered to documents the incumbent accepts");
        let ours: trust_toml::Value = match trust_toml::from_str(text) {
            Ok(value) => value,
            Err(error) => {
                // A read-path disagreement. It belongs to the other gate, but
                // reporting it here beats silently skipping the document.
                failures.push(format!("READ DISAGREEMENT  {path}\n    {error}"));
                continue;
            }
        };

        // Both emitters, because they are two code paths: `to_string_pretty`
        // differs from `to_string` in array formatting, and an array is exactly
        // where a writer bug hides.
        for (label, emitted) in [
            ("to_string", trust_toml::to_string(&ours)),
            ("to_string_pretty", trust_toml::to_string_pretty(&ours)),
        ] {
            let emitted = match emitted {
                Ok(text) => text,
                Err(error) => {
                    failures.push(format!("EMIT REFUSED  {path} [{label}]\n    {error}"));
                    continue;
                }
            };
            match incumbent_toml::from_str::<incumbent_toml::Value>(&emitted) {
                Err(error) => failures.push(format!(
                    "THE INCUMBENT CANNOT READ WHAT WE WROTE  {path} [{label}]\n    {error}"
                )),
                Ok(reread) => {
                    let mut differences = Vec::new();
                    compare_incumbent(&expected, &reread, "", &mut differences);
                    if !differences.is_empty() {
                        failures.push(format!(
                            "VALUE CHANGED ACROSS THE WRITE PATH  {path} [{label}]\n    {}",
                            differences.join("\n    ")
                        ));
                    }
                }
            }
        }
    }

    println!(
        "write-path differential: {} documents x 2 emitters, {} failure(s)",
        corpus.len(),
        failures.len()
    );
    assert!(
        failures.is_empty(),
        "the write path changed the meaning of {} document(s). Every one is a defect in \
         `trust-toml` or a measured difference that must be written down at its site — never \
         waved through.\n\n{}",
        failures.len(),
        failures.join("\n")
    );
}

/// Documents this repository's tooling actually *writes* with `toml::to_string`.
///
/// The eleven `toml::to_string*` call sites under `crates/` all live in
/// `trust-js-differential` and all serialize one of these ledgers. Byte
/// agreement here is what makes `src/emit.rs`'s documented string-style
/// deviation affordable: on the real workload there is no deviation.
const SHAPES_THIS_TREE_WRITES: &[&str] = &[
    "tests/js262/coverage.toml",
    "tests/js262/coverage-async.toml",
    "tests/js262/coverage-module.toml",
    "tests/js262/baseline.toml",
    "tests/js262/divergence-audit.toml",
    "tests/js262/test-exceptions.toml",
    "tests/js262/S0.toml",
];

/// The first line where two emissions diverge, with its neighbours.
///
/// Printing both whole documents is what this reported at first, and on a
/// 12,000-line ledger the result was unreadable — which in practice means the
/// gate fires and nobody can act on it. One located line is the diagnosis.
fn first_difference(left: &str, right: &str) -> String {
    let left_lines: Vec<&str> = left.lines().collect();
    let right_lines: Vec<&str> = right.lines().collect();
    for (index, (left_line, right_line)) in left_lines.iter().zip(&right_lines).enumerate() {
        if left_line != right_line {
            let context = index.saturating_sub(1);
            return format!(
                "  first difference at line {}:\n    context   {}\n    incumbent {left_line}\n    \
                 trust-toml {right_line}",
                index + 1,
                left_lines.get(context).copied().unwrap_or("")
            );
        }
    }
    format!(
        "  identical for {} lines, then the length differs: incumbent {} lines, trust-toml {} lines",
        left_lines.len().min(right_lines.len()),
        left_lines.len(),
        right_lines.len()
    )
}

#[test]
fn emitted_text_is_byte_identical_to_the_incumbent_on_the_shapes_this_tree_writes() {
    let root = repository_root();
    let mut checked = 0usize;
    let mut differences: Vec<String> = Vec::new();

    for path in SHAPES_THIS_TREE_WRITES {
        let text = std::fs::read_to_string(root.join(path))
            .unwrap_or_else(|error| panic!("{path}: {error} — this list is pinned, not globbed"));
        let theirs_tree: incumbent_toml::Value =
            incumbent_toml::from_str(&text).unwrap_or_else(|error| panic!("{path}: {error}"));
        let ours_tree: trust_toml::Value =
            trust_toml::from_str(&text).unwrap_or_else(|error| panic!("{path}: {error}"));

        for (label, theirs, ours) in [
            (
                "to_string",
                incumbent_toml::to_string(&theirs_tree),
                trust_toml::to_string(&ours_tree).map_err(|e| e.to_string()),
            ),
            (
                "to_string_pretty",
                incumbent_toml::to_string_pretty(&theirs_tree),
                trust_toml::to_string_pretty(&ours_tree).map_err(|e| e.to_string()),
            ),
        ] {
            checked += 1;
            let theirs = theirs.expect("the incumbent emits its own tree");
            let ours = ours.expect("we emit our own tree");
            if theirs != ours {
                differences.push(format!("{path} [{label}]\n{}", first_difference(&theirs, &ours)));
            }
        }
    }

    println!("byte-identity on written shapes: {checked} emissions checked");
    assert!(
        differences.is_empty(),
        "the two emitters disagree byte-for-byte on {} of {checked} emission(s) of the documents \
         this repository's own tooling writes. `src/emit.rs` claims the deviation is confined to \
         string spellings this workload does not contain; that claim is now false and must be \
         corrected there, not silenced here.\n\n{}",
        differences.len(),
        differences.join("\n\n")
    );
}

#[test]
fn byte_agreement_over_the_whole_corpus_holds_at_the_measured_floor() {
    // Full byte agreement is NOT required — see the module docs. What is
    // required is that the agreement rate does not silently fall: a change to
    // `render_string` or the header rules that started spelling ordinary
    // documents differently would show up here even though every value still
    // round-trips.
    let corpus = readable_corpus();
    let mut identical = 0usize;
    let mut different: Vec<&str> = Vec::new();

    for (path, text) in &corpus {
        let theirs_tree: incumbent_toml::Value = incumbent_toml::from_str(text).expect("filtered");
        let Ok(ours_tree) = trust_toml::from_str::<trust_toml::Value>(text) else { continue };
        let (Ok(theirs), Ok(ours)) =
            (incumbent_toml::to_string(&theirs_tree), trust_toml::to_string(&ours_tree))
        else {
            continue;
        };
        if theirs == ours {
            identical += 1;
        } else {
            different.push(path);
        }
    }

    let rate = identical as f64 / corpus.len() as f64;
    println!(
        "corpus byte agreement: {identical}/{} documents ({:.2}%)",
        corpus.len(),
        rate * 100.0
    );
    if !different.is_empty() {
        println!("  first differing documents: {:?}", &different[..different.len().min(10)]);
    }
    assert!(
        rate >= BYTE_AGREEMENT_FLOOR,
        "byte agreement with the incumbent's emitter fell to {:.2}%, below the {:.2}% floor \
         measured when this slice landed. That is not automatically a defect — the contract is \
         value preservation — but it IS a change in emitted spelling that nobody asked for. \
         Find the cause before moving the floor.\n  differing: {:?}",
        rate * 100.0,
        BYTE_AGREEMENT_FLOOR * 100.0,
        &different[..different.len().min(40)]
    );
}

/// Measured **100.00%** when the write path landed (1377/1377), and again at
/// the rename (1381/1381). RATCHETED to 1.0 when the rename was wired.
///
/// The floor used to sit at 0.99 to absorb corpus churn. That reasoning does not
/// survive the swap: with the rename live, every consumer's emitter IS this
/// crate, so 1% of slack against a measured 100% is roughly thirteen documents
/// that could start disagreeing with the incumbent without the gate saying so.
/// A gate with slack against a measured perfect score is not a gate.
///
/// If a genuinely new corpus document breaks byte-identity, that is a real
/// finding about the emitter — fix the spelling rule or exclude the document
/// explicitly and say why. Do not lower this number back.
const BYTE_AGREEMENT_FLOOR: f64 = 1.0;

/// Every character class the string-spelling rule branches on, so the generated
/// strings actually reach the branches. Ordinary letters are in the list too —
/// without them every generated string would be pathological and the common
/// case would go untested.
const STRING_ALPHABET: &[&str] = &[
    "a", "Z", "9", " ", "_", "-", ".", "#", "=", "[", "]", "{", "}", ",", "é", "→", "\u{10348}",
    "\"", "'", "\\", "\n", "\t", "\r", "\u{8}", "\u{c}", "\u{1}", "\u{1f}", "\u{7f}",
];

/// A tiny deterministic PRNG, so a failure is reproducible from its seed.
///
/// Deliberately not a `rand` dependency: `trust-rand` exists precisely so this
/// workspace stops linking one, and a test that needs nothing but a reproducible
/// bit stream should not add an edge to the graph this crate exists to shrink.
fn next(state: &mut u64) -> u64 {
    // xorshift64*, chosen for being four lines and having no tuning constants to
    // get wrong. Statistical quality is irrelevant here; coverage is.
    *state ^= *state >> 12;
    *state ^= *state << 25;
    *state ^= *state >> 27;
    state.wrapping_mul(0x2545_F491_4F6C_DD1D)
}

#[test]
fn string_spelling_matches_the_incumbent_over_generated_strings() {
    // `src/emit.rs`'s `StringForm` reproduces a heuristic that was FITTED to
    // twenty-eight measurements. A fitted rule is a hypothesis; this is the
    // test that keeps trying to falsify it. Both the exhaustive short strings
    // and the random longer ones matter: the short ones cover the delimiter
    // edge cases exactly (`'''`, a trailing quote), the long ones cover
    // combinations nobody enumerated.
    let mut cases: Vec<String> = Vec::new();

    // Exhaustive over the alphabet, lengths 0..=2.
    cases.push(String::new());
    for first in STRING_ALPHABET {
        cases.push((*first).to_string());
        for second in STRING_ALPHABET {
            cases.push(format!("{first}{second}"));
        }
    }
    // Exhaustive over the delimiter characters, length 3 and 4 — where `'''`
    // and `"""` and the trailing-quote rules live.
    let delimiters = ["'", "\"", "a", "\\", "\n"];
    for a in delimiters {
        for b in delimiters {
            for c in delimiters {
                cases.push(format!("{a}{b}{c}"));
                for d in delimiters {
                    cases.push(format!("{a}{b}{c}{d}"));
                }
            }
        }
    }
    // Random strings over the full alphabet, up to length 12.
    let mut state = 0x5EED_1234_ABCD_0001_u64;
    for _ in 0..20_000 {
        let length = (next(&mut state) % 13) as usize;
        let mut value = String::new();
        for _ in 0..length {
            let index = (next(&mut state) as usize) % STRING_ALPHABET.len();
            value.push_str(STRING_ALPHABET[index]);
        }
        cases.push(value);
    }

    let mut lost: Vec<String> = Vec::new();
    let mut disagreements: Vec<String> = Vec::new();
    let mut plain_disagreements: Vec<String> = Vec::new();
    let mut plain_total = 0usize;
    let mut mixed_total = 0usize;
    let mut mixed_differing = 0usize;

    for value in &cases {
        let mut ours_tree = trust_toml::Table::new();
        ours_tree.insert("k".to_string(), trust_toml::Value::String(value.clone()));
        let ours = trust_toml::to_string(&ours_tree).expect("a string is always representable");

        let mut theirs_tree = incumbent_toml::Table::new();
        theirs_tree.insert("k".to_string(), incumbent_toml::Value::String(value.clone()));
        let theirs = incumbent_toml::to_string(&theirs_tree).expect("likewise");

        // CORRECTNESS, and it is unconditional: whatever spelling we choose, the
        // INCUMBENT must read the original string back out of it. This is the
        // property that actually matters, it is checked for every case, and it
        // is strictly stronger than agreeing on the spelling.
        match incumbent_toml::from_str::<incumbent_toml::Value>(&ours) {
            Ok(reread) if reread["k"].as_str() == Some(value.as_str()) => {}
            other => lost.push(format!("{value:?}\n    we wrote {ours:?}\n    incumbent read {other:?}")),
        }
        // And our own parser, so the crate can read what it writes.
        match trust_toml::from_str::<trust_toml::Value>(&ours) {
            Ok(reread) if reread["k"].as_str() == Some(value.as_str()) => {}
            other => lost.push(format!("{value:?}\n    we wrote {ours:?}\n    we read {other:?}")),
        }

        // SPELLING, and it is conditional. See `is_mixed_quote`.
        if is_mixed_quote(value) {
            mixed_total += 1;
            if ours != theirs {
                // Counted in full; only the first few are printed. Reporting a
                // display cap as if it were the measurement is how a number in
                // a report stops meaning anything.
                mixed_differing += 1;
                if disagreements.len() < 8 {
                    disagreements.push(format!(
                        "  {value:?}\n    incumbent  {theirs:?}\n    trust-toml {ours:?}"
                    ));
                }
            }
        } else {
            plain_total += 1;
            if ours != theirs && plain_disagreements.len() < 20 {
                plain_disagreements.push(format!(
                    "  {value:?}\n    incumbent  {theirs:?}\n    trust-toml {ours:?}"
                ));
            }
        }
    }

    println!(
        "string spelling: {} generated cases — {plain_total} outside the mixed-quote class, all \
         byte-identical to the incumbent; {mixed_total} inside it, of which {mixed_differing} are \
         spelled differently (and every one of the {} round-tripped through BOTH parsers)",
        cases.len(),
        cases.len()
    );
    assert!(
        lost.is_empty(),
        "{} generated string(s) did not survive the write/read round trip. This is a CORRECTNESS \
         defect, not a spelling difference, and it is the one thing this test may never \
         tolerate.\n{}",
        lost.len(),
        lost[..lost.len().min(20)].join("\n")
    );
    assert!(
        plain_disagreements.is_empty(),
        "the string-spelling rule in `src/emit.rs` disagrees with the incumbent OUTSIDE the \
         mixed-quote class it is allowed to differ in. The rule there is a hypothesis fitted to \
         measurements; a disagreement here means the hypothesis is wrong and the rule must be \
         corrected — not that this exclusion should be widened.\n{}",
        plain_disagreements.join("\n")
    );
}

/// The one class where the emitted *spelling* is allowed to differ from the
/// incumbent's: a string holding an apostrophe **and** a quote or a backslash.
///
/// Measured, this is where `toml 0.8` starts doing delimiter arithmetic — it
/// will write `''''"'\'''`, a `'''` block whose content begins with a quote,
/// and `"""'"""""`, a `"""` block whose content ends with two. Both are legal
/// TOML and both read back correctly; reproducing the exact choice means
/// reimplementing `toml_edit`'s quote-run counting, which is unbounded work for
/// a cosmetic property.
///
/// It is a **predicate, not a list**, deliberately. A list of literal exceptions
/// grows every time someone finds a new case and stops being a boundary; a
/// predicate states the boundary once and makes any string outside it a
/// failure. The class is also measurably absent from the workload: no string in
/// any of the 1,377 readable corpus documents satisfies it, which is what
/// `emitted_text_is_byte_identical_to_the_incumbent_on_the_shapes_this_tree_writes`
/// independently confirms.
fn is_mixed_quote(value: &str) -> bool {
    value.contains('\'') && (value.contains('"') || value.contains('\\'))
}
