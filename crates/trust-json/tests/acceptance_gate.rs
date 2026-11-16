// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! The CHECKED-IN half of the `trust-json` acceptance gate.
//!
//! `differential_json.rs` generates its inputs — float bit patterns, Unicode
//! sweeps, random trees, byte soup. This file uses inputs that already exist:
//! the JSON documents pinned in `corpus_manifest.txt`, an enumerated table of
//! the byte-exactness hazards, and a `#[derive(Deserialize)]` driven from both
//! trees. Between them the two binaries cover the surface the phase-2 brief
//! names.
//!
//! # What is compared, and why it is bytes
//!
//! Everything. For every corpus document that both implementations accept:
//!
//! ```text
//!   ours.parse(doc)          ==  theirs.parse(doc)         (tree, carrier-exact)
//!   ours.compact(ours.tree)  ==  theirs.compact(theirs.tree)   BYTE for byte
//!   ours.pretty (ours.tree)  ==  theirs.pretty (theirs.tree)   BYTE for byte
//!   ours.parse(theirs.bytes) ==  theirs.parse(ours.bytes)  (the CROSS leg)
//! ```
//!
//! The cross leg is the one that cannot be satisfied by two implementations
//! that are each self-consistently wrong: it requires our reader to accept
//! their writer's output and vice versa, so a shared misunderstanding of, say,
//! exponent notation is caught even when both sides round-trip themselves.
//!
//! And for every document either side REJECTS, the other must reject it too, at
//! the same line, the same column, with the same message. *Agreeing on accept
//! while disagreeing on reject is a real defect* — a replacement that is merely
//! more permissive silently accepts corrupt proof bundles that the incumbent
//! would have refused.
//!
//! # The typed lens, and the honest limit on it
//!
//! `trust-json` has no serde layer yet (the phase-2 plan defers the serde
//! replacement as a six-repository atomic change), so `from_str::<MyStruct>` is
//! not a thing this crate can do and cannot be differentially compared. What
//! CAN be compared, and is, is one step earlier and is where every typed
//! decision is actually made: **the same derived `Deserialize`, driven by our
//! tree and by the incumbent's tree, must reach the same verdict** — the same
//! `Ok` value, or the same `Err` message. `serde_json::from_value` is the seam
//! that makes that a real differential rather than a re-implementation of
//! serde's rules by me, which would only test my own transcription.
//!
//! That is what makes `Option::None` vs a missing field, a missing required
//! field, an unknown field and a wrong scalar type testable today, and it is
//! the exact interface the future `trust-serde` layer has to satisfy.
//!
//! # MUTATION LOG — what THIS file has been SEEN to catch
//!
//! Each defect was applied to the crate, this binary was run, the listed tests
//! failed with the listed evidence, and the defect was reverted and the binary
//! re-run green. A test never observed failing is not evidence.
//!
//! Six defects, six killed, revert green. The "corpus" column is the number of
//! the 2954 documents that disagreed, and it is the interesting column.
//!
//! | # | defect injected | site | tests failed | corpus |
//! |---|---|---|---|---|
//! | A1 | `f64` threshold `(-5, 15)` -> `(-5, 16)` | `ser/float.rs` `F64_FIXED_EXP` | 8 | **0** |
//! | A2 | stop escaping U+001F (`ESCAPE[0x1F]` `UU` -> `__`) | `ser/mod.rs` `ESCAPE` | 4 | **0** |
//! | A3 | pretty-print an empty object as `{\n}` | `ser/mod.rs` `end_object` | 4 | 79 |
//! | A4 | recursion limit 128 -> 129 | `de.rs` `DEFAULT_RECURSION_LIMIT` | 3 | 1 |
//! | A5 | drop null-valued object entries | `de.rs` object loop | 7 | 2593 |
//! | A6 | accept trailing data (skip `de.end()`) | `de.rs` `from_str`/`from_slice` | 4 | 17 |
//!
//! ## The two zeros are the point, and they were a surprise
//!
//! A1 and A2 — a float-notation defect and a dropped escape, the two hazards
//! the brief names by name — are invisible to a 112 MiB corpus of real JSON.
//! A1 only moves values in `[1e15, 1e16)` and the corpus has none; A2 only
//! moves U+001F and the corpus has none of that either, despite 51 documents
//! containing SOME control character. Both were caught, immediately and with a
//! readable message, by the enumerated hazard table and by the generated
//! sweeps in `differential_json.rs`:
//!
//! ```text
//! A1  the_byte_exactness_hazard_table_round_trips
//!       f64 threshold, high end: "[1e15,1e16]"
//!            ours: [1000000000000000.0,10000000000000000.0]
//!          theirs: [1000000000000000.0,1e+16]
//!     parse_agrees_over_random_number_texts
//!       re-serialization of "-94353112606964411.53694203831592148"
//!            ours: "-94353112606964420.0"   theirs: "-9.435311260696442e+16"
//!
//! A2  the_byte_exactness_hazard_table_round_trips
//!       other controls are lowercase \u: "[\"\\u0000\\u0001\\u001F\"]"
//!            ours: the U+001F went out as a RAW BYTE, unescaped
//!          theirs: ["\u0000\u0001\u001f"]
//!     string_escaping_matches_for_every_bmp_scalar_value  (U+001F)
//! ```
//!
//! So: a real-document corpus is necessary and NOT sufficient, an enumerated
//! table is necessary and not sufficient, and generated sweeps are necessary
//! and not sufficient. Deleting any one of the three because "the others are
//! green" removes coverage the others provably do not have.
//!
//! A4's single corpus hit is the mirror image and just as instructive: exactly
//! one checked-in document sits at the recursion boundary, so a limit off by
//! one is a real-world defect, not a theoretical one.
//!
//! ## The mutation harness has its own trap, recorded so nobody re-finds it
//!
//! Reverting a mutant with `shutil.move`/`copy2` PRESERVES the original mtime,
//! so the restored file is OLDER than the artifact built from the mutant and
//! cargo's mtime freshness check skips the rebuild — the "reverted" run then
//! re-executes the MUTANT binary. Measured: the first sweep reported the revert
//! as NOT GREEN, with exactly the last mutation's failure set, from a source
//! file that was already correct on disk. Any revert must bump the mtime.

mod common;
use std::path::{Path, PathBuf};

use common::{agree_on_parse, first_difference, inc_from_slice, inc_from_str, same, to_inc};
use incumbent_serde::Deserialize;
use incumbent_serde_json as inc;
use trust_json as tj;

// ===========================================================================
// 1. THE CHECKED-IN CORPUS
// ===========================================================================

/// The pinned sample. See the file's own header for the regeneration rule and
/// for why it holds paths rather than digests.
const MANIFEST: &str = include_str!("corpus_manifest.txt");

fn repo_root() -> PathBuf {
    // crates/trust-json -> crates -> repo root.
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("crate is two levels below the repo root")
        .to_path_buf()
}

fn manifest_paths() -> Vec<String> {
    MANIFEST
        .lines()
        .map(str::trim)
        .filter(|l| !l.is_empty() && !l.starts_with('#'))
        .map(str::to_owned)
        .collect()
}

/// The membership rule, written once so the manifest and the check cannot drift
/// apart: a checked-in `*.json`, not under a submodule or `vendor/`, smaller
/// than 1 MiB.
const SIZE_CAP: u64 = 1 << 20;

fn recompute_membership(root: &Path) -> Vec<String> {
    let out = std::process::Command::new("git")
        .args(["ls-files", "-z", "--", "*.json"])
        .current_dir(root)
        .output()
        .expect("`git ls-files` must run: the corpus is defined by what is COMMITTED");
    assert!(out.status.success(), "git ls-files failed: {:?}", out.status);
    let mut keep: Vec<String> = String::from_utf8(out.stdout)
        .expect("git printed non-UTF-8 paths")
        .split('\0')
        .filter(|p| !p.is_empty())
        .filter(|p| !p.starts_with("first-party/") && !p.starts_with("vendor/"))
        .filter(|p| std::fs::metadata(root.join(p)).map(|m| m.len() < SIZE_CAP).unwrap_or(false))
        .map(str::to_owned)
        .collect();
    keep.sort();
    keep
}

/// The sample-shift guard. A corpus that quietly SHRINKS reads as a green run,
/// which is the failure mode this exists for; growth is reported too, because
/// an unreviewed addition is an unreviewed input.
#[test]
fn corpus_membership_matches_the_pinned_manifest() {
    let root = repo_root();
    let pinned = manifest_paths();
    let actual = recompute_membership(&root);
    println!("  corpus membership: {} pinned, {} on disk", pinned.len(), actual.len());

    let pset: std::collections::BTreeSet<&str> = pinned.iter().map(String::as_str).collect();
    let aset: std::collections::BTreeSet<&str> = actual.iter().map(String::as_str).collect();
    let removed: Vec<&&str> = pset.difference(&aset).collect();
    let added: Vec<&&str> = aset.difference(&pset).collect();
    if removed.is_empty() && added.is_empty() {
        return;
    }
    let show = |v: &[&&str]| -> String {
        let mut s: String = v.iter().take(20).map(|p| format!("\n    {p}")).collect();
        if v.len() > 20 {
            s.push_str(&format!("\n    ... and {} more", v.len() - 20));
        }
        s
    };
    panic!(
        "the pinned corpus no longer matches the tree.\n  \
         GONE from the tree ({}):{}\n  \
         NEW in the tree ({}):{}\n  \
         Regenerate with the command in tests/corpus_manifest.txt and READ THE DIFF.",
        removed.len(),
        show(&removed),
        added.len(),
        show(&added),
    );
}

/// The SCOPE pin, and the standing answer to a question that keeps being asked.
///
/// `recompute_membership` drops a tracked `*.json` for exactly three documented
/// reasons: the `first-party/` submodule prefix, the `vendor/` prefix, and the
/// 1 MiB size cap. This test takes the FULL tracked set and checks that every
/// path the rule drops is dropped for one of those three — so a fourth
/// exclusion cannot be slipped into the rule, because it would drop paths this
/// test cannot account for. It is deliberately NOT written by calling the rule
/// twice: it re-derives the header's wording against `git ls-files` itself.
///
/// It exists because the cheap answer to this gate's churn is "stop sampling
/// `reports/`", and that answer is wrong. Measured 2026-09-18: dropping that
/// one directory takes `non-ASCII key` from 4 documents to 1 (floor 2) and
/// `empty object` from 96 to 47 (floor 50) — the bulk machine-generated
/// directory is also the rare-construct carrier. The manifest header holds the
/// full table. Narrowing the sample by directory is the shrinking-corpus hazard
/// by another name, and it has to be argued, not typed.
#[test]
fn the_membership_rule_is_exactly_the_documented_rule() {
    let root = repo_root();
    let out = std::process::Command::new("git")
        .args(["ls-files", "-z", "--", "*.json"])
        .current_dir(&root)
        .output()
        .expect("`git ls-files` must run: the corpus is defined by what is COMMITTED");
    assert!(out.status.success(), "git ls-files failed: {:?}", out.status);
    let all: Vec<String> = String::from_utf8(out.stdout)
        .expect("git printed non-UTF-8 paths")
        .split('\0')
        .filter(|p| !p.is_empty())
        .map(str::to_owned)
        .collect();

    let kept: std::collections::BTreeSet<String> =
        recompute_membership(&root).into_iter().collect();

    let mut unaccounted: Vec<String> = Vec::new();
    for p in &all {
        if kept.contains(p) {
            continue;
        }
        // A tracked path with no readable metadata is counted as dropped by the
        // size cap, which is what `recompute_membership` does with it too; it
        // cannot happen in a clean worktree and must not redden this test.
        let oversized =
            std::fs::metadata(root.join(p)).map(|m| m.len() >= SIZE_CAP).unwrap_or(true);
        if !(p.starts_with("first-party/") || p.starts_with("vendor/") || oversized) {
            unaccounted.push(p.clone());
        }
    }
    println!(
        "  membership rule: {} tracked *.json, {} sampled, {} excluded",
        all.len(),
        kept.len(),
        all.len() - kept.len()
    );
    assert!(
        unaccounted.is_empty(),
        "the membership rule drops {} path(s) for a reason the manifest header does \
         not document. A fourth exclusion narrows the SAMPLE, which is the \
         shrinking-corpus hazard under another name — argue it in the header and \
         here, or do not make it:{}",
        unaccounted.len(),
        unaccounted.iter().take(20).map(|p| format!("\n    {p}")).collect::<String>(),
    );
}

/// The corpus differential. Read the module header for the four legs.
#[test]
fn corpus_round_trips_byte_for_byte() {
    let root = repo_root();
    let paths = manifest_paths();
    assert!(paths.len() > 2000, "manifest is suspiciously small: {}", paths.len());

    let mut accepted = 0usize;
    let mut rejected = 0usize;
    let mut bytes = 0usize;
    let mut failures: Vec<String> = Vec::new();

    for rel in &paths {
        let src = match std::fs::read(root.join(rel)) {
            Ok(b) => b,
            Err(e) => {
                failures.push(format!("{rel}: unreadable: {e}"));
                continue;
            }
        };
        bytes += src.len();
        let ours = tj::from_slice(&src);
        let theirs = inc_from_slice(&src);

        match (&ours, &theirs) {
            (Ok(a), Ok(b)) => {
                accepted += 1;
                if let Err(why) = same(a, b) {
                    failures.push(format!("{rel}: TREES DIFFER at {why}"));
                    continue;
                }
                let (mine_c, theirs_c) = (
                    tj::to_string(a).expect("compact write"),
                    inc::to_string(b).expect("compact write"),
                );
                if let Some(d) = first_difference(&mine_c, &theirs_c) {
                    failures.push(format!("{rel}: COMPACT BYTES DIFFER at {d}"));
                    continue;
                }
                let (mine_p, theirs_p) = (
                    tj::to_string_pretty(a).expect("pretty write"),
                    inc::to_string_pretty(b).expect("pretty write"),
                );
                if let Some(d) = first_difference(&mine_p, &theirs_p) {
                    failures.push(format!("{rel}: PRETTY BYTES DIFFER at {d}"));
                    continue;
                }
                // The CROSS leg: our reader on their bytes, their reader on
                // ours, both back to the original tree. Compact and pretty.
                for (label, mine_out, theirs_out) in [
                    ("compact", &mine_c, &theirs_c),
                    ("pretty", &mine_p, &theirs_p),
                ] {
                    let ours_on_theirs = match tj::from_str(theirs_out) {
                        Ok(v) => v,
                        Err(e) => {
                            failures.push(format!(
                                "{rel}: we REJECT the incumbent's own {label} output: {e}"
                            ));
                            continue;
                        }
                    };
                    let theirs_on_ours = match inc::from_str::<inc::Value>(mine_out) {
                        Ok(v) => v,
                        Err(e) => {
                            failures.push(format!(
                                "{rel}: the incumbent REJECTS our {label} output: {e}"
                            ));
                            continue;
                        }
                    };
                    if let Err(why) = same(&ours_on_theirs, &theirs_on_ours) {
                        failures.push(format!("{rel}: {label} CROSS re-parse differs at {why}"));
                    } else if let Err(why) = same(&ours_on_theirs, b) {
                        failures.push(format!("{rel}: {label} re-parse lost information at {why}"));
                    }
                }
            }
            (Err(a), Err(b)) => {
                rejected += 1;
                if (a.line(), a.column()) != (b.line(), b.column())
                    || a.to_string() != b.to_string()
                {
                    failures.push(format!(
                        "{rel}: both reject but differently:\n     ours: {a}\n   theirs: {b}"
                    ));
                }
            }
            (Ok(a), Err(b)) => failures.push(format!(
                "{rel}: WE ACCEPT, INCUMBENT REJECTS.\n   incumbent: {b}\n   our tree renders as: {}",
                truncate(&tj::to_string(a).unwrap_or_default())
            )),
            (Err(a), Ok(b)) => failures.push(format!(
                "{rel}: WE REJECT, INCUMBENT ACCEPTS.\n   ours: {a}\n   their tree renders as: {}",
                truncate(&inc::to_string(b).unwrap_or_default())
            )),
        }
    }

    println!(
        "  corpus differential: {} documents / {:.1} MiB — {accepted} accepted by both, \
         {rejected} rejected by both, {} disagreements",
        paths.len(),
        bytes as f64 / (1024.0 * 1024.0),
        failures.len()
    );
    assert!(
        failures.is_empty(),
        "{} corpus disagreement(s):\n{}",
        failures.len(),
        failures.iter().take(25).cloned().collect::<Vec<_>>().join("\n")
    );
}

fn truncate(s: &str) -> String {
    if s.len() <= 200 {
        s.to_owned()
    } else {
        let cut = (0..=200).rev().find(|i| s.is_char_boundary(*i)).unwrap_or(0);
        format!("{}… ({} bytes)", &s[..cut], s.len())
    }
}

/// Coverage floors for the corpus, measured with the INCUMBENT's parser so the
/// answer does not depend on the crate under test.
///
/// This is the other half of the sample pin. `corpus_membership_...` catches a
/// file disappearing; this catches the subtler version, where the file list is
/// unchanged but the CONTENT that exercised a hazard has been edited away — the
/// corpus keeps its size and quietly stops testing exponent floats.
#[test]
fn corpus_still_exercises_every_measured_construct() {
    let root = repo_root();
    let mut n: std::collections::BTreeMap<&str, usize> = Default::default();

    fn census(v: &inc::Value, depth: usize, hit: &mut dyn FnMut(&'static str)) {
        if depth >= 5 {
            hit("nesting depth >= 5");
        }
        match v {
            inc::Value::Null => hit("null"),
            inc::Value::Bool(_) => hit("bool"),
            inc::Value::Number(x) => {
                if let Some(f) = x.as_f64().filter(|_| x.is_f64()) {
                    hit("float");
                    if f.fract() != 0.0 {
                        hit("non-integral float");
                    }
                    // The rendered form is what this crate can get wrong.
                    if inc::to_string(x).unwrap_or_default().contains('e') {
                        hit("exponent-notation float");
                    }
                }
                if x.as_i64().is_some_and(|i| i < 0) || x.as_f64().is_some_and(|f| f < 0.0) {
                    hit("negative number");
                }
                if x.as_u64().is_some_and(|u| u > (1u64 << 53))
                    || x.as_i64().is_some_and(|i| i < -(1i64 << 53))
                {
                    hit("integer beyond 2^53");
                }
            }
            inc::Value::String(s) => {
                if s.is_empty() {
                    hit("empty string");
                }
                if s.chars().any(|c| c < ' ') {
                    hit("control character in a string");
                }
                if s.contains('"') || s.contains('\\') {
                    hit("quote or backslash in a string");
                }
                if !s.is_ascii() {
                    hit("non-ASCII string");
                }
            }
            inc::Value::Array(a) => {
                if a.is_empty() {
                    hit("empty array");
                }
                for e in a {
                    census(e, depth + 1, hit);
                }
            }
            inc::Value::Object(o) => {
                if o.is_empty() {
                    hit("empty object");
                }
                if o.keys().any(|k| k.is_empty()) {
                    hit("empty key");
                }
                if o.keys().any(|k| !k.is_ascii()) {
                    hit("non-ASCII key");
                }
                for (_, e) in o {
                    census(e, depth + 1, hit);
                }
            }
        }
    }

    for rel in manifest_paths() {
        let Ok(src) = std::fs::read(root.join(&rel)) else { continue };
        let Ok(v) = inc::from_slice::<inc::Value>(&src) else { continue };
        let mut seen: std::collections::BTreeSet<&'static str> = Default::default();
        census(&v, 0, &mut |k| {
            seen.insert(k);
        });
        for k in seen {
            *n.entry(k).or_default() += 1;
        }
    }

    // Floors, not equalities: measured 2026-08-23 (the number in the comment)
    // and set below it, so ordinary churn does not redden the gate but a
    // construct vanishing does.
    //
    // READ THE FLOAT ROWS BEFORE TRUSTING THIS CORPUS. A text-pattern estimate
    // of the same corpus said "336 documents contain an exponent float"; the
    // value-level census below says FIVE. The regex was counting `e`s inside
    // strings — version numbers, hashes, identifiers, hex — none of which reach
    // the float writer. The corpus is float-POOR, and that is not a defect in
    // the corpus: 2954 hand- and machine-written JSON documents from a compiler
    // repository simply do not contain many floats.
    //
    // The consequence is a division of labour, and it is the reason both test
    // binaries exist. The corpus covers breadth — real key sets, real nesting,
    // real escapes, real integers — and is nearly silent on the single hazard
    // this crate is most likely to get wrong. Float byte-exactness is carried
    // by `differential_json.rs`, which draws millions of bit patterns precisely
    // because no realistic corpus would find the 0.025% tie-break disagreement.
    // Neither file is sufficient alone; do not delete either on the grounds
    // that the other is green.
    let floors: &[(&str, usize)] = &[
        ("null", 2000),                         // 2593
        ("bool", 2000),                         // 2730
        ("float", 60),                          //   89  <- see the note above
        ("non-integral float", 55),             //   82
        ("exponent-notation float", 3),         //    5  <- and this one
        ("negative number", 300),               //  512
        ("integer beyond 2^53", 200),           //  399
        ("empty string", 40),                   //   54
        ("control character in a string", 20),  // 51
        ("quote or backslash in a string", 50), // 72
        ("non-ASCII string", 10),               //   29
        ("non-ASCII key", 2),                   //    4
        ("empty array", 2000),                  // 2662
        ("empty object", 50),                   //   79
        ("empty key", 2),                       //    5
        ("nesting depth >= 5", 500),            // 2658
    ];
    let mut short = Vec::new();
    for (k, floor) in floors {
        let got = n.get(k).copied().unwrap_or(0);
        println!("  {k:<32} {got:>5} documents (floor {floor})");
        if got < *floor {
            short.push(format!("{k}: {got} documents, floor {floor}"));
        }
    }
    // Anything the census found that has no floor is printed but not gated, so
    // a new construct shows up in the log before someone has to think about it.
    for (k, v) in &n {
        if !floors.iter().any(|(f, _)| f == k) {
            println!("  {k:<32} {v:>5} documents (ungated)");
        }
    }
    assert!(short.is_empty(), "the corpus stopped exercising:\n  {}", short.join("\n  "));
}

// ===========================================================================
// 2. THE BYTE-EXACTNESS HAZARDS, AS WHOLE DOCUMENTS
// ===========================================================================

/// Every hazard the JSON brief names, expressed as a document rather than as a
/// scalar, so that the writer's *document* path (separators, key order, nesting)
/// is exercised at the same time as the scalar path.
///
/// `differential_json.rs` already sweeps each hazard over millions of generated
/// values. This table exists for a different reason: it is READABLE. When one
/// of these fails, the failure names the hazard, and the expected byte string is
/// written out here so a reviewer can see what the incumbent does without
/// running it.
#[test]
fn the_byte_exactness_hazard_table_round_trips() {
    let cases: &[(&str, &str, &str)] = &[
        // (name, input document, the incumbent's compact re-serialization)
        ("positive exponent carries a SIGN", r#"{"a":1e30}"#, r#"{"a":1e+30}"#),
        // `1e-30` is not representable; the correctly-rounded `f64` renders
        // back as `1e-30`. This row used to expect `9.999999999999999e-31`,
        // the one-ulp-low value of serde_json's imprecise DEFAULT parse. That
        // stopped being the incumbent when first-party/clean 99ddfe452 enabled
        // `float_roundtrip` in clean-olean (unified into every `serde_json` in
        // the graph; trust-json's Cargo.toml now names it on the oracle), and
        // trust-json's parser became correctly rounded to match. The byte
        // requirement is unchanged: agree with the incumbent exactly.
        ("negative exponent, no padding", r#"{"a":1e-30}"#, r#"{"a":1e-30}"#),
        ("exponent is not zero-padded", r#"{"a":1e5}"#, r#"{"a":100000.0}"#),
        ("f64 threshold, low end", r#"[1e-5,1e-6]"#, "[0.00001,1e-6]"),
        ("f64 threshold, high end", r#"[1e15,1e16]"#, "[1000000000000000.0,1e+16]"),
        ("integral floats keep .0", r#"{"a":1.0,"b":-2.0}"#, r#"{"a":1.0,"b":-2.0}"#),
        ("ties round to even", "[810553441865041.25]", "[810553441865041.2]"),
        ("negative zero is a float", r#"{"z":-0}"#, r#"{"z":-0.0}"#),
        ("underflow to zero, not an error", "[1e-400]", "[0.0]"),
        ("subnormal minimum", "[5e-324]", "[5e-324]"),
        ("f64 maximum", "[1.7976931348623157e308]", "[1.7976931348623157e+308]"),
        ("i64::MIN keeps its sign", "[-9223372036854775808]", "[-9223372036854775808]"),
        ("u64::MAX stays an integer", "[18446744073709551615]", "[18446744073709551615]"),
        ("2^53+1 is exact as an integer", "[9007199254740993]", "[9007199254740993]"),
        ("solidus is NOT escaped", r#"["a/b"]"#, r#"["a/b"]"#),
        ("DEL is NOT escaped", "[\"\u{7f}\"]", "[\"\u{7f}\"]"),
        ("U+2028/29 pass through", "[\"\u{2028}\u{2029}\"]", "[\"\u{2028}\u{2029}\"]"),
        // NB: the inputs here are ESCAPED text, not raw control bytes. A raw
        // control byte inside a string is malformed JSON and both sides reject
        // it -- which is asserted separately, in the rejection table.
        ("short escapes are the named ones", r#"["\b\t\n\f\r\"\\"]"#, r#"["\b\t\n\f\r\"\\"]"#),
        (
            "other controls are lowercase \\u",
            r#"["\u0000\u0001\u001F"]"#,
            r#"["\u0000\u0001\u001f"]"#,
        ),
        ("an escaped DEL is UNescaped on the way out", r#"["\u007f"]"#, "[\"\u{7f}\"]"),
        ("a \\u escape of a printable char is folded", r#"["\u0041\u00e9"]"#, "[\"Aé\"]"),
        ("surrogate pairs fold to one char", r#"["\ud834\udd1e"]"#, "[\"𝄞\"]"),
        (
            "object keys sort, and sort by BYTES",
            r#"{"z":0,"a":0,"A":0,"":0,"é":0,"~":0}"#,
            r#"{"":0,"A":0,"a":0,"z":0,"~":0,"é":0}"#,
        ),
        ("duplicate keys: last wins", r#"{"a":1,"a":2,"a":3}"#, r#"{"a":3}"#),
        ("a key needing escapes is escaped", "{\"a\\nb\":1}", r#"{"a\nb":1}"#),
    ];

    let mut bad = Vec::new();
    for (name, src, expect) in cases {
        let (ours, theirs) = match (tj::from_str(src), inc_from_str(src)) {
            (Ok(a), Ok(b)) => (a, b),
            // Both rejecting is an error in THIS TABLE, not in the crate, and
            // saying so is the difference between a five-minute fix and an
            // afternoon spent looking at the parser. (It happened: three rows
            // were first written with raw control bytes inside the string,
            // which is malformed JSON that both sides correctly refuse.)
            (Err(a), Err(b)) => {
                bad.push(format!(
                    "{name}: BOTH rejected {src:?} — the table row is malformed, not the crate\n     ours: {a}\n   theirs: {b}"
                ));
                continue;
            }
            (Ok(_), Err(b)) => {
                bad.push(format!("{name}: we accepted {src:?}, the incumbent rejected it: {b}"));
                continue;
            }
            (Err(a), Ok(_)) => {
                bad.push(format!("{name}: we rejected {src:?}, the incumbent accepted it: {a}"));
                continue;
            }
        };
        if let Err(why) = same(&ours, &theirs) {
            bad.push(format!("{name}: trees differ for {src:?}: {why}"));
            continue;
        }
        let (o, t) = (tj::to_string(&ours).unwrap(), inc::to_string(&theirs).unwrap());
        if o != t {
            bad.push(format!("{name}: {src:?}\n     ours: {o}\n   theirs: {t}"));
            continue;
        }
        // The literal is the third column so the table documents the incumbent
        // without anyone having to run it. If the incumbent moves, THIS is what
        // fires, and the fix is to re-read the incumbent, not to edit our crate.
        if &t.as_str() != expect {
            bad.push(format!(
                "{name}: the INCUMBENT changed for {src:?}\n   expected: {expect}\n        got: {t}"
            ));
        }
    }
    assert!(bad.is_empty(), "{} hazard(s):\n{}", bad.len(), bad.join("\n"));
}

/// Empty containers, in every position they can occur, compact and pretty.
///
/// The hazard is specific: `serde_json`'s pretty writer emits `{}` and `[]` with
/// no interior newline or indent, but `{"a": 1}` with both. An implementation
/// that treats "write the opener, write the entries, write the closer"
/// uniformly produces `{\n}` and is still valid JSON, still round-trips, and
/// still differs in every byte-hash downstream.
#[test]
fn empty_containers_are_byte_identical_compact_and_pretty() {
    let cases = [
        "{}",
        "[]",
        r#""""#,
        "[[]]",
        "[{}]",
        "[[],[]]",
        "[{},{}]",
        r#"{"a":{}}"#,
        r#"{"a":[]}"#,
        r#"{"a":{},"b":[]}"#,
        r#"{"":""}"#,
        r#"{"a":[[],{}],"b":{"c":{},"d":[]}}"#,
        "[[[[]]]]",
        r#"{"a":{"b":{"c":{}}}}"#,
        r#"[1,[],2,{},3]"#,
        r#"{"a":1,"b":{},"c":2,"d":[],"e":3}"#,
        r#"[{"a":[]},[{}]]"#,
        r#"{"a":[{},[]],"b":[[],{}]}"#,
    ];
    for src in cases {
        let ours = tj::from_str(src).unwrap_or_else(|e| panic!("we rejected {src:?}: {e}"));
        let theirs =
            inc_from_str(src).unwrap_or_else(|e| panic!("incumbent rejected {src:?}: {e}"));
        same(&ours, &theirs).unwrap_or_else(|w| panic!("{src:?}: {w}"));
        assert_eq!(
            tj::to_string(&ours).unwrap(),
            inc::to_string(&theirs).unwrap(),
            "compact {src:?}"
        );
        let (o, t) =
            (tj::to_string_pretty(&ours).unwrap(), inc::to_string_pretty(&theirs).unwrap());
        assert_eq!(o, t, "pretty {src:?}\n     ours: {o:?}\n   theirs: {t:?}");
        assert_eq!(tj::to_vec(&ours).unwrap(), inc::to_vec(&theirs).unwrap(), "to_vec {src:?}");
        assert_eq!(
            tj::to_vec_pretty(&ours).unwrap(),
            inc::to_vec_pretty(&theirs).unwrap(),
            "to_vec_pretty {src:?}"
        );
    }
    // Spelled out, so a reviewer can see the rule without running anything.
    let v: tj::Value = tj::from_str(r#"{"e":{},"f":[],"g":{"h":[]}}"#).unwrap();
    assert_eq!(
        tj::to_string_pretty(&v).unwrap(),
        "{\n  \"e\": {},\n  \"f\": [],\n  \"g\": {\n    \"h\": []\n  }\n}"
    );
}

/// Deep nesting, in all three shapes, across the limit.
///
/// `differential_json.rs` walks bracket depth for arrays. Objects reach the same
/// counter through a different code path and the mixed shape through a third, so
/// an off-by-one that only affects one of them is invisible to the array sweep.
#[test]
fn deep_nesting_agrees_at_and_around_the_limit() {
    fn arrays(d: usize) -> String {
        "[".repeat(d) + &"]".repeat(d)
    }
    fn objects(d: usize) -> String {
        let mut s = String::new();
        for _ in 0..d {
            s.push_str("{\"a\":");
        }
        s.push('1');
        for _ in 0..d {
            s.push('}');
        }
        s
    }
    fn mixed(d: usize) -> String {
        // Each iteration adds TWO levels, so this crosses the limit at half the
        // nominal depth -- a different arithmetic than either pure shape.
        let mut s = String::new();
        for _ in 0..d {
            s.push_str("[{\"a\":");
        }
        s.push_str("null");
        for _ in 0..d {
            s.push_str("}]");
        }
        s
    }

    let mut boundary = Vec::new();
    for (name, build) in
        [("array", arrays as fn(usize) -> String), ("object", objects), ("mixed", mixed)]
    {
        let mut last_ok = None;
        for d in 1..=200usize {
            let s = build(d);
            let ours = tj::from_str(&s);
            let theirs = inc_from_str(&s);
            assert_eq!(
                ours.is_ok(),
                theirs.is_ok(),
                "{name} depth {d}: ours ok={} theirs ok={}\n   ours: {}\n theirs: {}",
                ours.is_ok(),
                theirs.is_ok(),
                ours.as_ref().err().map(ToString::to_string).unwrap_or_default(),
                theirs.as_ref().err().map(ToString::to_string).unwrap_or_default(),
            );
            match (&ours, &theirs) {
                (Ok(a), Ok(b)) => {
                    last_ok = Some(d);
                    same(a, b).unwrap_or_else(|w| panic!("{name} depth {d}: {w}"));
                    assert_eq!(
                        tj::to_string(a).unwrap(),
                        inc::to_string(b).unwrap(),
                        "{name} depth {d} compact"
                    );
                    assert_eq!(
                        tj::to_string_pretty(a).unwrap(),
                        inc::to_string_pretty(b).unwrap(),
                        "{name} depth {d} pretty"
                    );
                }
                (Err(a), Err(b)) => assert_eq!(
                    (a.line(), a.column(), a.to_string()),
                    (b.line(), b.column(), b.to_string()),
                    "{name} depth {d}: rejection differs"
                ),
                _ => unreachable!("agreement asserted above"),
            }
        }
        let d = last_ok.expect("some depth must parse");
        println!("  {name:<7} deepest accepted depth: {d}");
        boundary.push((name, d));
    }
    // Pin the boundary itself. Agreement alone would still be satisfied if BOTH
    // limits moved, which cannot happen here (only one side is ours) -- but it
    // records what the number is, which is the thing a reader wants.
    //
    // 127, not 128: the limit constant is 128 and it is spent on the OUTERMOST
    // container, so 127 further ones fit. `mixed` adds two levels per iteration
    // and lands on 63 because 64 would need 128 levels plus the outermost.
    assert_eq!(
        boundary,
        vec![("array", 127), ("object", 127), ("mixed", 63)],
        "the recursion boundary moved"
    );

    // The one leg `differential_json.rs` could not drive, now that the trait
    // crate is a dev-dependency: lifting the limit must work on BOTH sides.
    let deep = arrays(300);
    let mut ours = tj::Deserializer::from_str(&deep).disable_recursion_limit();
    let mut de = inc::Deserializer::from_str(&deep);
    de.disable_recursion_limit();
    let theirs = inc::Value::deserialize(&mut de).expect("incumbent, limit lifted");
    let ours = ours.parse_value().expect("ours, limit lifted");
    same(&ours, &theirs).expect("300-deep tree with the limit lifted");
    assert!(tj::from_str(&deep).is_err() && inc::from_str::<inc::Value>(&deep).is_err());
}

// ===========================================================================
// 3. THE TYPED LENS — one derive, two trees
// ===========================================================================

// `#[serde(crate = "...")]` on every derived type below is NOT optional here,
// and the failure it prevents is worth recording because it is silent-adjacent.
//
// `serde_derive` emits `extern crate serde as _serde;`. The dev-dependency is
// RENAMED to `incumbent-serde` (so the gate can never accidentally resolve to a
// future `trust-serde`), so no crate named `serde` is in the extern prelude —
// and this sysroot SHIPS one, `rustc_private`'s. Without the attribute the
// derive silently binds to the compiler's internal serde and the build dies 89
// errors deep in `E0658: use of unstable library feature 'rustc_private'` and
// `cannot find '__private229' in '_serde'`, neither of which names the cause.
#[derive(Debug, PartialEq, Deserialize)]
#[serde(crate = "incumbent_serde", deny_unknown_fields)]
struct Release {
    name: String,
    channel: Channel,
    build: u64,
    #[serde(default)]
    tags: Vec<String>,
    note: Option<String>,
    limits: Option<Limits>,
    ratio: f64,
    signed: bool,
}

#[derive(Debug, PartialEq, Deserialize)]
#[serde(crate = "incumbent_serde", rename_all = "lowercase")]
enum Channel {
    Stable,
    Beta,
    Trust,
}

#[derive(Debug, PartialEq, Deserialize)]
#[serde(crate = "incumbent_serde", deny_unknown_fields)]
struct Limits {
    max: i64,
    min: i64,
}

/// A valid document, and the mutations of it that each exercise one typed
/// failure the brief names.
fn typed_cases() -> Vec<(&'static str, &'static str)> {
    vec![
        (
            "everything present",
            r#"{"name":"trust","channel":"trust","build":42,"tags":["a","b"],"note":"hi","limits":{"max":9,"min":-9},"ratio":0.5,"signed":true}"#,
        ),
        (
            "optional fields ABSENT",
            r#"{"name":"trust","channel":"stable","build":1,"ratio":0.5,"signed":false}"#,
        ),
        (
            "optional fields NULL",
            r#"{"name":"trust","channel":"stable","build":1,"note":null,"limits":null,"ratio":0.5,"signed":false}"#,
        ),
        (
            "defaulted field absent",
            r#"{"name":"trust","channel":"beta","build":1,"note":null,"limits":null,"ratio":0.5,"signed":false}"#,
        ),
        (
            "defaulted field null",
            r#"{"name":"trust","channel":"beta","build":1,"tags":null,"ratio":0.5,"signed":false}"#,
        ),
        (
            "MISSING required scalar",
            r#"{"name":"trust","channel":"stable","ratio":0.5,"signed":false}"#,
        ),
        ("MISSING required string", r#"{"channel":"stable","build":1,"ratio":0.5,"signed":false}"#),
        (
            "UNKNOWN field at the top",
            r#"{"name":"t","channel":"stable","build":1,"ratio":0.5,"signed":false,"extra":1}"#,
        ),
        (
            "UNKNOWN field when nested",
            r#"{"name":"t","channel":"stable","build":1,"ratio":0.5,"signed":false,"limits":{"max":1,"min":2,"mid":3}}"#,
        ),
        (
            "MISSING field when nested",
            r#"{"name":"t","channel":"stable","build":1,"ratio":0.5,"signed":false,"limits":{"max":1}}"#,
        ),
        (
            "WRONG type: string for u64",
            r#"{"name":"t","channel":"stable","build":"1","ratio":0.5,"signed":false}"#,
        ),
        (
            "WRONG type: negative for u64",
            r#"{"name":"t","channel":"stable","build":-1,"ratio":0.5,"signed":false}"#,
        ),
        (
            "WRONG type: float for u64",
            r#"{"name":"t","channel":"stable","build":1.5,"ratio":0.5,"signed":false}"#,
        ),
        (
            "WRONG type: string for bool",
            r#"{"name":"t","channel":"stable","build":1,"ratio":0.5,"signed":"true"}"#,
        ),
        (
            "WRONG type: null for String",
            r#"{"name":null,"channel":"stable","build":1,"ratio":0.5,"signed":false}"#,
        ),
        (
            "WRONG type: object for i64",
            r#"{"name":"t","channel":"stable","build":1,"ratio":0.5,"signed":false,"limits":3}"#,
        ),
        (
            "WRONG type: number in a Vec<String>",
            r#"{"name":"t","channel":"stable","build":1,"tags":["a",1],"ratio":0.5,"signed":false}"#,
        ),
        (
            "INT where a float is wanted",
            r#"{"name":"t","channel":"stable","build":1,"ratio":2,"signed":false}"#,
        ),
        (
            "UNKNOWN enum variant",
            r#"{"name":"t","channel":"nightly","build":1,"ratio":0.5,"signed":false}"#,
        ),
        (
            "enum variant with wrong case",
            r#"{"name":"t","channel":"Stable","build":1,"ratio":0.5,"signed":false}"#,
        ),
        (
            "u64 boundary",
            r#"{"name":"t","channel":"stable","build":18446744073709551615,"ratio":0.5,"signed":false}"#,
        ),
        (
            "u64 boundary + 1 (overflows)",
            r#"{"name":"t","channel":"stable","build":18446744073709551616,"ratio":0.5,"signed":false}"#,
        ),
        ("top level is an array", r#"[{"name":"t"}]"#),
        ("top level is a scalar", r#"7"#),
        (
            "DUPLICATE required key",
            r#"{"name":"t","channel":"stable","build":1,"build":2,"ratio":0.5,"signed":false}"#,
        ),
        (
            "DUPLICATE optional key",
            r#"{"name":"t","channel":"stable","build":1,"note":"a","note":"b","ratio":0.5,"signed":false}"#,
        ),
    ]
}

fn render<T: std::fmt::Debug>(r: &Result<T, inc::Error>) -> String {
    match r {
        Ok(v) => format!("Ok({v:?})"),
        Err(e) => format!("Err({e})"),
    }
}

/// THE typed differential: the same `#[derive(Deserialize)]`, driven once from
/// our tree and once from the incumbent's, must reach the same verdict.
///
/// Both sides go through `serde_json::from_value`, so the derive, the visitor
/// and the error text are literally the same code; the ONLY difference between
/// the two runs is which parser built the tree. Any disagreement is therefore a
/// defect in this crate, and it is reported with the input and both verdicts.
#[test]
fn one_derive_two_trees_reach_the_same_verdict() {
    let mut bad = Vec::new();
    let mut ok = 0usize;
    let mut err = 0usize;
    for (name, src) in typed_cases() {
        let ours_tree = match tj::from_str(src) {
            Ok(v) => to_inc(&v),
            Err(e) => {
                // A parse failure is a legitimate outcome; the incumbent must
                // share it. That leg is `agree_on_parse`, applied below.
                bad.push(format!("{name}: we failed to PARSE {src:?}: {e}"));
                continue;
            }
        };
        let theirs_tree = match inc_from_str(src) {
            Ok(v) => v,
            Err(e) => {
                bad.push(format!("{name}: the incumbent failed to PARSE {src:?}: {e}"));
                continue;
            }
        };
        let ours = inc::from_value::<Release>(ours_tree);
        let theirs = inc::from_value::<Release>(theirs_tree);
        match (&ours, &theirs) {
            (Ok(a), Ok(b)) if a == b => ok += 1,
            (Err(a), Err(b)) if a.to_string() == b.to_string() => err += 1,
            _ => bad.push(format!(
                "{name}\n    input: {src}\n     ours: {}\n   theirs: {}",
                render(&ours),
                render(&theirs)
            )),
        }
        // ... and the raw text must be accepted or rejected identically by the
        // two PARSERS as well, which is a separate claim from the typed one.
        agree_on_parse(src);
    }
    println!(
        "  typed lens: {} cases — {ok} deserialized, {err} rejected, {} disagreements",
        typed_cases().len(),
        bad.len()
    );
    assert!(bad.is_empty(), "{} typed disagreement(s):\n{}", bad.len(), bad.join("\n"));
}

/// The verdicts themselves, pinned.
///
/// `one_derive_two_trees_reach_the_same_verdict` proves the two trees AGREE. It
/// would still pass if both trees became garbage in the same way. This test
/// says what the answers are.
#[test]
fn the_typed_verdicts_are_what_the_incumbent_says_they_are() {
    let expect: &[(&str, &str)] = &[
        ("everything present", "Ok"),
        ("optional fields ABSENT", "Ok"),
        ("optional fields NULL", "Ok"),
        ("defaulted field absent", "Ok"),
        ("defaulted field null", "Err(invalid type: null, expected a sequence)"),
        ("MISSING required scalar", "Err(missing field `build`)"),
        ("MISSING required string", "Err(missing field `name`)"),
        (
            "UNKNOWN field at the top",
            "Err(unknown field `extra`, expected one of `name`, `channel`, `build`, `tags`, `note`, `limits`, `ratio`, `signed`)",
        ),
        ("UNKNOWN field when nested", "Err(unknown field `mid`, expected `max` or `min`)"),
        ("MISSING field when nested", "Err(missing field `min`)"),
        ("WRONG type: string for u64", "Err(invalid type: string \"1\", expected u64)"),
        ("WRONG type: negative for u64", "Err(invalid value: integer `-1`, expected u64)"),
        ("WRONG type: float for u64", "Err(invalid type: floating point `1.5`, expected u64)"),
        ("WRONG type: string for bool", "Err(invalid type: string \"true\", expected a boolean)"),
        ("WRONG type: null for String", "Err(invalid type: null, expected a string)"),
        ("WRONG type: object for i64", "Err(invalid type: integer `3`, expected struct Limits)"),
        (
            "WRONG type: number in a Vec<String>",
            "Err(invalid type: integer `1`, expected a string)",
        ),
        ("INT where a float is wanted", "Ok"),
        (
            "UNKNOWN enum variant",
            "Err(unknown variant `nightly`, expected one of `stable`, `beta`, `trust`)",
        ),
        (
            "enum variant with wrong case",
            "Err(unknown variant `Stable`, expected one of `stable`, `beta`, `trust`)",
        ),
        ("u64 boundary", "Ok"),
        // Two rows that were guessed wrong and corrected against the incumbent,
        // both worth keeping for what they reveal:
        //   * the overflow message renders the float through serde_json's OWN
        //     writer (`1.8446744073709552e+19`), not Rust's `{}`
        //     (`18446744073709552000`) -- so even an ERROR STRING is a byte
        //     observable of the float backend;
        //   * `deserialize_struct` accepts a SEQUENCE (the tuple form), so a
        //     top-level array is not rejected as "expected a struct"; it is
        //     accepted as a field list and fails on the first field's type.
        (
            "u64 boundary + 1 (overflows)",
            "Err(invalid type: floating point `1.8446744073709552e+19`, expected u64)",
        ),
        ("top level is an array", "Err(invalid type: map, expected a string)"),
        ("top level is a scalar", "Err(invalid type: integer `7`, expected struct Release)"),
        ("DUPLICATE required key", "Ok"),
        ("DUPLICATE optional key", "Ok"),
    ];
    let cases = typed_cases();
    assert_eq!(cases.len(), expect.len(), "the table and the case list disagree");
    let mut bad = Vec::new();
    for ((name, src), (ename, want)) in cases.iter().zip(expect) {
        assert_eq!(name, ename, "table order");
        let got = inc::from_value::<Release>(to_inc(&tj::from_str(src).unwrap()));
        let got_s = match &got {
            Ok(_) => "Ok".to_owned(),
            Err(e) => format!("Err({e})"),
        };
        if got_s != *want {
            bad.push(format!("{name}\n    input: {src}\n   wanted: {want}\n      got: {got_s}"));
        }
    }
    assert!(bad.is_empty(), "{} verdict(s) moved:\n{}", bad.len(), bad.join("\n"));
}

/// `Option::None` vs a missing field — the three levels at which they differ,
/// and the one at which they do not.
///
/// This is the case the brief singles out, and it is worth spelling out because
/// the answer is "it depends which layer you ask":
///
/// * in the TREE they are different: one object has the key, the other does not;
/// * in the BYTES they are different, and stay different through a round trip;
/// * after `#[derive(Deserialize)]` they are the SAME — both give `None`.
///
/// The consequence for the deferred serde layer is a design constraint, not a
/// curiosity: serialization is not the inverse of deserialization here, so
/// `trust-serde` must decide `skip_serializing_if` explicitly. If it does not,
/// a bundle that was read from `{}` gets written back as `{"note":null}` and
/// every digest downstream moves.
#[test]
fn a_missing_field_and_an_explicit_null_are_distinct_in_the_tree() {
    let absent = r#"{"name":"t","channel":"stable","build":1,"ratio":0.5,"signed":false}"#;
    let explicit =
        r#"{"name":"t","channel":"stable","build":1,"note":null,"ratio":0.5,"signed":false}"#;

    // Level 1: the tree. Both implementations must draw the same distinction.
    let (oa, ea) = (tj::from_str(absent).unwrap(), tj::from_str(explicit).unwrap());
    let (ob, eb) = (inc_from_str(absent).unwrap(), inc_from_str(explicit).unwrap());
    assert!(oa.get("note").is_none(), "ours: an absent key must not materialise");
    assert!(ob.get("note").is_none(), "incumbent: an absent key must not materialise");
    assert_eq!(ea.get("note").map(|v| v.is_null()), Some(true), "ours: explicit null");
    assert_eq!(eb.get("note").map(|v| v.is_null()), Some(true), "incumbent: explicit null");
    same(&oa, &ob).unwrap();
    same(&ea, &eb).unwrap();

    // Level 2: the bytes. Different, and identically different on both sides.
    assert_eq!(tj::to_string(&oa).unwrap(), inc::to_string(&ob).unwrap());
    assert_eq!(tj::to_string(&ea).unwrap(), inc::to_string(&eb).unwrap());
    assert_ne!(
        tj::to_string(&oa).unwrap(),
        tj::to_string(&ea).unwrap(),
        "the two documents must NOT round-trip to the same bytes"
    );

    // Level 3: the derive. The same, and the same on both sides.
    for (label, ours_tree, theirs_tree) in [("absent", &oa, &ob), ("explicit null", &ea, &eb)] {
        let ours = inc::from_value::<Release>(to_inc(ours_tree)).expect(label);
        let theirs = inc::from_value::<Release>(theirs_tree.clone()).expect(label);
        assert_eq!(ours, theirs, "{label}");
        assert_eq!(ours.note, None, "{label}: serde collapses both to None");
        assert_eq!(ours.limits, None, "{label}");
    }
}

/// Duplicate keys: the streaming reader and the tree reader DISAGREE, on the
/// incumbent, by design — and the disagreement is a constraint on the layer this
/// crate has not built yet.
///
/// `serde_json::from_str::<Struct>` sees the fields one at a time and rejects
/// the second `build` with *"duplicate field"*. `from_value::<Struct>` sees a
/// map that has already collapsed to last-wins and accepts. Neither is wrong;
/// they are different code paths.
///
/// It is recorded here because the obvious way to build `trust-serde` — parse to
/// a `Value`, then deserialize the `Value` — silently loses the duplicate-field
/// rejection, and duplicate-field rejection is a real defence for a format that
/// carries proof obligations. A future `trust-serde` streaming deserializer must
/// reproduce the streaming behaviour; a `Value`-based one must not claim to.
#[test]
fn duplicate_keys_collapse_in_the_tree_but_are_rejected_by_the_streaming_reader() {
    let src = r#"{"name":"t","channel":"stable","build":1,"build":2,"ratio":0.5,"signed":false}"#;

    // Both PARSERS collapse identically, last wins. This is the claim about us.
    let ours = tj::from_str(src).unwrap();
    let theirs = inc_from_str(src).unwrap();
    same(&ours, &theirs).unwrap();
    assert_eq!(ours.get("build").unwrap().as_u64(), Some(2));
    assert_eq!(tj::to_string(&ours).unwrap(), inc::to_string(&theirs).unwrap());

    // Both TREES then deserialize, identically, without complaint.
    let via_ours = inc::from_value::<Release>(to_inc(&ours)).expect("tree path accepts");
    let via_theirs = inc::from_value::<Release>(theirs).expect("tree path accepts");
    assert_eq!(via_ours, via_theirs);
    assert_eq!(via_ours.build, 2);

    // The streaming path does NOT. This is a statement about the incumbent, and
    // it is the requirement the deferred serde layer inherits.
    let streamed = inc::from_str::<Release>(src);
    let msg = streamed.expect_err("streaming must reject a duplicate field").to_string();
    assert!(
        msg.starts_with("duplicate field `build`"),
        "the incumbent's streaming duplicate-field rejection changed: {msg}"
    );
}

// ===========================================================================
// 4. REJECTION AGREEMENT
// ===========================================================================

/// Trailing data, leading junk, and the near-misses around a complete value.
///
/// A reader that stops at the end of the first complete value and returns `Ok`
/// accepts `{"a":1} DROP TABLE` — it round-trips, it hashes, and it silently
/// discards whatever came after. Every case here must be REJECTED by both, at
/// the same position.
#[test]
fn trailing_data_and_leading_junk_are_rejected_identically() {
    let cases = [
        // trailing values
        "{} {}",
        "[] []",
        "1 2",
        "null null",
        "true false",
        "\"a\" \"b\"",
        "{}[]",
        "[]{}",
        "1,2",
        "{\"a\":1} garbage",
        "[1,2,3]]",
        "{\"a\":1}}",
        // trailing junk with no whitespace
        "1x",
        "truex",
        "nullx",
        "\"a\"x",
        "{}x",
        "[]x",
        "1.0.0",
        "1e5e5",
        "--1",
        "+1",
        "01",
        "1.",
        ".1",
        "1e",
        "1e+",
        // leading junk
        "x{}",
        " \u{feff}{}",
        "\u{feff}{}",
        ")",
        "'a'",
        // trailing whitespace and control bytes (whitespace is fine, the rest not)
        "{} ",
        "{}\n",
        "{}\t\r\n ",
        "{}\u{0}",
        "{}\u{b}",
        "{}\u{c}",
        // NUL and friends inside
        "[\u{0}]",
        "{\"a\"\u{0}:1}",
        // unterminated
        "\"",
        "\"\\",
        "\"\\u",
        "\"\\u00",
        "\"\\u00zz\"",
        "\"\\x\"",
        "\"a",
        "[\"a",
        // lone surrogates
        "\"\\ud834\"",
        "\"\\ud834x\"",
        "\"\\udd1e\"",
        "\"\\ud834\\ud834\"",
    ];
    for src in cases {
        agree_on_parse(src);
    }
    println!("  rejection agreement: {} inputs", cases.len());

    // ... and the whitespace forms that ARE allowed, so this test cannot pass by
    // rejecting everything.
    for src in ["{}", " {} ", "\t\r\n{}\n\r\t", "[]", "\n1\n", " null "] {
        assert!(tj::from_str(src).is_ok(), "we rejected valid {src:?}");
        assert!(inc::from_str::<inc::Value>(src).is_ok(), "incumbent rejected valid {src:?}");
        agree_on_parse(src);
    }
}
