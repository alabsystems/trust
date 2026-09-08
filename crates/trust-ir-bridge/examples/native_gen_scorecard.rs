// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0 or the MIT license.

//! Produce the `trust.native-gen-scorecard/v1` artifact over a committed dump
//! corpus — the corpus-walking half of
//! `trust_ir_bridge::native_gen_scorecard` (see that module's docs for why the
//! walk lives in an example: deriving an outcome needs trust-vcgen, which is
//! deliberately a dev-dependency).
//!
//! ```text
//! targo --unverified run -p trust-ir-bridge --example native_gen_scorecard -- \
//!     [--corpus DIR]... [--out FILE]
//! ```
//!
//! Default corpus root: `../trust-clean/fixtures` relative to the crate — the
//! same root the missing-obligation ratchet measures, so the two instruments
//! read the same population. The artifact goes to `--out` (or stdout) and a
//! human summary to stderr.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

use trust_ir_bridge::native_gen_scorecard::{
    CorpusLoss, FunctionOutcomeRow, NativeGenScorecard, classify_function,
};
use trust_types::VerifiableFunction;

/// Depth-first corpus discovery: every directory holding at least one `.json`
/// file (byte-identical policy to the ratchet's `dump_dirs`).
fn dump_dirs(root: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = std::fs::read_dir(root) else {
        return;
    };
    let mut has_json = false;
    let mut subdirs = Vec::new();
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            subdirs.push(path);
        } else if path.extension().and_then(|x| x.to_str()) == Some("json") {
            has_json = true;
        }
    }
    if has_json {
        out.push(root.to_path_buf());
    }
    for sub in subdirs {
        dump_dirs(&sub, out);
    }
}

/// trust-vcgen's VC set for one function, exactly as the ratchet derives it —
/// the flip's comparison input, not a new policy.
fn vcgen_vcs_for(
    func: &VerifiableFunction,
) -> (Vec<trust_types::VerificationCondition>, Vec<trust_types::VerificationCondition>) {
    let summaries = trust_vcgen::SummaryDatabase::new();
    let (solver_vcs, discharged) =
        trust_vcgen::generate_vcs_with_discharge_and_summaries(func, &summaries);
    (
        trust_vcgen::filter_vcs_by_level(solver_vcs, trust_types::ProofLevel::L1Functional),
        discharged.into_iter().map(|(vc, _)| vc).collect(),
    )
}

fn main() -> std::process::ExitCode {
    let mut corpus_roots: Vec<PathBuf> = Vec::new();
    let mut out: Option<PathBuf> = None;
    let mut dump_unreachable_mismatches = 0usize;
    let mut args = std::env::args().skip(1);
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--corpus" => match args.next() {
                Some(dir) => corpus_roots.push(PathBuf::from(dir)),
                None => return usage("--corpus requires a directory"),
            },
            "--out" => match args.next() {
                Some(file) => out = Some(PathBuf::from(file)),
                None => return usage("--out requires a file path"),
            },
            // W4/unreachable-formula-parity iteration instrument: print the
            // first N (vcgen, spine) formula pairs for Unreachable rows that
            // block NativeGenerated, so the enrichment chain is constructed
            // against OBSERVED bytes rather than guessed.
            "--dump-unreachable-mismatches" => match args.next().map(|n| n.parse()) {
                Some(Ok(n)) => dump_unreachable_mismatches = n,
                _ => return usage("--dump-unreachable-mismatches requires a count"),
            },
            other => return usage(&format!("unknown argument `{other}`")),
        }
    }
    if corpus_roots.is_empty() {
        corpus_roots.push(Path::new(env!("CARGO_MANIFEST_DIR")).join("../trust-clean/fixtures"));
    }

    let mut dirs = Vec::new();
    for root in &corpus_roots {
        dump_dirs(root, &mut dirs);
    }
    if dirs.is_empty() {
        eprintln!(
            "native-gen-scorecard: no dump directories under {:?} — an empty corpus would \
             render a vacuous scorecard, refusing",
            corpus_roots
        );
        return std::process::ExitCode::from(2);
    }

    let mut rows: Vec<FunctionOutcomeRow> = Vec::new();
    let mut losses: Vec<CorpusLoss> = Vec::new();
    let mut files_scanned = 0usize;
    for dir in &dirs {
        let Ok(entries) = std::fs::read_dir(dir) else {
            losses.push(CorpusLoss {
                path: dir.display().to_string(),
                reason: "directory became unreadable between discovery and scan".to_string(),
            });
            continue;
        };
        // Deterministic order for reproducible loss listings.
        let mut paths: BTreeSet<PathBuf> = entries
            .flatten()
            .map(|entry| entry.path())
            .filter(|path| path.extension().and_then(|x| x.to_str()) == Some("json"))
            .collect();
        while let Some(path) = paths.pop_first() {
            files_scanned += 1;
            let text = match std::fs::read_to_string(&path) {
                Ok(text) => text,
                Err(error) => {
                    losses.push(CorpusLoss {
                        path: path.display().to_string(),
                        reason: format!("read: {error}"),
                    });
                    continue;
                }
            };
            let func = match serde_json::from_str::<VerifiableFunction>(&text) {
                Ok(func) => func,
                Err(error) => {
                    losses.push(CorpusLoss {
                        path: path.display().to_string(),
                        reason: format!("parse: {error}"),
                    });
                    continue;
                }
            };
            let hash16 = match func.try_content_hash() {
                Ok(hash) => hash.chars().take(16).collect::<String>(),
                Err(error) => {
                    losses.push(CorpusLoss {
                        path: path.display().to_string(),
                        reason: format!("content-hash: {error}"),
                    });
                    continue;
                }
            };
            let (vcgen, discharged) = vcgen_vcs_for(&func);
            let spine_declined = trust_ir_bridge::generate_native_safety_vcs(&func).is_none();
            // W4/spine-derives-unreachable: the terminator walk takes vcgen's own
            // arm-1b block population as its reachability gate — the same input
            // the production caller threads once the trust_verify hookup lands.
            let terminator_blocks = trust_vcgen::terminator_vc_block_set(&func);
            let (dispatched, outcome) =
                trust_ir_bridge::generate_native_or_flip_safety_vcs_with_reachability(
                    &func,
                    vcgen,
                    discharged.iter(),
                    Some(&terminator_blocks),
                );
            if dump_unreachable_mismatches > 0
                && matches!(outcome, trust_ir_bridge::NativeGenOutcome::FlippedFallback(_))
            {
                let vcgen_unreach: Vec<_> = dispatched
                    .iter()
                    .filter(|vc| matches!(vc.kind, trust_types::VcKind::Unreachable))
                    .collect();
                if !vcgen_unreach.is_empty() {
                    if let Some(native) =
                        trust_ir_bridge::generate_native_safety_vcs_with_reachability(
                            &func,
                            Some(&terminator_blocks),
                        )
                    {
                        let native_unreach: Vec<_> = native
                            .iter()
                            .filter(|vc| matches!(vc.kind, trust_types::VcKind::Unreachable))
                            .collect();
                        eprintln!("== {} ==", func.def_path);
                        for vc in &vcgen_unreach {
                            eprintln!("  vcgen @{:?}: {:?}", vc.location.line_start, vc.formula);
                        }
                        for vc in &native_unreach {
                            eprintln!("  spine @{:?}: {:?}", vc.location.line_start, vc.formula);
                        }
                        dump_unreachable_mismatches -= 1;
                    }
                }
            }
            rows.push(classify_function(
                func.def_path.clone(),
                hash16,
                spine_declined,
                &dispatched,
                &outcome,
            ));
        }
    }

    let card = NativeGenScorecard::measure(&rows, losses, files_scanned);
    let json = card.to_json();
    let rendered = serde_json::to_string_pretty(&json).expect("scorecard JSON renders");
    match &out {
        Some(path) => {
            if let Some(parent) = path.parent() {
                if let Err(error) = std::fs::create_dir_all(parent) {
                    eprintln!("native-gen-scorecard: create {}: {error}", parent.display());
                    return std::process::ExitCode::from(2);
                }
            }
            if let Err(error) = std::fs::write(path, rendered + "\n") {
                eprintln!("native-gen-scorecard: write {}: {error}", path.display());
                return std::process::ExitCode::from(2);
            }
            eprintln!("wrote {}", path.display());
        }
        None => println!("{rendered}"),
    }

    eprintln!(
        "corpus: {} files, {} functions, {} losses | outcomes: native={} fallback={} \
         disagreed={} spine_declined={} | classes eligible: {}",
        json["corpus"]["files_scanned"],
        json["corpus"]["functions"],
        json["corpus"]["losses"].as_array().map_or(0, Vec::len),
        json["outcomes"]["native_generated"],
        json["outcomes"]["flipped_fallback"],
        json["outcomes"]["disagreed"],
        json["outcomes"]["spine_declined"],
        json["eligible_classes"],
    );
    std::process::ExitCode::SUCCESS
}

fn usage(problem: &str) -> std::process::ExitCode {
    eprintln!(
        "native-gen-scorecard: {problem}\n\
         usage: --corpus DIR (repeatable; default ../trust-clean/fixtures) --out FILE"
    );
    std::process::ExitCode::from(2)
}
