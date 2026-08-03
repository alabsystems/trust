//! The pure-Lean front door, and the Clean proof corpora it is measured on.
//!
//! `targo trust check <file.lean>` kernel-checks a standalone Clean/Lean file
//! through `trust_certify::clean_island` — the same parser, elaborator, and CIC
//! kernel the `clean { … }` island lane uses, linked into the toolchain rather
//! than reached through a subprocess. This gate holds that lane to Trust's own
//! machine-checked corpora:
//!
//! - `proofs/trust-soundness` — that Trust's discharge encoding is sound
//!   (`realPanics ⊆ models`), plus the per-class soundness arms.
//! - `proofs/codegen-equivalence` — that the value semantics of the machine
//!   instructions trust-cg emits equal the IR semantics they implement.
//!
//! This is the AUTHORITATIVE lane for both corpora, and nothing in it is
//! conditional: the kernel is a dependency of this test binary, so the gate
//! cannot degrade into a skip, and its verdict cannot change with whichever
//! `clean` executable happens to be installed. The sibling gates that shell out
//! to a discovered `clean` binary are reproducibility evidence about that
//! binary, not about the proofs.

use std::path::{Path, PathBuf};

use trust_certify::clean_island::check_clean_island;

fn corpus_dir(name: &str) -> PathBuf {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..").join("proofs").join(name);
    dir.canonicalize().unwrap_or_else(|e| panic!("proof corpus {dir:?} not found: {e}"))
}

fn corpus_files(dir: &Path) -> Vec<PathBuf> {
    let mut files = Vec::new();
    for entry in std::fs::read_dir(dir).expect("read proof corpus directory") {
        let path = entry.expect("dir entry").path();
        if path.extension().and_then(|e| e.to_str()) == Some("lean") {
            files.push(path);
        }
    }
    files.sort();
    files
}

/// Kernel-check every `.lean` file in `dir`, requiring at least `min_files` of
/// them so a deleted or clobbered corpus fails instead of vacuously passing.
///
/// `min_files` is deliberately BELOW the corpus size. A floor equal to the
/// current count only catches a total wipe and has to be edited every time a
/// proof lands; a floor with headroom catches deletion while leaving growth
/// free, and every file that IS present is checked regardless of the floor.
fn check_corpus(name: &str, min_files: usize) {
    let dir = corpus_dir(name);
    let files = corpus_files(&dir);
    assert!(
        files.len() >= min_files,
        "expected the {name} proof corpus (>= {min_files} files), found {} in {}",
        files.len(),
        dir.display()
    );

    let mut failures = Vec::new();
    let mut registered = 0usize;
    for path in &files {
        let source = std::fs::read_to_string(path)
            .unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
        let outcome = check_clean_island(&source);
        if outcome.is_rejected() {
            let messages = outcome
                .errors
                .iter()
                .map(|err| format!("    {}", err.message))
                .collect::<Vec<_>>()
                .join("\n");
            failures.push(format!(
                "{} no longer kernel-checks in process\n{messages}",
                path.display()
            ));
        }
        registered += outcome.registered.len();
    }

    assert!(
        failures.is_empty(),
        "PROOF CORPUS BROKEN: {} of {} {name} proofs failed the in-process Clean kernel:\n{}",
        failures.len(),
        files.len(),
        failures.join("\n\n")
    );

    eprintln!(
        "{name} GREEN: {} files, {registered} declarations kernel-checked in process",
        files.len()
    );
}

#[test]
fn lean_front_door_checks_the_trust_soundness_corpus() {
    check_corpus("trust-soundness", 30);
}

#[test]
fn lean_front_door_checks_the_codegen_equivalence_corpus() {
    check_corpus("codegen-equivalence", 2);
}

/// A rejected file must be reported as rejected. The front door is only worth
/// having if it fails closed, so pin the negative direction on inputs whose
/// failure modes are structurally different: a parse error, a false theorem the
/// kernel refuses, and two assumptions the strict policy refuses even though
/// the kernel itself would accept them.
#[test]
fn lean_front_door_fails_closed() {
    for source in [
        "def : := :=\n",
        "theorem false_claim : 0 = 1 := rfl\n",
        "axiom assumed : True\n",
        "theorem hole : True := sorry\n",
    ] {
        let outcome = check_clean_island(source);
        assert!(outcome.is_rejected(), "front door accepted `{source}`");
    }
}

/// Projection-certificate-specific non-vacuity control. Dropping the checked
/// conclusion would let an accepted certificate claim that `true -> false` is
/// satisfied. Keep the red proof as a named fixture so edits to the green
/// semantic theorem cannot silently weaken or delete the load-bearing check.
#[test]
fn quantified_projection_red_control_is_rejected() {
    let green_path = corpus_dir("trust-soundness").join("quantified_projection_certificate.lean");
    let green = std::fs::read_to_string(&green_path)
        .unwrap_or_else(|e| panic!("read projection proof {}: {e}", green_path.display()));
    let negative_dir = corpus_dir("trust-soundness-negative");
    let controls = [
        ("quantified_projection_accept_without_conclusion.lean", 1usize),
        ("quantified_projection_source_binding_bypass.lean", 14),
        ("quantified_projection_query_identity_bypass.lean", 16),
        ("quantified_projection_query_feature_bypass.lean", 4),
        ("quantified_projection_dispatch_bypass.lean", 3),
        ("quantified_projection_missing_semantic_evidence.lean", 3),
        ("quantified_projection_literal_true_substitution.lean", 1),
        ("quantified_projection_map_shape_bypass.lean", 2),
    ];

    for (file, expected_failures) in controls {
        let red_path = negative_dir.join(file);
        let fragment = std::fs::read_to_string(&red_path)
            .unwrap_or_else(|e| panic!("read projection red control {}: {e}", red_path.display()));
        let fragment_offset = green.len() + 1;
        let mut source = green.clone();
        source.push('\n');
        source.push_str(&fragment);

        let mut declarations = Vec::new();
        let mut offset = 0usize;
        for line in fragment.split_inclusive('\n') {
            if let Some(rest) = line.strip_prefix("def ") {
                let name = rest
                    .split(|ch: char| ch.is_whitespace() || ch == ':')
                    .next()
                    .expect("red declaration has a name");
                declarations.push((name.to_owned(), fragment_offset + offset));
            }
            offset += line.len();
        }
        assert_eq!(
            declarations.len(),
            expected_failures,
            "projection red declaration inventory changed: {}",
            red_path.display()
        );

        let outcome = check_clean_island(&source);
        assert!(
            outcome.is_rejected(),
            "projection checker red control unexpectedly kernel-checked: {}",
            red_path.display()
        );
        assert_eq!(
            outcome.errors.len(),
            expected_failures,
            "projection checker red control did not produce its exact rejection count ({}): {:?}",
            red_path.display(),
            outcome.errors
        );
        assert!(
            outcome.errors.iter().all(|error| !error.message.contains("UnknownIdent")
                && !error.message.contains("unknown identifier")),
            "projection checker red control was vacuously rejected by an unknown name ({}): {:?}",
            red_path.display(),
            outcome.errors
        );

        for (index, (name, start)) in declarations.iter().enumerate() {
            let end =
                declarations.get(index + 1).map_or(source.len(), |(_, next_start)| *next_start);
            assert!(
                !outcome.registered.iter().any(|registered| registered == name),
                "projection bypass declaration unexpectedly registered: {name} ({})",
                red_path.display()
            );
            assert!(
                outcome.errors.iter().any(|error| error.start < end && error.end >= *start),
                "projection bypass declaration lacked its own rejection: {name} ({})",
                red_path.display()
            );
        }
    }
}
