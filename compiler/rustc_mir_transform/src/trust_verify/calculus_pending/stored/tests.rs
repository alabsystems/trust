//! Original publication storage controls only. No constructor here produces
//! native/source eligibility, a mathematical token, grade or selected outcome.

use super::*;
use std::path::PathBuf;
use std::sync::atomic::{AtomicU64, Ordering};

struct Scratch(PathBuf);

impl Scratch {
    fn new() -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let path = std::env::temp_dir().join(format!(
            "trust-vf5-original-record-{}-{}", std::process::id(), NEXT.fetch_add(1, Ordering::Relaxed),
        ));
        let mut create = std::fs::DirBuilder::new();
        #[cfg(unix)]
        { use std::os::unix::fs::DirBuilderExt; create.mode(0o700); }
        create.create(&path).unwrap();
        Self(std::fs::canonicalize(path).unwrap())
    }
}

impl Drop for Scratch {
    fn drop(&mut self) { let _ = std::fs::remove_dir_all(&self.0); }
}

fn inventory(description: &str) -> OwedInventory {
    let row: TransportObligationResult = serde_json::from_value(serde_json::json!({
        "obligation_id": "original-record-data:0", "kind": "divzero",
        "description": description, "outcome": "unknown", "solver": "unit-DATA", "time_ms": 0,
    })).unwrap();
    OwedInventory::capture(&[row.clone()], PublishedRowTally::of(&[row], None), || true).unwrap()
}

fn original() -> PreparedCollection {
    PreparedCollection {
        actions: vec![
            PreparedAction::Stderr("first original action".into()),
            PreparedAction::Note(PreparedLocatedNote {
                span: rustc_span::DUMMY_SP,
                report: PreparedHumanReport { summary: "original NOTE".into(), notes: vec!["note child".into()] },
            }),
            PreparedAction::Diagnostic(PreparedLocatedDiagnostic {
                span: rustc_span::DUMMY_SP,
                diagnostic: PreparedDiagnostic {
                    aborting: true, header: "original refusal".into(),
                    children: vec![PreparedDiagnosticChild::Help("help first".into()),
                        PreparedDiagnosticChild::Note("note after help".into())],
                },
            }),
        ],
        transport: None, human: None, owed: Some(inventory("complete original row remains unproved")),
    }
}

#[test]
fn original_roundtrip_retains_complete_debt_and_ordered_note_error_data() {
    let scratch = Scratch::new();
    let storage = spool::PublicationSpool::create(&scratch.0).unwrap();
    let collection = original();
    let digest = collection.owed.as_ref().unwrap().digest();
    let saved = match save_original(&storage, "actual-body", collection) {
        Ok(saved) => saved, Err((error, _)) => panic!("save original DATA: {error}"),
    };
    let restored = match saved.restore("actual-body") {
        Ok(restored) => restored, Err((error, _)) => panic!("restore original DATA: {error}"),
    };
    assert_eq!(restored.owed.as_ref().unwrap().digest(), digest);
    assert_eq!(restored.owed.as_ref().unwrap().outcome(0), Some(Outcome::Unknown));
    assert!(matches!(&restored.actions[0], PreparedAction::Stderr(text) if text == "first original action"));
    assert!(matches!(&restored.actions[1], PreparedAction::Note(note)
        if note.span == rustc_span::DUMMY_SP && note.report.summary == "original NOTE"));
    let PreparedAction::Diagnostic(error) = &restored.actions[2] else { panic!("original error disappeared") };
    assert!(error.diagnostic.aborting);
    assert!(matches!(&error.diagnostic.children[0], PreparedDiagnosticChild::Help(text) if text == "help first"));
    assert!(matches!(&error.diagnostic.children[1], PreparedDiagnosticChild::Note(text) if text == "note after help"));
    assert!(restored.transport.is_none());
}

#[test]
fn wrong_body_or_live_row_commitment_refuses_with_full_original_inventory() {
    let scratch = Scratch::new();
    let storage = spool::PublicationSpool::create(&scratch.0).unwrap();
    for wrong_body in [true, false] {
        let mut saved = match save_original(&storage, "actual-body", original()) {
            Ok(saved) => saved, Err((error, _)) => panic!("save original DATA: {error}"),
        };
        if !wrong_body {
            // Same public count/id/outcome, different complete row commitment.
            saved.owed = inventory("different original row, same count and label");
        }
        let owed = saved.owed.digest();
        match saved.restore(if wrong_body { "another-body" } else { "actual-body" }) {
            Ok(_) => panic!("mismatched body/row DATA restored"),
            Err((_, remaining)) => {
                assert_eq!(remaining.total(), 1);
                assert_eq!(remaining.digest(), owed);
                assert_eq!(remaining.outcome(0), Some(Outcome::Unknown));
            }
        }
    }
}

#[test]
fn proposed_role_cannot_decode_as_original_even_with_valid_accepted_write_hash() {
    let scratch = Scratch::new();
    let storage = spool::PublicationSpool::create(&scratch.0).unwrap();
    let collection = original();
    let mut spans = LiveSpans::new().unwrap();
    let owed = collection.owed.as_ref().unwrap();
    let actions = publication_output::capture(&mut spans, &collection.actions).unwrap();
    let mut wrong_role = serde_json::to_value(OriginalRef {
        role: OriginalRole::Original, owed, actions, transport: None,
    }).unwrap();
    wrong_role["role"] = serde_json::json!("proposed-publication-delta-v1");
    // The storage really seals these emitted bytes. Digest equality cannot
    // substitute the proposed role for a complete original publication.
    let mut saved = storage.save_as::<_, OriginalRecord>("actual-body", owed.total(), &wrong_role).unwrap();
    assert!(saved.consume("actual-body", owed.total()).is_err());
    assert!(saved.consume("actual-body", owed.total()).is_err(), "no retry after refused decode");
}
