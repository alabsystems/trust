use super::*;
use super::super::spool::PublicationSpool;
use super::super::super::{
    PreparedDiagnostic, PreparedDiagnosticChild, PreparedHumanReport,
    PreparedLocatedDiagnostic, PreparedLocatedNote,
};
use rustc_span::{BytePos, Span};
use serde::Serialize;
use serde::ser::SerializeSeq;
use std::path::PathBuf;
use std::sync::atomic::{AtomicU64, Ordering};

static NEXT_SCRATCH: AtomicU64 = AtomicU64::new(0);

struct Scratch(PathBuf);

impl Scratch {
    fn new() -> Self {
        let sequence = NEXT_SCRATCH.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!(
            "trust-publication-output-test-{}-{sequence}", std::process::id(),
        ));
        let mut create = std::fs::DirBuilder::new();
        #[cfg(unix)]
        {
            use std::os::unix::fs::DirBuilderExt;
            create.mode(0o700);
        }
        create.create(&path).unwrap();
        Self(std::fs::canonicalize(path).unwrap())
    }
}

impl Drop for Scratch {
    fn drop(&mut self) { let _ = std::fs::remove_dir_all(&self.0); }
}

fn site(start: u32) -> Span {
    Span::with_root_ctxt(BytePos(start), BytePos(start + 1))
}

fn diagnostic(aborting: bool, header: &str, start: u32) -> PreparedAction {
    PreparedAction::Diagnostic(PreparedLocatedDiagnostic {
        span: site(start),
        diagnostic: PreparedDiagnostic {
            aborting,
            header: header.into(),
            children: vec![
                PreparedDiagnosticChild::Note("before help".into()),
                PreparedDiagnosticChild::Help("help stays between notes".into()),
                PreparedDiagnosticChild::SpanNote(site(start + 2), "actual child site".into()),
                PreparedDiagnosticChild::Note("after help".into()),
            ],
        },
    })
}

fn note(summary: &str, start: u32) -> PreparedAction {
    PreparedAction::Note(PreparedLocatedNote {
        span: site(start),
        report: PreparedHumanReport {
            summary: summary.into(),
            notes: vec!["first note child".into(), "last note child".into()],
        },
    })
}

fn original() -> Vec<PreparedAction> {
    vec![
        PreparedAction::Stderr("first line\n\0unicode: λ".into()),
        diagnostic(true, "original error", 10),
        note("primary NOTE before warning", 20),
        PreparedAction::Stderr("between NOTE and warning\n".into()),
        diagnostic(false, "original warning", 30),
        note("last primary NOTE", 40),
        PreparedAction::Stderr("final stderr, no added newline".into()),
    ]
}

fn assert_diagnostic(action: &PreparedAction, aborting: bool, header: &str, start: u32) {
    let PreparedAction::Diagnostic(value) = action else { panic!("diagnostic variant lost"); };
    assert_eq!(value.span, site(start));
    assert_eq!(value.diagnostic.aborting, aborting);
    assert_eq!(value.diagnostic.header, header);
    assert!(matches!(&value.diagnostic.children[..], [
        PreparedDiagnosticChild::Note(before), PreparedDiagnosticChild::Help(help),
        PreparedDiagnosticChild::SpanNote(actual, at), PreparedDiagnosticChild::Note(after),
    ] if before == "before help" && help == "help stays between notes"
        && *actual == site(start + 2) && at == "actual child site" && after == "after help"));
}

fn assert_note(action: &PreparedAction, summary: &str, start: u32) {
    let PreparedAction::Note(value) = action else { panic!("primary NOTE became a diagnostic"); };
    assert_eq!(value.span, site(start));
    assert_eq!(value.report.summary, summary);
    assert_eq!(value.report.notes.len(), 2);
    assert_eq!(value.report.notes[0], "first note child");
    assert_eq!(value.report.notes[1], "last note child");
}

fn assert_original(actions: &[PreparedAction]) {
    assert_eq!(actions.len(), 7, "no prefix-only return or dropped action");
    assert!(matches!(&actions[0], PreparedAction::Stderr(s) if s == "first line\n\0unicode: λ"));
    assert_diagnostic(&actions[1], true, "original error", 10);
    assert_note(&actions[2], "primary NOTE before warning", 20);
    assert!(matches!(&actions[3], PreparedAction::Stderr(s) if s == "between NOTE and warning\n"));
    assert_diagnostic(&actions[4], false, "original warning", 30);
    assert_note(&actions[5], "last primary NOTE", 40);
    assert!(matches!(&actions[6], PreparedAction::Stderr(s) if s == "final stderr, no added newline"));
}

fn json(actual: &mut LiveSpans, original: &[PreparedAction]) -> serde_json::Value {
    serde_json::to_value(capture(actual, original).unwrap()).unwrap()
}

#[test]
fn borrowed_mixed_actions_spool_as_owned_after_original_text_is_released() {
    let root = Scratch::new();
    let spool = PublicationSpool::create(&root.0).unwrap();
    let mut actual = LiveSpans::new().unwrap();
    let mut saved = {
        let original = original();
        let borrowed = capture(&mut actual, &original).unwrap();
        // The row denominator belongs to the actual parent; action count
        // is not a verification-row count or a source of debt authority.
        spool.save_as::<_, PreparedEmission>("actual body identity", 3, &borrowed).unwrap()
    };
    let owned = saved.consume("actual body identity", 3).unwrap();
    let restored = owned.restore(&actual).unwrap();
    assert_original(&restored);
    assert!(saved.consume("actual body identity", 3).is_err(), "one record attempt");
}

#[test]
fn late_invalid_span_or_wrong_live_table_refuses_the_entire_action_sequence() {
    let original = original();
    let mut actual = LiveSpans::new().unwrap();
    let valid = json(&mut actual, &original);
    let another = LiveSpans::new().unwrap();
    let owned: PreparedEmission = serde_json::from_value(valid.clone()).unwrap();
    assert!(owned.restore(&another).is_err());
    let mut wrong_table = valid.clone();
    wrong_table["actions"][5]["Note"]["table"] = serde_json::json!(u64::MAX);
    let owned: PreparedEmission = serde_json::from_value(wrong_table).unwrap();
    assert!(owned.restore(&actual).is_err(), "a late unknown table cannot release a prefix");
    for (action, child) in [(5, false), (4, true)] {
        let mut mutant = valid.clone();
        if child {
            mutant["actions"][action]["Diagnostic"]["diagnostic"]["children"][2]["SpanNote"][0]
                = serde_json::json!(usize::MAX);
        } else {
            mutant["actions"][action]["Note"]["span"] = serde_json::json!(usize::MAX);
        }
        let owned: PreparedEmission = serde_json::from_value(mutant).unwrap();
        assert!(owned.restore(&actual).is_err(), "no valid prefix can escape a late refusal");
    }
    assert_original(&original);
    let owned: PreparedEmission = serde_json::from_value(valid).unwrap();
    assert_original(&owned.restore(&actual).unwrap());
}

#[test]
fn serde_rejects_unknown_actions_malformed_slots_and_missing_or_extra_fields() {
    let original = original();
    let mut actual = LiveSpans::new().unwrap();
    let valid = json(&mut actual, &original);
    let mut unknown = valid.clone();
    unknown["actions"][6] = serde_json::json!({"Proof": "not an action or authority"});
    assert!(serde_json::from_value::<PreparedEmission>(unknown).is_err());
    let mut malformed = valid.clone();
    malformed["actions"][5]["Note"]["span"] = serde_json::json!(-1);
    assert!(serde_json::from_value::<PreparedEmission>(malformed).is_err());
    let mut wrong_kind = valid.clone();
    wrong_kind["actions"][1]["Diagnostic"]["table"] = serde_json::json!("not a table id");
    assert!(serde_json::from_value::<PreparedEmission>(wrong_kind).is_err());
    let mut missing = valid.clone();
    missing.as_object_mut().unwrap().remove("actions");
    assert!(serde_json::from_value::<PreparedEmission>(missing).is_err());
    let mut extra = valid;
    extra["selected_success"] = serde_json::json!(true);
    assert!(serde_json::from_value::<PreparedEmission>(extra).is_err());
    assert_original(&original);
}

#[test]
fn spool_decode_or_body_refusal_cannot_be_retried_as_a_favorable_output() {
    let root = Scratch::new();
    let spool = PublicationSpool::create(&root.0).unwrap();
    let original = original();
    let mut actual = LiveSpans::new().unwrap();
    let borrowed = capture(&mut actual, &original).unwrap();
    let mut wrong_body = spool.save_as::<_, PreparedEmission>("original body", 3, &borrowed).unwrap();
    assert!(wrong_body.consume("other body", 3).is_err());
    assert!(wrong_body.consume("original body", 3).is_err());
    let mut wrong_shape = spool.save_as::<str, PreparedEmission>("original body", 3, "not actions").unwrap();
    assert!(wrong_shape.consume("original body", 3).is_err());
    assert!(wrong_shape.consume("original body", 3).is_err());
    assert_original(&original);
}

struct InterruptedAlternative;

impl Serialize for InterruptedAlternative {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let mut sequence = serializer.serialize_seq(Some(2))?;
        sequence.serialize_element("actual partial second-alternative bytes")?;
        Err(serde::ser::Error::custom("injected output alternative failure"))
    }
}

#[test]
fn partial_second_alternative_returns_no_pair_and_preserves_original_fallback() {
    let root = Scratch::new();
    let spool = PublicationSpool::create(&root.0).unwrap();
    let original = original();
    let mut actual = LiveSpans::new().unwrap();
    let borrowed = capture(&mut actual, &original).unwrap();
    let mut prior = spool.save_as::<_, PreparedEmission>("prior body", 3, &borrowed).unwrap();
    assert!(spool.save_pair_as::<_, PreparedEmission, _, PreparedEmission>(
        "current body", 3, &borrowed, &InterruptedAlternative,
    ).is_err(), "no first or second handle escapes a partial second append");
    assert!(spool.save_as::<_, PreparedEmission>("retry body", 3, &borrowed).is_err());
    assert_original(&original);
    assert_original(&prior.consume("prior body", 3).unwrap().restore(&actual).unwrap());
}
