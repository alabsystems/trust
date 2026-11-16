use super::*;
use rustc_span::{BytePos, Span};

fn original() -> PreparedLocatedDiagnostic {
    PreparedLocatedDiagnostic {
        span: Span::with_root_ctxt(BytePos(1), BytePos(2)),
        diagnostic: PreparedDiagnostic {
            aborting: true,
            header: "original header".into(),
            children: vec![
                PreparedDiagnosticChild::Note("before".into()),
                PreparedDiagnosticChild::Help("help between notes".into()),
                PreparedDiagnosticChild::SpanNote(
                    Span::with_root_ctxt(BytePos(3), BytePos(4)), "actual source site".into(),
                ),
                PreparedDiagnosticChild::Note("after".into()),
            ],
        },
    }
}

#[test]
fn borrowed_text_roundtrip_preserves_order_and_actual_live_spans() {
    let original = original();
    let mut actual = LiveSpans::new().unwrap();
    let borrowed = actual.capture(&original).unwrap();
    let bytes = serde_json::to_vec(&borrowed).unwrap();
    let owned: IndexedDiagnostic = serde_json::from_slice(&bytes).unwrap();
    let restored = owned.restore(&actual).unwrap();
    assert_eq!(restored.span, original.span);
    assert_eq!(restored.diagnostic.header, original.diagnostic.header);
    assert!(restored.diagnostic.aborting);
    assert!(matches!(&restored.diagnostic.children[..], [
        PreparedDiagnosticChild::Note(before), PreparedDiagnosticChild::Help(help),
        PreparedDiagnosticChild::SpanNote(site, note), PreparedDiagnosticChild::Note(after),
    ] if before == "before" && help == "help between notes" && note == "actual source site"
        && after == "after" && *site == Span::with_root_ctxt(BytePos(3), BytePos(4))));
    assert_eq!(actual.values.len(), 2);
}

#[test]
fn stored_data_cannot_supply_another_table_or_out_of_bounds_span() {
    let original = original();
    let mut actual = LiveSpans::new().unwrap();
    let bytes = serde_json::to_vec(&actual.capture(&original).unwrap()).unwrap();
    let another = LiveSpans::new().unwrap();
    let owned: IndexedDiagnostic = serde_json::from_slice(&bytes).unwrap();
    assert!(owned.restore(&another).is_err());
    let mut owned: IndexedDiagnostic = serde_json::from_slice(&bytes).unwrap();
    owned.span = usize::MAX;
    assert!(owned.restore(&actual).is_err());
    let mut owned: IndexedDiagnostic = serde_json::from_slice(&bytes).unwrap();
    owned.diagnostic.children.push(PreparedDiagnosticChild::SpanNote(usize::MAX, "mutant".into()));
    assert!(owned.restore(&actual).is_err());
    // These are decoder refusal controls only. Production also verifies
    // the original-write spool commitment before deserializing this DATA.
}

#[test]
fn standalone_transport_span_keeps_actual_table_and_slot_provenance() {
    let span = Span::with_root_ctxt(BytePos(31), BytePos(37));
    let mut actual = LiveSpans::new().unwrap();
    let saved = actual.capture_span(span).unwrap();
    let bytes = serde_json::to_vec(&saved).unwrap();
    let mut saved: IndexedSpan = serde_json::from_slice(&bytes).unwrap();
    assert_eq!(actual.restore_span(&saved).unwrap(), span);
    assert!(LiveSpans::new().unwrap().restore_span(&saved).is_err());
    saved.span = usize::MAX;
    assert!(actual.restore_span(&saved).is_err());
    // The enclosing original-write/body/role frame still authenticates
    // these DATA bytes before any slot is restored in production.
}

#[test]
fn primary_note_roundtrip_keeps_note_data_and_its_live_span() {
    let original = PreparedLocatedNote {
        span: Span::with_root_ctxt(BytePos(5), BytePos(7)),
        report: PreparedHumanReport {
            summary: "original NOTE, never an advisory or error".into(),
            notes: vec!["original ordered child".into()],
        },
    };
    let mut actual = LiveSpans::new().unwrap();
    let bytes = serde_json::to_vec(&actual.capture_note(&original).unwrap()).unwrap();
    let restored: IndexedNote = serde_json::from_slice(&bytes).unwrap();
    let restored = restored.restore(&actual).unwrap();
    assert_eq!(restored.span, original.span);
    assert_eq!(restored.report.summary, original.report.summary);
    assert_eq!(restored.report.notes, original.report.notes);
    let restored: IndexedNote = serde_json::from_slice(&bytes).unwrap();
    assert!(restored.restore(&LiveSpans::new().unwrap()).is_err());
}
