//! AUTHORED / UNEXECUTED pure reporting DATA controls. These contain no
//! proof/certificate, live source-map span, compiler-produced result or
//! favorable placeholder evidence and establish no compiler qualification.
use super::*;
use trust_types::obligation_identity::{AnchorInput, KeyedRow, LineIndex, local_ids, row_anchor,
    row_discriminator, span_position};

const SOURCE: &str = "fn first() { let x = 1; }\nfn second() { let y = 2; }\n";

fn span(line: u32) -> trust_types::SourceSpan {
    trust_types::SourceSpan { file: "data.rs".into(), line_start: line,
        col_start: 1, line_end: line, col_end: 1 }
}

fn row(description: &str, location: Option<trust_types::SourceSpan>) -> TransportObligationResult {
    serde_json::from_value(serde_json::json!({
        "kind": "assert", "description": description, "location": location,
        "outcome": "unknown", "solver": "reporting-DATA-no-proof", "time_ms": 0,
    })).expect("authority-free row DATA")
}

fn anchors(rows: &[TransportObligationResult], fallback: Option<&trust_types::SourceSpan>) -> Vec<LocatedAnchor> {
    let lines = LineIndex::new(SOURCE);
    let mut seen = FxHashSet::default();
    rows.iter().filter_map(|row| row.location.as_ref()).chain(fallback)
        .filter(|location| !location.file.is_empty() && seen.insert((*location).clone()))
        .map(|location| LocatedAnchor {
            location: location.clone(),
            anchor: row_anchor(AnchorInput::of(Some(location), "",
                (location.file == "data.rs").then_some((SOURCE, &lines)))).anchor,
        }).collect()
}

fn source_ids(rows: &[TransportObligationResult]) -> Vec<String> {
    let lines = LineIndex::new(SOURCE);
    let anchors = rows.iter().map(|row| row_anchor(AnchorInput::of(
        row.location.as_ref(), &row.description,
        row.location.as_ref().filter(|location| location.file == "data.rs")
            .map(|_| (SOURCE, &lines)),
    )).anchor).collect::<Vec<_>>();
    let discriminators = rows.iter().map(|row| row_discriminator(&row.description)).collect::<Vec<_>>();
    let keyed = rows.iter().zip(&anchors).zip(&discriminators)
        .map(|((row, anchor), discriminator)| KeyedRow {
            kind: &row.kind, anchor, position: span_position(row.location.as_ref()), discriminator,
        }).collect::<Vec<_>>();
    local_ids(&keyed).expect("maintained source-based identity DATA")
}

fn data(rows: Vec<TransportObligationResult>, fallback_location: Option<trust_types::SourceSpan>, budget: u64) -> PreparedTransportData {
    let anchors = anchors(&rows, fallback_location.as_ref());
    let counts = PublishedRowTally::of(&rows, None).json_counts();
    let mut result: FunctionTransportResult = serde_json::from_value(serde_json::json!({
        "function": "reporting_data::subject", "results": [], "proved": 0,
        "failed": 0, "unknown": 0, "runtime_checked": 0, "total": 0,
    })).expect("authority-free envelope DATA");
    result.stable_ids = source_ids(&rows);
    result.results = rows;
    result.proved = counts.proved;
    result.failed = counts.failed;
    result.unknown = counts.unknown;
    result.timed_out = counts.timed_out;
    result.skipped = counts.skipped;
    result.runtime_checked = counts.runtime_checked;
    result.total = counts.total;
    PreparedTransportData {
        function_result: result, framing: CapturedFraming::RawStderr, budget,
        fallback_location, anchors,
        minted_counts: [counts.proved, counts.failed, counts.unknown, counts.timed_out,
            counts.skipped, counts.runtime_checked, counts.total],
        row_diagnostics_enabled: false,
    }
}

#[test]
fn frozen_located_and_description_anchors_match_maintained_source_ids() {
    let external = trust_types::SourceSpan { file: "/registry/external.rs".into(), ..span(1) };
    let empty = trust_types::SourceSpan { file: String::new(), ..span(2) };
    let mut rows = vec![row("first row", Some(span(1))), row("second row", Some(span(1))),
        row("external", Some(external)), row("unlocated", None), row("empty file", Some(empty))];
    let captured = anchors(&rows, None);
    let index = AnchorIndex::new(&captured).unwrap();
    assert_eq!(index.ids(&rows).unwrap(), source_ids(&rows));
    // A budget rewrite may change outcomes; a future separately-authorized
    // pure amendment may change descriptions, not the captured source.
    rows[0].outcome = Outcome::Failed;
    for row in &mut rows { row.description.push_str(" changed DATA"); }
    assert_eq!(index.ids(&rows).unwrap(), source_ids(&rows));
}

#[test]
fn unknown_and_conflicting_located_anchors_refuse_instead_of_guessing() {
    let rows = vec![row("original", Some(span(1)))];
    let mut captured = anchors(&rows, None);
    assert!(AnchorIndex::new(&captured).unwrap().ids(&[row("new location", Some(span(2)))]).is_err());
    captured.push(LocatedAnchor { location: span(1), anchor: "conflicting-DATA".into() });
    assert!(AnchorIndex::new(&captured).is_err());
}

#[test]
fn final_fallback_uses_exact_captured_or_description_anchor_and_counts() {
    for fallback in [Some(span(2)), None, Some(trust_types::SourceSpan { file: String::new(), ..span(2) })] {
        let mut rows = (0..40).map(|i| row(&format!("row{i}:{}", "x".repeat(2048)), Some(span(1))))
            .collect::<Vec<_>>();
        rows[3].outcome = Outcome::Failed;
        let prepared = data(rows, fallback, trust_types::transport_budget::MIN_TRANSPORT_LINE_BUDGET_BYTES);
        let fitted = prepared.fit();
        assert!(fitted.identity_defect.is_none());
        assert!(fitted.fitted.is_ok());
        assert_eq!(fitted.function_result.results.len(), 1);
        assert_eq!(fitted.function_result.transport_budget.as_ref().unwrap().step, TransportBudgetStep::ReportReplaced);
        assert_eq!(fitted.function_result.results[0].outcome, Outcome::Failed);
        assert_eq!(fitted.counts, TransportRowCounts { proved: 0, failed: 1, unknown: 0,
            timed_out: 0, skipped: 0, runtime_checked: 0, total: 1 });
        assert_eq!(fitted.function_result.stable_ids, source_ids(&fitted.function_result.results));
    }
}

#[test]
fn prepared_framing_roundtrip_and_unrewritten_payload_are_exact() {
    for framing in [TransportLineFraming::RawStderr,
        TransportLineFraming::json_diagnostic("/DATA/quote\"/雪/back\\slash.rs")]
    {
        let captured = CapturedFraming::capture(framing);
        let decoded: CapturedFraming = serde_json::from_slice(&serde_json::to_vec(&captured).unwrap()).unwrap();
        assert_eq!(decoded.framing(), framing);
        assert_eq!(decoded.framing().line_bytes("{\"text\":\"escaped\\n\"}"), framing.line_bytes("{\"text\":\"escaped\\n\"}"));
    }
    let prepared = data(vec![row("ordinary unproved DATA", Some(span(1)))], Some(span(2)),
        trust_types::transport_budget::TRANSPORT_LINE_BUDGET_BYTES);
    let expected = trust_types::transport_budget::function_result_payload(prepared.result()).unwrap();
    let decoded: PreparedTransportData = serde_json::from_slice(&serde_json::to_vec(&prepared).unwrap()).unwrap();
    let fitted = decoded.fit();
    assert!(fitted.identity_defect.is_none());
    assert_eq!(fitted.fitted.unwrap().payload, expected);
    assert_eq!(fitted.counts.unknown, 1);
    assert_eq!(fitted.counts.total, 1);
}
