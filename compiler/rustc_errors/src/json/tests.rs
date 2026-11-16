use std::str;

use rustc_span::BytePos;
use rustc_span::source_map::FilePathMapping;
use serde::Deserialize;

use super::*;
use crate::DiagCtxt;

#[derive(Deserialize, Debug, PartialEq, Eq)]
struct TestData {
    spans: Vec<SpanTestData>,
}

#[derive(Deserialize, Debug, PartialEq, Eq)]
struct SpanTestData {
    pub byte_start: u32,
    pub byte_end: u32,
    pub line_start: u32,
    pub column_start: u32,
    pub line_end: u32,
    pub column_end: u32,
}

struct Shared<T> {
    data: Arc<Mutex<T>>,
}

impl<T: Write> Write for Shared<T> {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        self.data.lock().unwrap().write(buf)
    }

    fn flush(&mut self) -> io::Result<()> {
        self.data.lock().unwrap().flush()
    }
}

fn filename(sm: &SourceMap, path: &str) -> FileName {
    FileName::Real(sm.path_mapping().to_real_filename(sm.working_dir(), PathBuf::from(path)))
}

/// Test the span yields correct positions in JSON.
fn test_positions(code: &str, span: (u32, u32), expected_output: SpanTestData) {
    rustc_span::create_default_session_globals_then(|| {
        let sm = Arc::new(SourceMap::new(FilePathMapping::empty()));
        sm.new_source_file(filename(&sm, "test.rs"), code.to_owned());

        let output = Arc::new(Mutex::new(Vec::new()));
        let je = JsonEmitter::new(
            Box::new(Shared { data: output.clone() }),
            Some(sm),
            true, // pretty
            HumanReadableErrorType { short: true, unicode: false },
            ColorConfig::Never,
        );

        let span = Span::with_root_ctxt(BytePos(span.0), BytePos(span.1));
        DiagCtxt::new(Box::new(je)).handle().span_err(span, "foo");

        let bytes = output.lock().unwrap();
        let actual_output = str::from_utf8(&bytes).unwrap();
        let actual_output: TestData = serde_json::from_str(actual_output).unwrap();
        let spans = actual_output.spans;
        assert_eq!(spans.len(), 1);

        assert_eq!(expected_output, spans[0])
    })
}

#[test]
fn empty() {
    test_positions(
        " ",
        (0, 1),
        SpanTestData {
            byte_start: 0,
            byte_end: 1,
            line_start: 1,
            column_start: 1,
            line_end: 1,
            column_end: 2,
        },
    )
}

#[test]
fn bom() {
    test_positions(
        "\u{feff} ",
        (0, 1),
        SpanTestData {
            byte_start: 3,
            byte_end: 4,
            line_start: 1,
            column_start: 1,
            line_end: 1,
            column_end: 2,
        },
    )
}

#[test]
fn lf_newlines() {
    test_positions(
        "\nmod foo;\nmod bar;\n",
        (5, 12),
        SpanTestData {
            byte_start: 5,
            byte_end: 12,
            line_start: 2,
            column_start: 5,
            line_end: 3,
            column_end: 3,
        },
    )
}

#[test]
fn crlf_newlines() {
    test_positions(
        "\r\nmod foo;\r\nmod bar;\r\n",
        (5, 12),
        SpanTestData {
            byte_start: 6,
            byte_end: 14,
            line_start: 2,
            column_start: 5,
            line_end: 3,
            column_end: 3,
        },
    )
}

#[test]
fn crlf_newlines_with_bom() {
    test_positions(
        "\u{feff}\r\nmod foo;\r\nmod bar;\r\n",
        (5, 12),
        SpanTestData {
            byte_start: 9,
            byte_end: 17,
            line_start: 2,
            column_start: 5,
            line_end: 3,
            column_end: 3,
        },
    )
}

#[test]
fn span_before_crlf() {
    test_positions(
        "foo\r\nbar",
        (2, 3),
        SpanTestData {
            byte_start: 2,
            byte_end: 3,
            line_start: 1,
            column_start: 3,
            line_end: 1,
            column_end: 4,
        },
    )
}

#[test]
fn span_on_crlf() {
    test_positions(
        "foo\r\nbar",
        (3, 4),
        SpanTestData {
            byte_start: 3,
            byte_end: 5,
            line_start: 1,
            column_start: 4,
            line_end: 2,
            column_end: 1,
        },
    )
}

#[test]
fn span_after_crlf() {
    test_positions(
        "foo\r\nbar",
        (4, 5),
        SpanTestData {
            byte_start: 5,
            byte_end: 6,
            line_start: 2,
            column_start: 1,
            line_end: 2,
            column_end: 2,
        },
    )
}

// Trust: (TRANSPORT-LINE-BUDGET-1) emit one note through a non-pretty JSON emitter, the
// shape trustc uses for a verification transport payload, and return the emitted line.
fn emit_note_line(message: &str, code: Option<&str>) -> String {
    rustc_span::create_default_session_globals_then(|| {
        let sm = Arc::new(SourceMap::new(FilePathMapping::empty()));
        // trustc's transport note has a dummy span, which a session's source map
        // resolves to its first file.
        sm.new_source_file(filename(&sm, "lib.rs"), "pub fn f() {}\n".to_owned());
        let output = Arc::new(Mutex::new(Vec::new()));
        let je = JsonEmitter::new(
            Box::new(Shared { data: output.clone() }),
            Some(sm),
            false, // one line per diagnostic, as trustc writes it
            HumanReadableErrorType { short: false, unicode: false },
            ColorConfig::Never,
        );
        let dcx = DiagCtxt::new(Box::new(je));
        let mut diag = dcx.handle().struct_span_note(rustc_span::DUMMY_SP, message.to_string());
        if let Some(code) = code {
            diag.is_lint(code.to_string(), false, None);
        }
        diag.emit();
        let bytes = output.lock().unwrap();
        str::from_utf8(&bytes).unwrap().to_string()
    })
}

// Trust: (TRANSPORT-LINE-BUDGET-1) a transport note's payload travels once, in `message`;
// `rendered` is the short fixed statement, so the line is the escaped message plus a
// bounded frame (`trust_types::transport_budget::JSON_DIAGNOSTIC_FRAMING_OVERHEAD_BYTES`,
// 4 KiB).
#[test]
fn trust_transport_note_is_not_rendered_twice() {
    let payload =
        format!("TRUST_JSON:{{\"type\":\"function_result\",\"blob\":\"{}\"}}", "x".repeat(200_000));
    let line = emit_note_line(&payload, Some(TRUST_TRANSPORT_DIAGNOSTIC_CODE));
    assert_eq!(line.lines().count(), 1, "one diagnostic, one line");
    let value: serde_json::Value = serde_json::from_str(&line).unwrap();
    assert_eq!(value["message"], payload.as_str(), "the payload is the message, byte for byte");
    assert_eq!(value["rendered"], TRUST_TRANSPORT_RENDERED);
    assert_eq!(value["code"]["code"], TRUST_TRANSPORT_DIAGNOSTIC_CODE);
    // The message as a JSON string body (no quotes), as `trust_types::transport_budget`
    // prices it; the frame around it, newline included, stays under 4 KiB.
    let message_body = serde_json::to_string(&payload).unwrap().len() - 2;
    assert!(
        line.len() <= message_body + 4096,
        "line {} bytes for a {message_body}-byte message body",
        line.len()
    );
}

// Trust: (TRANSPORT-LINE-BUDGET-1) controls: an ordinary note, and a note with another
// code, still render their message in full.
#[test]
fn ordinary_notes_still_render_their_message() {
    let message = format!("an ordinary note {}", "y".repeat(10_000));
    for code in [None, Some("some_other_lint")] {
        let line = emit_note_line(&message, code);
        let value: serde_json::Value = serde_json::from_str(&line).unwrap();
        let rendered = value["rendered"].as_str().unwrap();
        assert!(rendered.contains(&message), "code {code:?}: rendered {rendered:?}");
        assert_ne!(rendered, TRUST_TRANSPORT_RENDERED);
    }
}

// Trust: structured compiler payloads must not be repeated in human rendering.
fn emit_payload_note(payload: String, rendered: Option<&str>) -> Vec<u8> {
    rustc_span::create_default_session_globals_then(|| {
        let output = Arc::new(Mutex::new(Vec::new()));
        let je = JsonEmitter::new(
            Box::new(Shared { data: output.clone() }),
            None,
            false,
            HumanReadableErrorType { short: false, unicode: false },
            ColorConfig::Never,
        );
        let dcx = DiagCtxt::new(Box::new(je));
        let mut diagnostic = dcx.handle().struct_span_note(rustc_span::DUMMY_SP, payload);
        diagnostic.is_lint("structured_payload_observation".to_string(), false, None);
        if let Some(rendered) = rendered {
            diagnostic.set_json_rendered_message(rendered.to_owned());
        }
        diagnostic.emit();
        drop(dcx);
        Arc::try_unwrap(output).unwrap().into_inner().unwrap()
    })
}

// Trust: the default remains unchanged, including escaping and UTF-8.
#[test]
fn json_rendered_message_is_opt_in_and_preserves_structured_payload() {
    let payload = "structured rows: \"quoted\" \\ newline\nα".to_string();
    let ordinary = emit_payload_note(payload.clone(), None);
    let ordinary: serde_json::Value = serde_json::from_slice(&ordinary).unwrap();
    assert_eq!(ordinary["message"], payload);
    assert!(ordinary["rendered"].as_str().unwrap().contains("structured rows:"));

    let output = emit_payload_note(payload.clone(), Some("structured rows are in message"));
    let compact: serde_json::Value = serde_json::from_slice(&output).unwrap();
    assert_eq!(compact["message"], payload);
    assert!(compact["rendered"].as_str().unwrap().contains("structured rows are in message"));
    assert!(!compact["rendered"].as_str().unwrap().contains("quoted"));
    for field in ["$message_type", "code", "level", "spans", "children"] {
        assert_eq!(compact[field], ordinary[field], "changed structured field {field}");
    }
}

// Trust: the rendering hint preserves real parent and child source metadata.
#[test]
fn json_rendered_message_preserves_primary_and_child_spans() {
    rustc_span::create_default_session_globals_then(|| {
        const SOURCE: &str = "let primary = 1;\nlet child = 2;\n";
        const PAYLOAD: &str = "original-top-level-payload-sentinel";
        const CHILD: &str = "child-span-note-sentinel";
        const HINT: &str = "short-rendered-hint-sentinel";
        const LINT: &str = "spanned_payload_observation";
        let sm = Arc::new(SourceMap::new(FilePathMapping::empty()));
        let file = sm.new_source_file(filename(&sm, "metadata.rs"), SOURCE.to_owned());
        let span_for = |word: &str| {
            let start = SOURCE.find(word).unwrap() as u32;
            Span::with_root_ctxt(
                file.start_pos + BytePos(start),
                file.start_pos + BytePos(start + word.len() as u32),
            )
        };
        let primary = span_for("primary");
        let child = span_for("child");
        let emit = |rendered: Option<&str>| {
            let output = Arc::new(Mutex::new(Vec::new()));
            let je = JsonEmitter::new(
                Box::new(Shared { data: output.clone() }),
                Some(sm.clone()),
                false,
                HumanReadableErrorType { short: false, unicode: false },
                ColorConfig::Never,
            );
            let dcx = DiagCtxt::new(Box::new(je));
            let mut diagnostic = dcx.handle().struct_span_note(primary, PAYLOAD);
            diagnostic.is_lint(LINT.to_owned(), false, None);
            diagnostic.span_note(child, CHILD);
            if let Some(rendered) = rendered {
                diagnostic.set_json_rendered_message(rendered.to_owned());
            }
            diagnostic.emit();
            drop(dcx);
            let bytes = Arc::try_unwrap(output).unwrap().into_inner().unwrap();
            serde_json::from_slice::<serde_json::Value>(&bytes).unwrap()
        };
        let ordinary = emit(None);
        let compact = emit(Some(HINT));
        let spans = ordinary["spans"].as_array().unwrap();
        assert!(!spans.is_empty(), "the control must carry a real primary span");
        assert!(spans.iter().any(|span| span["is_primary"] == true));
        let children = ordinary["children"].as_array().unwrap();
        assert!(!children.is_empty(), "the control must carry a child note");
        let child_notes: Vec<_> = children.iter().filter(|note| note["message"] == CHILD).collect();
        assert_eq!(child_notes.len(), 1, "the child sentinel must identify a real note");
        assert!(!child_notes[0]["spans"].as_array().unwrap().is_empty());
        assert_eq!(ordinary["code"]["code"], LINT);
        assert_eq!(ordinary["message"], PAYLOAD);
        for field in ["$message_type", "message", "code", "level", "spans", "children"] {
            assert_eq!(compact[field], ordinary[field], "changed structured field {field}");
        }
        let ordinary_rendered = ordinary["rendered"].as_str().unwrap();
        assert!(ordinary_rendered.contains(PAYLOAD));
        assert!(ordinary_rendered.contains(CHILD));
        let compact_rendered = compact["rendered"].as_str().unwrap();
        assert!(compact_rendered.contains(HINT));
        assert!(compact_rendered.contains(CHILD));
        assert!(!compact_rendered.contains(PAYLOAD));
    });
}

// Trust: 32 MiB of permitted decoded artifacts become 64 MiB of inline hex.
// A complete rendered duplicate crosses Targo's unchanged 128 MiB line cap.
// This tests the real JsonEmitter; trust-types' serialization observation uses
// the actual artifact constructors and full FunctionTransportResult schema.
#[test]
fn json_rendered_message_avoids_duplicate_payload_at_transport_boundary() {
    const LINE_BYTES: usize = 128 * 1024 * 1024;
    let payload = format!("observed inline hex: {}", "a".repeat(64 * 1024 * 1024));
    let output = emit_payload_note(payload.clone(), Some("structured results are in message"));
    assert!(output.len() < LINE_BYTES, "diagnostic line has {} bytes", output.len());
    let diagnostic: serde_json::Value = serde_json::from_slice(&output).unwrap();
    assert!(
        diagnostic["message"].as_str() == Some(payload.as_str()),
        "the complete original bytes must survive"
    );
    let rendered = diagnostic["rendered"].as_str().unwrap();
    assert!(rendered.contains("structured results are in message"));
    assert!(rendered.len() < 1024);
}

// Trust: presentation does not change the identity of a complete diagnostic.
#[test]
fn json_rendered_message_does_not_change_deduplication() {
    let original = crate::DiagInner::new(crate::Level::Note, "complete structured payload");
    let mut summarized = original.clone();
    summarized.set_json_rendered_message("short rendering");
    assert_eq!(original.dedup_hash(), summarized.dedup_hash());
}
