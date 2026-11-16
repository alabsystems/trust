use serde_json::{Value, json};

use super::*;

fn row(description: &str, outcome: &str, discharge: Option<&str>) -> TransportObligationResult {
    let mut row = json!({
        "obligation_id": format!("vc:fixture:{description}"),
        "kind": "assert",
        "description": description,
        "outcome": outcome,
        "solver": "diagnostic-fixture",
        "time_ms": 0,
    });
    if let Some(discharge) = discharge {
        row["grade"] = json!({
            "encoding": "unvalidated-encoder",
            "discharge": discharge,
            "premises": [],
        });
    }
    serde_json::from_value(row).expect("canonical row fixture")
}

#[test]
fn sibling_certificate_cannot_share_the_aggregate_diagnostic_line() {
    let rows = [
        row("panic freedom aggregate", "runtime_checked", None),
        row("independent panic site", "proved", Some("kernel-reference-checked")),
    ];
    let mut output = Vec::new();
    write_rows(true, &mut output, "fixture::body", &rows).expect("diagnostic rows");
    let text = String::from_utf8(output).expect("UTF-8");
    let records: Vec<Value> = text
        .lines()
        .map(|line| serde_json::from_str(line.strip_prefix(PREFIX).expect("diagnostic prefix")))
        .collect::<Result<_, _>>()
        .expect("one JSON record per line");
    assert_eq!(records.len(), rows.len());
    for (record, row) in records.iter().zip(&rows) {
        assert_eq!(record["function"], "fixture::body");
        assert_eq!(record["row"], serde_json::to_value(row).expect("canonical row"));
        assert_eq!(record.as_object().expect("record").len(), 2);
    }
    assert!(records[0]["row"].get("grade").is_none());
    assert_eq!(records[1]["row"]["grade"]["discharge"], "kernel-reference-checked");
}

#[test]
fn embedded_newlines_and_diagnostic_text_stay_inside_one_escaped_record() {
    let name = "fixture\nTRUST_ROW_DIAGNOSTIC:\"other\"";
    let rows = [row("panic\nsite \"quoted\"", "unknown", None)];
    let mut output = Vec::new();
    write_rows(true, &mut output, name, &rows).expect("escaped record");
    let text = String::from_utf8(output).expect("UTF-8");
    assert_eq!(text.lines().count(), 1);
    let record: Value =
        serde_json::from_str(text.trim_end().strip_prefix(PREFIX).expect("prefix")).expect("JSON");
    assert_eq!(record["function"], name);
    assert_eq!(record["row"], serde_json::to_value(&rows[0]).expect("canonical row"));
}

struct RefusingWriter;

impl Write for RefusingWriter {
    fn write(&mut self, _: &[u8]) -> io::Result<usize> {
        Err(io::Error::other("refused diagnostic write"))
    }
    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

#[test]
fn disabled_diagnostics_never_touch_the_writer() {
    let rows = [row("assertion", "unknown", None)];
    assert!(write_rows(false, &mut RefusingWriter, "fixture", &rows).is_ok());
    assert!(write_rows(true, &mut RefusingWriter, "fixture", &rows).is_err());
}
