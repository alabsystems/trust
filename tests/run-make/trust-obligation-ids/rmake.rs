// Trust (T9, 2026-10-09): an obligation's stable key, `<def_path>#<local id>`,
// is content-addressed, so edits that do not touch an obligation's own text do
// not move its key.
//
// `a.rs` is compiled, then `b.rs` — the same program with twenty comment lines
// and an unrelated function inserted at the top, two functions swapped, and,
// inside `f`, a division of the same kind inserted ABOVE `a / b`, an unrelated
// line inserted below it, and two multiplications swapped — under the same
// crate name and file name. The ordinal `obligation_id` renumbers under such
// edits, and so would any key that ranked a function's rows of one kind by
// position (a silent fallback from content to position); the content-addressed
// key must not. Nor may it read the END of a row's span: measured 2026-10-10,
// `f`'s rows are published as points at their start (`lo == hi`) from `a.rs`
// and as ranges from `b.rs` — the inserted division alone flips them (measured
// on `f` compiled alone with and without it; the swap and the unrelated line
// do not) — and a key that read the range's tokens moved every key of `f`.
// So:
//   * every function of `a.rs` keeps its exact key set in `b.rs`;
//   * `f` keeps the key of every obligation whose span lies on one line — the
//     `a / b` division below the inserted one, and both swapped
//     multiplications, included — and gains the inserted division's;
//   * the untouched functions keep their `source_sha256`, and `f`'s moves;
//   * within a function every key is distinct — `add3`'s two additions and the
//     macro division's twins included — and there is one id per row.

use std::collections::{BTreeMap, BTreeSet};

use run_make_support::serde_json::{self, Value};
use run_make_support::{bin_name, cmd, rfs, rustc_path};

const TRUST_VANILLA_REAL_RUSTC_ENV: &str = "__COMPILETEST_TRUST_VANILLA_REAL_RUSTC";

struct Function {
    keys: BTreeSet<String>,
    /// Each key's `(line_start, line_end)`, when its row has a location.
    lines: BTreeMap<String, (u64, u64)>,
    /// Each key's row kind.
    kinds: BTreeMap<String, String>,
    source: Option<String>,
    expanded: Option<Value>,
}

/// `function -> (its keys, its source digest)` from the transport rows.
fn functions(stderr: &str) -> BTreeMap<String, Function> {
    let mut out = BTreeMap::new();
    for line in stderr.lines() {
        let Some(payload) = line.strip_prefix("TRUST_JSON:") else { continue };
        let row: Value = serde_json::from_str(payload).expect("TRUST_JSON payload is JSON");
        if row["type"] != "function_result" {
            continue;
        }
        let function = row["function"].as_str().expect("function row names its function");
        let results = row["results"].as_array().expect("function row has results");
        let ids: Vec<&str> = row["stable_ids"]
            .as_array()
            .map(|ids| ids.iter().map(|id| id.as_str().expect("an id is a string")).collect())
            .unwrap_or_default();
        assert_eq!(ids.len(), results.len(), "{function}: one stable id per row: {row}");
        let keys: BTreeSet<String> = ids.iter().map(|id| format!("{function}#{id}")).collect();
        let lines = ids
            .iter()
            .zip(results)
            .filter_map(|(id, result)| {
                let location = &result["location"];
                Some((
                    format!("{function}#{id}"),
                    (location["line_start"].as_u64()?, location["line_end"].as_u64()?),
                ))
            })
            .collect();
        let kinds = ids
            .iter()
            .zip(results)
            .map(|(id, result)| {
                let kind = result["kind"].as_str().expect("a row names its kind").to_string();
                (format!("{function}#{id}"), kind)
            })
            .collect();
        assert_eq!(keys.len(), ids.len(), "{function}: stable ids are distinct: {ids:?}");
        for id in &ids {
            assert!(
                id.len() == 16 && id.bytes().all(|b| b.is_ascii_hexdigit() && !b.is_ascii_uppercase()),
                "{function}: `{id}` is sixteen lowercase hex digits"
            );
        }
        let source = row["source_sha256"].as_str().map(str::to_string);
        assert!(
            out.insert(function.to_string(), Function { keys, lines, kinds, source, expanded: row.get("expanded_function_identity").cloned() }).is_none()
        );
    }
    out
}

fn compile(trustc: &std::path::Path, source: &str, out: &str) -> String {
    rfs::write("obligation_ids.rs", source);
    cmd(trustc)
        .arg("--edition=2021")
        .arg("--crate-type=lib")
        .arg("--crate-name=obligation_ids")
        .arg("--emit=metadata")
        .arg("-Ztrust-verify=on")
        .arg("-Ztrust-policy=advisory")
        .arg("-Ztrust-verify-output=json")
        .arg("--error-format=human")
        .arg("obligation_ids.rs")
        .arg("-o")
        .arg(format!("lib{out}.rmeta"))
        // An inherited nested-process off-switch would beat `-Ztrust-verify=on`.
        .env_remove("TRUST_NO_VERIFY")
        .run()
        .stderr_utf8()
}

fn main() {
    let rustc = std::path::PathBuf::from(rustc_path());
    let trustc = rustc.with_file_name(bin_name("trustc"));
    let trustc = if trustc.exists() { trustc } else { rustc };
    if std::env::var_os(TRUST_VANILLA_REAL_RUSTC_ENV).is_some() {
        // The upstream compiler does not know Trust's policy/output options.
        return;
    }

    let before = functions(&compile(&trustc, &rfs::read_to_string("a.rs"), "a"));
    let after = functions(&compile(&trustc, &rfs::read_to_string("b.rs"), "b"));

    for name in ["obligation_ids::div_index", "obligation_ids::add3", "obligation_ids::f"] {
        let function = before.get(name).unwrap_or_else(|| panic!("a.rs: no row for {name}"));
        assert!(!function.keys.is_empty(), "{name} carries obligations");
    }
    assert!(
        before["obligation_ids::add3"].keys.len() >= 2,
        "add3's two additions are two keys: {:?}",
        before["obligation_ids::add3"].keys
    );
    assert!(after.contains_key("obligation_ids::unrelated"), "b.rs adds `unrelated`");

    for (name, function) in &before {
        let edited = after.get(name).unwrap_or_else(|| panic!("b.rs: no row for {name}"));
        if name == "obligation_ids::f" {
            // Every row of `f` whose span lies on one line is anchored on text
            // none of the edits changed. A row whose span covers several lines
            // (a whole-body row, if the compiler publishes one) is anchored on
            // edited text, so its key may move.
            let one_line: BTreeSet<&String> = function
                .keys
                .iter()
                .filter(|key| function.lines.get(*key).is_some_and(|(lo, hi)| lo == hi))
                .collect();
            let on_line = |line: u64, kind: &str| {
                one_line.iter().any(|key| {
                    function.lines[*key] == (line, line) && function.kinds[*key] == kind
                })
            };
            assert!(on_line(12, "divzero"), "a.rs:12 `a / b` is a division row: {one_line:?}");
            for key in one_line {
                assert!(edited.keys.contains(key), "f: the unedited obligation {key} lost its key");
            }
            let divisions = |function: &Function| {
                function.kinds.values().filter(|kind| *kind == "divzero").count()
            };
            assert!(
                divisions(edited) > divisions(function),
                "b.rs inserts a division above `a / b`, which mints a key of its own"
            );
        } else {
            assert_eq!(
                function.keys, edited.keys,
                "{name}: an edit that touches none of its obligations moved its keys"
            );
        }
        assert!(function.source.is_some(), "{name}: the compiler states its source digest");
        if name == "obligation_ids::f" {
            assert_ne!(function.source, edited.source, "f was edited: its source digest moves");
        } else {
            assert_eq!(function.source, edited.source, "{name} is untouched: same source digest");
        }
    }

    // Trust: a macro definition's template span can remain identical while an
    // invocation changes the actual body. Neither that template nor the call
    // alone is the generated item's complete source. Withhold its source digest
    // until the compiler can describe that source faithfully; keep ordinary
    // source identity and the existing stable obligation keys intact.
    let macro_runs: Vec<_> = ["a", "b", "c"]
        .into_iter()
        .map(|variant| {
            functions(&compile(
                &trustc,
                &rfs::read_to_string(format!("macro-source-{variant}.rs")),
                &format!("macro-{variant}"),
            ))
        })
        .collect();
    for run in &macro_runs {
        for name in ["obligation_ids::generated", "obligation_ids::neighbor"] {
            let function = run.get(name).unwrap_or_else(|| panic!("missing generated {name}"));
            assert!(!function.keys.is_empty(), "{name} still carries its obligations");
            assert!(function.source.is_none(), "{name}: template text is not the function source");
            assert_eq!(function.expanded.as_ref().unwrap()["schema"], "trust.expanded-function-input.v1");
        }
        for name in ["obligation_ids::ordinary", "obligation_ids::untouched"] {
            assert!(run[name].source.is_some(), "{name}: ordinary source digest is retained");
            assert!(run[name].expanded.is_none(), "ordinary source remains a distinct identity");
        }
    }
    for (before, after) in [(0, 1), (1, 2)] {
        assert_ne!(macro_runs[before]["obligation_ids::generated"].expanded,
            macro_runs[after]["obligation_ids::generated"].expanded);
    }
    assert_eq!(macro_runs[0]["obligation_ids::generated"].expanded.as_ref().unwrap()["definition"],
        macro_runs[1]["obligation_ids::generated"].expanded.as_ref().unwrap()["definition"]);
    assert_eq!(macro_runs[1]["obligation_ids::generated"].expanded.as_ref().unwrap()["invocation"],
        macro_runs[2]["obligation_ids::generated"].expanded.as_ref().unwrap()["invocation"]);
    assert_eq!(
        macro_runs[0]["obligation_ids::ordinary"].source,
        macro_runs[1]["obligation_ids::ordinary"].source,
        "an invocation edit leaves the ordinary function's source unchanged"
    );
    assert_ne!(
        macro_runs[1]["obligation_ids::ordinary"].source,
        macro_runs[2]["obligation_ids::ordinary"].source,
        "an ordinary function body edit changes its source digest"
    );
    assert!(macro_runs.windows(2).all(|pair| {
        pair[0]["obligation_ids::untouched"].source == pair[1]["obligation_ids::untouched"].source
    }));
}
