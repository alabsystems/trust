//! Native controls for every case formerly owned by compare_elide_audit_test.py.

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use super::*;

const FN: [&str; 4] = ["lib", "lib", "demo", "demo::f"];
const OTHER: [&str; 4] = ["lib", "lib", "demo", "demo::g"];
const CRATE: [&str; 4] = ["lib", "lib", "demo", "crate"];
const DIGEST_A: &str = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
const DIGEST_B: &str = "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb";
const DELETED_SITE: &str = "crates/trust-verifier-api/src/lib.rs:MAX_VERIFIER_RUN_RECORDS";
const MOVED_SITE: &str =
    "compiler/rustc_mir_transform/src/trust_verify.rs:typed-chc-contract-decline";
const MEMO_SITE: &str =
    "compiler/rustc_mir_transform/src/trust_verify.rs:FUNCTION_SOURCE_DIGEST_MEMO_BUDGET_BYTES";

fn row(kind: &str, function: &[&str; 4], columns: &[&str]) -> String {
    std::iter::once(kind)
        .chain(function.iter().copied())
        .chain(columns.iter().copied())
        .collect::<Vec<_>>()
        .join("\t")
}

fn verdict(
    function: &[&str; 4],
    key: &str,
    status: &str,
    stop: &str,
    kind: &str,
    location: &str,
    audit_key: Option<&str>,
) -> String {
    row("VERDICT", function, &[key, status, stop, kind, location, audit_key.unwrap_or(key)])
}

fn base() -> Vec<String> {
    base_with(DIGEST_A, "proved", "solved", true)
}

fn base_with(digest: &str, status: &str, stop: &str, elided: bool) -> Vec<String> {
    vec![
        row(
            if elided { "ELIDED" } else { "KEPT" },
            &FN,
            &[
                if elided { "bb1" } else { "uncertified" },
                "Add",
                "f.rs:1:1-1:2",
                "k0123456789abcdef",
            ],
        ),
        row("ORIGINS", &FN, &["native", "complete", "unique=1", "ambiguous=0"]),
        verdict(&FN, "demo::f#0", status, stop, "overflow:add", "f.rs:1:1-1:2", None),
        row("ROWDIGEST", &FN, &["0", "overflow:add", "f.rs:1:1-1:2", digest]),
        verdict(&OTHER, "demo::g#0", "proved", "solved", "overflow:sub", "f.rs:2:1-2:2", None),
        row("ROWDIGEST", &OTHER, &["0", "overflow:sub", "f.rs:2:1-2:2", DIGEST_B]),
    ]
}

fn l3_rows() -> Vec<String> {
    base()
        .into_iter()
        .map(|line| {
            if line.starts_with("VERDICT") {
                line.rsplit_once('\t').unwrap().0.to_owned()
            } else {
                line
            }
        })
        .collect()
}

fn with_extra(mut rows: Vec<String>, extra: impl IntoIterator<Item = String>) -> Vec<String> {
    rows.extend(extra);
    rows
}

fn replace_function(rows: Vec<String>, from: &[&str; 4], to: &[&str; 4]) -> Vec<String> {
    rows.into_iter().map(|line| line.replacen(&from.join("\t"), &to.join("\t"), 1)).collect()
}

fn contains(output: &str, expected: impl AsRef<str>) {
    assert!(output.contains(expected.as_ref()), "missing {:?} in:\n{output}", expected.as_ref());
}

fn excludes(output: &str, unexpected: impl AsRef<str>) {
    assert!(
        !output.contains(unexpected.as_ref()),
        "unexpected {:?} in:\n{output}",
        unexpected.as_ref()
    );
}

struct Harness {
    _temporary: tempfile::TempDir,
    root: PathBuf,
}

impl Harness {
    fn new() -> Self {
        let temporary = tempfile::tempdir().unwrap();
        let root = temporary.path().to_owned();
        Self { _temporary: temporary, root }
    }

    fn side(&self, name: &str, lines: &[String], corpus: Option<&str>) -> PathBuf {
        let directory = self.root.join(name);
        let target = corpus.map_or_else(|| directory.clone(), |corpus| directory.join(corpus));
        fs::create_dir_all(&target).unwrap();
        let index = fs::read_dir(&target).unwrap().count() + 1;
        let mut text = lines.join("\n");
        text.push('\n');
        fs::write(target.join(format!("elide-audit-{index}.tsv")), text).unwrap();
        directory
    }

    fn run(&self, options: &[&str], parent: &Path, candidate: &Path) -> (u8, String) {
        let mut args = options.iter().map(|value| (*value).to_owned()).collect::<Vec<_>>();
        args.extend([parent.to_str().unwrap().into(), candidate.to_str().unwrap().into()]);
        super::cli::run_to_string(&args)
    }

    fn check(&self, options: &[&str], parent: &Path, candidate: &Path, expected: u8) -> String {
        let (status, output) = self.run(options, parent, candidate);
        assert_eq!(status, expected, "{options:?}:\n{output}");
        output
    }

    fn attribution(&self, text: impl AsRef<str>) -> PathBuf {
        let path = self.root.join("attributed.tsv");
        fs::write(&path, text.as_ref()).unwrap();
        path
    }

    fn records(&self, name: &str, entries: &[(&str, &str, &str)]) -> PathBuf {
        let directory = self.root.join(name);
        fs::create_dir_all(&directory).unwrap();
        let mut lines = vec![
            serde_json::json!({"schema":"trust.obligations.v1", "package":"demo"}).to_string(),
        ];
        for &(key, status, stop) in entries {
            lines.push(
                serde_json::json!({"fn":key.split('#').next().unwrap(), "source":null}).to_string(),
            );
            lines.push(
                serde_json::json!({"key":key,"kind":"overflow:add","status":status,"stop":stop,
                "file":"f.rs","line":1,"col":1})
                .to_string(),
            );
        }
        fs::write(directory.join("demo.obligations.ndjson"), format!("{}\n", lines.join("\n")))
            .unwrap();
        directory
    }
}

#[test]
fn l3_l4_rows_are_ignored_and_counted() {
    let h = Harness::new();
    let p = h.side("p", &base(), None);
    let c = h.side(
        "c",
        &with_extra(
            base(),
            [
                row("STOP", &FN, &["solver", "wall-backstop"]),
                row("CERTIFY-STOP", &FN, &["3", "unclassified"]),
                row("CAP", &FN, &[DELETED_SITE]),
                row("PARITY", &FN, &["row", "rows=1", "mismatches=1"]),
                row("ROWDIGEST", &FN, &["1", "overflow:mul", "f.rs:3:1-3:2", DIGEST_B]),
            ],
        ),
        None,
    );
    let out = h.check(&[], &p, &c, 0);
    contains(&out, "parent   : 2 L4 rows ignored in L3 mode (ROWDIGEST 2)");
    contains(
        &out,
        "candidate: 7 L4 rows ignored in L3 mode (CAP 1, CERTIFY-STOP 1, PARITY 1, ROWDIGEST 3, STOP 1)",
    );
}

#[test]
fn l3_verdicts_and_vacuity_are_unchanged() {
    let h = Harness::new();
    let p = h.side("p", &base(), None);
    let c = h.side("c", &base_with(DIGEST_A, "failed", "solved", true), None);
    contains(&h.check(&[], &p, &c, 1), "verdict moved");
    let bad = h.side("b", &with_extra(base(), [row("NONSENSE", &FN, &["x"])]), None);
    h.check(&[], &p, &bad, 3);
}

#[test]
fn l3_reads_the_t9_key_of_either_width() {
    let h = Harness::new();
    let p = h.side("p", &l3_rows(), None);
    let prefix = format!("VERDICT\t{}", FN.join("\t"));
    let changed = base()
        .into_iter()
        .map(|line| {
            if line.starts_with(&prefix) {
                verdict(
                    &FN,
                    "demo::f#0",
                    "proved",
                    "solved",
                    "overflow:add",
                    "f.rs:1:1-1:2",
                    Some("demo::f#9"),
                )
            } else {
                line
            }
        })
        .collect::<Vec<_>>();
    h.check(&[], &p, &h.side("c", &changed, None), 0);
    let moved = l3_rows()
        .into_iter()
        .map(|line| {
            if line.starts_with("VERDICT") {
                line.replacen("demo::f#0", "demo::f#1", 1)
            } else {
                line
            }
        })
        .collect::<Vec<_>>();
    h.check(&[], &p, &h.side("c2", &moved, None), 1);
}

#[test]
fn l4_identical_sides_pass() {
    let h = Harness::new();
    h.check(&["--l4"], &h.side("p", &base(), None), &h.side("c", &base(), None), 0);
}

#[test]
fn l4_changed_rowdigest_without_a_stop_is_a_violation() {
    let h = Harness::new();
    let p = h.side("p", &base(), None);
    let c = h.side("c", &base_with(DIGEST_B, "proved", "solved", true), None);
    contains(&h.check(&["--l4"], &p, &c, 1), "VIOLATION\trows moved\tlib\tlib\tdemo\tdemo::f");
}

#[test]
fn l4_changed_rowdigest_is_listed_under_a_stop_on_either_side() {
    let h = Harness::new();
    for stopped_parent in [true, false] {
        for (index, stop) in [
            row("STOP", &FN, &["solver", "wall-backstop"]),
            row("CERTIFY-STOP", &FN, &["0", "unclassified"]),
        ]
        .into_iter()
        .enumerate()
        {
            let mut p = base();
            let mut c = base_with(DIGEST_B, "proved", "solved", true);
            if stopped_parent {
                p.push(stop)
            } else {
                c.push(stop)
            }
            let p = h.side(&format!("p-{stopped_parent}-{index}"), &p, None);
            let c = h.side(&format!("c-{stopped_parent}-{index}"), &c, None);
            contains(&h.check(&["--l4"], &p, &c, 0), "LISTED\trows clock-stopped");
        }
    }
}

#[test]
fn l4_a_verdict_that_states_no_cause_excuses_nothing() {
    let h = Harness::new();
    let p = h.side("p", &base_with(DIGEST_A, "unknown", "unclassified", true), None);
    let c = h.side("c", &base_with(DIGEST_B, "unknown", "unclassified", true), None);
    contains(&h.check(&["--l4"], &p, &c, 1), "VIOLATION\trows moved");
    let moved = h.side("c2", &base_with(DIGEST_B, "proved", "solved", true), None);
    let out = h.check(&["--l4"], &p, &moved, 1);
    contains(&out, "VIOLATION\tverdict moved\tlib\tlib\tdemo\tdemo::f");
    contains(&out, "VIOLATION\trows moved\tlib\tlib\tdemo\tdemo::f");
    excludes(&out, "LISTED");
    let prefix = format!("VERDICT\t{}", FN.join("\t"));
    let dropped = base_with(DIGEST_A, "unknown", "unclassified", true)
        .into_iter()
        .filter(|line| !line.starts_with(&prefix))
        .collect::<Vec<_>>();
    contains(
        &h.check(&["--l4"], &p, &h.side("c3", &dropped, None), 1),
        "VIOLATION\tverdict moved\tlib\tlib\tdemo\tdemo::f\tdemo::f#0",
    );
}

#[test]
fn l4_every_excuse_is_scoped_to_its_own_function() {
    let h = Harness::new();
    let cases = [
        (vec![row("STOP", &OTHER, &["solver", "wall-backstop"])], vec![]),
        (vec![], vec![row("CERTIFY-STOP", &OTHER, &["0", "unclassified"])]),
        {
            let v =
                verdict(&OTHER, "demo::g#1", "unknown", "wall-backstop", "k", "f.rs:3:1-3:2", None);
            (vec![v.clone()], vec![v])
        },
        (vec![row("CAP", &OTHER, &[DELETED_SITE])], vec![]),
    ];
    let changes = [
        base_with(DIGEST_B, "proved", "solved", true),
        base_with(DIGEST_A, "failed", "solved", true),
        base_with(DIGEST_A, "proved", "solved", false),
    ];
    for (case, (pe, ce)) in cases.into_iter().enumerate() {
        for (change, changed) in changes.iter().enumerate() {
            let p = h.side(&format!("p-{case}-{change}"), &with_extra(base(), pe.clone()), None);
            let c = h.side(
                &format!("c-{case}-{change}"),
                &with_extra(changed.clone(), ce.clone()),
                None,
            );
            let out = h.check(&["--l4", "--deleted-caps", "C09d"], &p, &c, 1);
            contains(&out, "VIOLATION");
            excludes(&out, "LISTED");
            let p = h.side(
                &format!("p2-{case}-{change}"),
                &with_extra(base(), replace_function(pe.clone(), &OTHER, &FN)),
                None,
            );
            let c = h.side(
                &format!("c2-{case}-{change}"),
                &with_extra(changed.clone(), replace_function(ce.clone(), &OTHER, &FN)),
                None,
            );
            h.check(&["--l4", "--deleted-caps", "C09d"], &p, &c, 0);
        }
    }
}

#[test]
fn l4_an_attribution_is_scoped_to_its_function() {
    let h = Harness::new();
    let p = h.side("p", &with_extra(base(), [row("CAP", &CRATE, &[DELETED_SITE])]), None);
    let c = h.side("c", &base_with(DIGEST_B, "proved", "solved", true), None);
    let a = h.attribution(format!("lib\tlib\tdemo\t{DELETED_SITE}\tdemo::g\n"));
    contains(
        &h.check(
            &["--l4", "--deleted-caps", "C09d", "--attributed", a.to_str().unwrap()],
            &p,
            &c,
            1,
        ),
        "VIOLATION\trows moved\tlib\tlib\tdemo\tdemo::f",
    );
}

#[test]
fn l4_the_audit_key_matches_rows_across_builds() {
    let h = Harness::new();
    let p = h.side("p", &base(), None);
    let replace = |key: &str, audit: &str| {
        base()
            .into_iter()
            .map(|line| {
                if line.starts_with(&format!("VERDICT\t{}", FN.join("\t"))) {
                    verdict(
                        &FN,
                        key,
                        "proved",
                        "solved",
                        "overflow:add",
                        "f.rs:1:1-1:2",
                        Some(audit),
                    )
                } else {
                    line
                }
            })
            .collect::<Vec<_>>()
    };
    h.check(&["--l4"], &p, &h.side("c", &replace("demo::f#77", "demo::f#0"), None), 0);
    let out = h.check(&["--l4"], &p, &h.side("c2", &replace("demo::f#0", "demo::f#1"), None), 1);
    assert_eq!(out.matches("VIOLATION\tverdict moved").count(), 2, "{out}");
    h.check(&["--l4"], &h.side("p3", &l3_rows(), None), &p, 3);
}

#[test]
fn l4_a_def_path_under_crate_is_a_function() {
    for (scope, expected) in [
        ("crate", true),
        ("crate:r1", true),
        ("crate:finalize", true),
        ("crate::f", false),
        ("crate:", false),
        ("crates::f", false),
    ] {
        assert_eq!(
            is_crate_level(&["i".into(), "o".into(), "c".into(), scope.into()]),
            expected,
            "{scope}"
        );
    }
    let h = Harness::new();
    let spelled = ["lib", "lib", "demo", "crate::f"];
    let p = h.side(
        "p",
        &with_extra(
            replace_function(base(), &FN, &spelled),
            [row("STOP", &spelled, &["solver", "wall-backstop"])],
        ),
        None,
    );
    let c = h.side(
        "c",
        &replace_function(base_with(DIGEST_B, "proved", "solved", true), &FN, &spelled),
        None,
    );
    contains(
        &h.check(&["--l4"], &p, &c, 0),
        "LISTED\trows clock-stopped\tlib\tlib\tdemo\tcrate::f",
    );
}

#[test]
fn l4_functions_clock_stopped_on_the_candidate_only_are_printed() {
    let h = Harness::new();
    let p =
        h.side("p", &with_extra(base(), [row("STOP", &OTHER, &["solver", "wall-backstop"])]), None);
    let c = h.side("c", &with_extra(base(), [row("STOP", &FN, &["solver", "rss-backstop"])]), None);
    let out = h.check(&["--l4"], &p, &c, 0);
    contains(&out, "clock-stopped functions: 2 (1 on the parent, 1 on the candidate only)");
    contains(&out, "CANDIDATE-CLOCK\tlib\tlib\tdemo\tdemo::f");
    excludes(&out, "CANDIDATE-CLOCK\tlib\tlib\tdemo\tdemo::g");
}

#[test]
fn l4_a_verdict_that_names_a_clock_exempts_its_function() {
    let h = Harness::new();
    let p = h.side("p", &base_with(DIGEST_A, "unknown", "wall-backstop", true), None);
    let c = h.side("c", &base_with(DIGEST_B, "unknown", "wall-backstop", true), None);
    contains(&h.check(&["--l4"], &p, &c, 0), "LISTED\trows clock-stopped");
}

#[test]
fn l4_a_reproducible_stop_does_not_list() {
    let h = Harness::new();
    let p = h.side("p", &with_extra(base(), [row("STOP", &FN, &["solver", "effort"])]), None);
    h.check(&["--l4"], &p, &h.side("c", &base_with(DIGEST_B, "proved", "solved", true), None), 1);
}

#[test]
fn l4_a_crate_level_stop_marks_no_function() {
    let h = Harness::new();
    let p =
        h.side("p", &with_extra(base(), [row("STOP", &CRATE, &["solver", "wall-backstop"])]), None);
    h.check(&["--l4"], &p, &h.side("c", &base_with(DIGEST_B, "proved", "solved", true), None), 1);
}

#[test]
fn l4_parent_cap_of_a_deleted_site_lists_only_under_its_commit() {
    let h = Harness::new();
    let p = h.side("p", &with_extra(base(), [row("CAP", &FN, &[DELETED_SITE])]), None);
    let c = h.side("c", &base_with(DIGEST_B, "failed", "solved", true), None);
    h.check(&["--l4"], &p, &c, 1);
    h.check(&["--l4", "--deleted-caps", "C12"], &p, &c, 1);
    let out = h.check(&["--l4", "--deleted-caps", "C09d"], &p, &c, 0);
    contains(&out, format!("LISTED\trows cap-attributed (C09d {DELETED_SITE})"));
    contains(&out, "LISTED\tverdict cap-attributed");
}

#[test]
fn l4_a_candidate_cap_attributes_nothing() {
    let h = Harness::new();
    let p = h.side("p", &base(), None);
    let c = h.side(
        "c",
        &with_extra(
            base_with(DIGEST_B, "proved", "solved", true),
            [row("CAP", &FN, &[DELETED_SITE])],
        ),
        None,
    );
    h.check(&["--l4", "--deleted-caps", "C09d"], &p, &c, 1);
}

#[test]
fn l4_a_candidate_hit_of_a_deleted_site_is_a_violation() {
    let h = Harness::new();
    let p = h.side("p", &with_extra(base(), [row("CAP", &FN, &[DELETED_SITE])]), None);
    let c = h.side("c", &with_extra(base(), [row("CAP", &FN, &[DELETED_SITE])]), None);
    let out = h.check(&["--l4", "--deleted-caps", "C09d"], &p, &c, 1);
    contains(
        &out,
        format!("VIOLATION\tcandidate still refuses at a deleted cap site (C09d {DELETED_SITE}"),
    );
    h.check(&["--l4", "--deleted-caps", "C12"], &p, &c, 0);
    let p = h.side("p2", &with_extra(base(), [row("CAP", &FN, &[MOVED_SITE])]), None);
    let c = h.side(
        "c2",
        &with_extra(
            base_with(DIGEST_A, "failed", "solved", true),
            [row("CAP", &FN, &[MOVED_SITE])],
        ),
        None,
    );
    contains(
        &h.check(&["--l4", "--deleted-caps", "C09d"], &p, &c, 0),
        format!("LISTED\tverdict cap-attributed (C09d {MOVED_SITE})"),
    );
}

#[test]
fn l4_an_answer_preserving_site_attributes_no_difference() {
    let h = Harness::new();
    let p = h.side("p", &with_extra(base(), [row("CAP", &FN, &[MEMO_SITE])]), None);
    let c = h.side("c", &base_with(DIGEST_B, "failed", "solved", true), None);
    excludes(&h.check(&["--l4", "--deleted-caps", "C09d"], &p, &c, 1), "cap-attributed (");
    let both = h.side(
        "p2",
        &with_extra(base(), [row("CAP", &FN, &[MEMO_SITE]), row("CAP", &FN, &[DELETED_SITE])]),
        None,
    );
    contains(
        &h.check(&["--l4", "--deleted-caps", "C09d"], &both, &c, 0),
        format!("LISTED\trows cap-attributed (C09d {DELETED_SITE})"),
    );
    let cr = h.side("p3", &with_extra(base(), [row("CAP", &CRATE, &[MEMO_SITE])]), None);
    h.check(&["--l4", "--deleted-caps", "C09d"], &cr, &h.side("c3", &base(), None), 0);
    let a = h.attribution(format!("lib\tlib\tdemo\t{MEMO_SITE}\tdemo::f\n"));
    contains(
        &h.check(
            &["--l4", "--deleted-caps", "C09d", "--attributed", a.to_str().unwrap()],
            &cr,
            &c,
            3,
        ),
        "an answer-preserving site attributes nothing",
    );
    contains(
        &h.check(
            &["--l4", "--deleted-caps", "C09d"],
            &h.side("p4", &base(), None),
            &h.side("c4", &with_extra(base(), [row("CAP", &FN, &[MEMO_SITE])]), None),
            1,
        ),
        format!("candidate still refuses at a deleted cap site (C09d {MEMO_SITE}"),
    );
}

#[test]
fn l4_crate_level_cap_of_a_deleted_site_could_not_run_unless_attributed() {
    let h = Harness::new();
    let p = h.side("p", &with_extra(base(), [row("CAP", &CRATE, &[DELETED_SITE])]), None);
    let c = h.side("c", &base(), None);
    contains(&h.check(&["--l4", "--deleted-caps", "C09d"], &p, &c, 3), "UNATTRIBUTED");
    h.check(&["--l4", "--deleted-caps", "C12"], &p, &c, 0);
    let a =
        h.attribution(format!("# reviewed by hand\nlib\tlib\tdemo\t{DELETED_SITE}\t-\tno row\n"));
    h.check(&["--l4", "--deleted-caps", "C09d", "--attributed", a.to_str().unwrap()], &p, &c, 0);
}

#[test]
fn l4_an_attribution_names_the_function_it_explains() {
    let h = Harness::new();
    let p = h.side("p", &with_extra(base(), [row("CAP", &CRATE, &[DELETED_SITE])]), None);
    let c = h.side("c", &base_with(DIGEST_B, "proved", "solved", true), None);
    let a = h.attribution(format!("lib\tlib\tdemo\t{DELETED_SITE}\tdemo::f\n"));
    contains(
        &h.check(
            &["--l4", "--deleted-caps", "C09d", "--attributed", a.to_str().unwrap()],
            &p,
            &c,
            0,
        ),
        "rows cap-attributed",
    );
}

#[test]
fn l4_a_hash_inside_a_def_path_is_text() {
    let h = Harness::new();
    let closure = ["lib", "lib", "demo", "demo::f::{closure#0}"];
    let p = h.side(
        "p",
        &with_extra(replace_function(base(), &FN, &closure), [row("CAP", &CRATE, &[DELETED_SITE])]),
        None,
    );
    let c = h.side(
        "c",
        &replace_function(base_with(DIGEST_B, "proved", "solved", true), &FN, &closure),
        None,
    );
    let a = h.attribution(format!(
        "  # a comment line\nlib\tlib\tdemo\t{DELETED_SITE}\tdemo::f::{{closure#0}}\tsee #12\n"
    ));
    contains(
        &h.check(
            &["--l4", "--deleted-caps", "C09d", "--attributed", a.to_str().unwrap()],
            &p,
            &c,
            0,
        ),
        format!(
            "LISTED\trows cap-attributed (C09d {DELETED_SITE})\tlib\tlib\tdemo\tdemo::f::{{closure#0}}"
        ),
    );
}

#[test]
fn l4_a_stale_attribution_could_not_run() {
    let h = Harness::new();
    let c = h.side("c", &base_with(DIGEST_B, "proved", "solved", true), None);
    let a = h.attribution(format!("lib\tlib\tdemo\t{DELETED_SITE}\tdemo::f\n"));
    for (name, extra) in [
        ("none", vec![]),
        ("function-level", vec![row("CAP", &FN, &[DELETED_SITE])]),
        ("other-unit", vec![row("CAP", &["lib", "other", "demo", "crate"], &[DELETED_SITE])]),
    ] {
        let p = h.side(&format!("p-{name}"), &with_extra(base(), extra), None);
        contains(
            &h.check(
                &["--l4", "--deleted-caps", "C09d", "--attributed", a.to_str().unwrap()],
                &p,
                &c,
                3,
            ),
            "MALFORMED\t--attributed",
        );
    }
    let p = h.side("p-judged", &with_extra(base(), [row("CAP", &CRATE, &[DELETED_SITE])]), None);
    h.check(&["--l4", "--deleted-caps", "C12", "--attributed", a.to_str().unwrap()], &p, &c, 3);
}

#[test]
fn l4_parity_mismatch_is_a_violation() {
    let h = Harness::new();
    let p = h.side("p", &base(), None);
    let c = h.side(
        "c",
        &with_extra(base(), [row("PARITY", &FN, &["row", "rows=4", "mismatches=1"])]),
        None,
    );
    contains(&h.check(&["--l4"], &p, &c, 1), "parity mismatch (candidate, row)");
}

#[test]
fn l4_an_unjudged_identity_binding_is_listed_never_a_violation() {
    let h = Harness::new();
    let scope = row("PARITY", &FN, &["identity-scope", "rows=3", "mismatches=2"]);
    let cs = row("PARITY", &CRATE, &["identity-scope", "rows=1", "mismatches=1"]);
    let judged = row("PARITY", &FN, &["identity", "rows=5", "mismatches=0"]);
    let p = h.side("p", &base(), None);
    let c = h.side("c", &with_extra(base(), [scope.clone(), cs, judged]), None);
    let out = h.check(&["--l4", "--oracles", "identity"], &p, &c, 0);
    contains(
        &out,
        format!(
            "LISTED\tunjudged binding (candidate, identity-scope)\t{}\trows=3 mismatches=2",
            FN.join("\t")
        ),
    );
    contains(&out, format!("unjudged binding (candidate, identity-scope)\t{}", CRATE.join("\t")));
    let c = h.side(
        "c2",
        &with_extra(
            base(),
            [scope.clone(), row("PARITY", &FN, &["identity", "rows=5", "mismatches=1"])],
        ),
        None,
    );
    contains(&h.check(&["--l4"], &p, &c, 1), "VIOLATION\tparity mismatch (candidate, identity)");
    h.check(&["--l4", "--oracles", "identity-scope"], &p, &c, 2);
    let c = h.side("c3", &with_extra(base(), [scope]), None);
    contains(
        &h.check(&["--l4", "--oracles", "identity"], &p, &c, 3),
        "oracle `identity` has rows=0",
    );
}

#[test]
fn l4_an_oracle_with_no_rows_on_a_corpus_could_not_run() {
    let h = Harness::new();
    let p = h.side("p", &base(), Some("ui"));
    h.side("p", &base(), Some("crate"));
    let c = h.side(
        "c",
        &with_extra(base(), [row("PARITY", &FN, &["row", "rows=4", "mismatches=0"])]),
        Some("ui"),
    );
    h.side(
        "c",
        &with_extra(base(), [row("PARITY", &OTHER, &["row", "rows=0", "mismatches=0"])]),
        Some("crate"),
    );
    contains(
        &h.check(&["--l4", "--oracles", "row"], &p, &c, 3),
        "oracle `row` has rows=0 on corpus crate",
    );
    h.check(&["--l4"], &p, &c, 0);
}

#[test]
fn l4_a_side_without_rowdigest_could_not_run() {
    let h = Harness::new();
    let rows = base().into_iter().filter(|line| !line.starts_with("ROWDIGEST")).collect::<Vec<_>>();
    let p = h.side("p", &base(), None);
    let c = h.side("c", &rows, None);
    h.check(&["--l4"], &p, &c, 1);
    let p = h.side("p2", &rows, None);
    contains(&h.check(&["--l4"], &p, &c, 3), "a side recorded no ROWDIGEST row");
}

#[test]
fn l4_elided_difference_only_as_a_verdict_gate_in_a_clock_stopped_function() {
    let h = Harness::new();
    let p = h.side("p", &base(), None);
    let mut kept =
        base().into_iter().filter(|line| !line.starts_with("ELIDED")).collect::<Vec<_>>();
    kept.push(row("KEPT", &FN, &["uncertified", "Add", "f.rs:1:1-1:2", "k0123456789abcdef"]));
    let c = h.side("c", &kept, None);
    h.check(&["--l4"], &p, &c, 1);
    let stopped =
        h.side("c2", &with_extra(kept, [row("STOP", &FN, &["certify", "wall-backstop"])]), None);
    h.check(&["--l4"], &p, &stopped, 0);
    let absent = with_extra(
        base().into_iter().filter(|line| !line.starts_with("ELIDED")).collect(),
        [row("KEPT", &FN, &["absent", "Add", "f.rs:1:1-1:2", "k0123456789abcdef"])],
    );
    h.check(&["--l4"], &h.side("p3", &absent, None), &h.side("c3", &base(), None), 1);
}

#[test]
fn l4_unknown_cap_site_and_bad_digest_are_malformed() {
    let h = Harness::new();
    let p = h.side("p", &base(), None);
    for (index, bad) in [
        row("CAP", &FN, &["nowhere.rs:MAX_NOTHING"]),
        row("ROWDIGEST", &FN, &["9", "overflow:add", "f.rs:1:1-1:2", "xyz"]),
        row("STOP", &FN, &["solver", "tired"]),
        row("PARITY", &FN, &["vibes", "rows=1", "mismatches=0"]),
    ]
    .into_iter()
    .enumerate()
    {
        h.check(&["--l4"], &p, &h.side(&format!("c{index}"), &with_extra(base(), [bad]), None), 3);
    }
}

#[test]
fn l4_usage_errors() {
    let h = Harness::new();
    let p = h.side("p", &base(), None);
    h.check(&["--l4", "--deleted-caps", "C99"], &p, &p, 2);
    h.check(&["--deleted-caps", "C09d"], &p, &p, 2);
    h.check(&["--l4", "--oracles", "vibes"], &p, &p, 2);
}

fn repository() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).parent().unwrap().to_owned()
}

fn deleted_constants(groups: &[&str]) -> BTreeSet<(String, String)> {
    caps::DELETED_CAPS
        .iter()
        .filter(|(commit, _)| groups.contains(commit))
        .flat_map(|(_, sites)| sites.iter())
        .filter_map(|site| {
            let (path, name) = site.rsplit_once(':').unwrap();
            (name == name.to_ascii_uppercase() && !name.contains('-'))
                .then(|| (path.to_owned(), name.to_owned()))
        })
        .collect()
}

#[test]
fn cap_table_is_the_census_rows_l4_deletes() {
    let text = fs::read_to_string(
        repository().join("docs/audits/2026-10-08-t3-size-threshold-census.tsv"),
    )
    .unwrap();
    let mut lines = text.lines();
    let header = lines.next().unwrap().split('\t').collect::<Vec<_>>();
    let column = |name| header.iter().position(|item| *item == name).unwrap();
    let (file, constant, class, commit) =
        (column("file"), column("constant"), column("class"), column("commit"));
    let mut census = BTreeMap::<String, BTreeSet<(String, String)>>::new();
    for line in lines {
        let row = line.split('\t').collect::<Vec<_>>();
        if row[class] == "DEL-T3" && ["C09", "C11e", "C12"].contains(&row[commit]) {
            census
                .entry(row[commit].into())
                .or_default()
                .insert((row[file].into(), row[constant].into()));
        }
    }
    assert_eq!(deleted_constants(&["C09d"]), census["C09"]);
    assert_eq!(deleted_constants(&["C11e1", "C11e2"]), census["C11e"]);
    assert_eq!(deleted_constants(&["C12"]), census["C12"]);
    assert!(deleted_constants(&["C11e1"]).is_disjoint(&deleted_constants(&["C11e2"])));
    for &(group, sites) in caps::DELETED_CAPS {
        assert_eq!(deleted_constants(&[group]).len(), sites.len(), "{group}");
    }
    for &(group, sites) in caps::MOVED_CAPS {
        assert!(caps::DELETED_CAPS.iter().any(|(deleted_group, _)| *deleted_group == group));
        for site in sites {
            let name = site.rsplit_once(':').unwrap().1;
            assert!(name != name.to_ascii_uppercase() || name.contains('-'), "{site}");
        }
    }
    let all = caps::DELETED_CAPS
        .iter()
        .chain(caps::MOVED_CAPS)
        .flat_map(|(group, sites)| sites.iter().map(move |site| (*site, *group)))
        .collect::<Vec<_>>();
    let distinct = all.iter().map(|(site, _)| *site).collect::<BTreeSet<_>>();
    assert_eq!(distinct.len(), all.len(), "each cap site has one group owner");
    for (site, group) in all {
        assert_eq!(caps::site_commit(site), Some(group));
    }
    let deleted = caps::DELETED_CAPS
        .iter()
        .flat_map(|(_, sites)| sites.iter().copied())
        .collect::<BTreeSet<_>>();
    for site in caps::ANSWER_PRESERVING_CAPS {
        assert!(deleted.contains(site), "{site}");
    }
}

fn quoted_sites(text: &str) -> BTreeSet<String> {
    text.match_indices('"')
        .filter_map(|(offset, _)| {
            let tail = &text[offset + 1..];
            tail.find('"').map(|end| &tail[..end])
        })
        .filter(|value| {
            let Some((path, name)) = value.rsplit_once(':') else { return false };
            let mut chars = name.chars();
            ["compiler/", "crates/", "targo-trust/"].iter().any(|prefix| path.starts_with(prefix))
                && path.ends_with(".rs")
                && !value.chars().any(char::is_whitespace)
                && chars.next().is_some_and(|c| c.is_ascii_alphabetic() || c == '_')
                && chars.all(|c| c.is_ascii_alphanumeric() || c == '_' || c == '-')
        })
        .map(str::to_owned)
        .collect()
}

fn defines(path: &Path, constant: &str) -> bool {
    let Ok(text) = fs::read_to_string(path) else { return false };
    text.lines().any(|line| {
        let mut line = line.trim_start();
        if let Some(after) = line.strip_prefix("pub") {
            line = after;
            if line.starts_with('(') {
                let Some(end) = line.find(')') else { return false };
                line = &line[end + 1..];
                if !line.starts_with(char::is_whitespace) {
                    return false;
                }
            } else if !line.starts_with(char::is_whitespace) {
                return false;
            }
            line = line.trim_start();
        }
        let after = line.strip_prefix("const").or_else(|| line.strip_prefix("static"));
        let Some(after) = after else { return false };
        if !after.starts_with(char::is_whitespace) {
            return false;
        }
        let Some(after_name) = after.trim_start().strip_prefix(constant) else { return false };
        after_name.trim_start().starts_with(':')
    })
}

#[test]
fn cap_source_and_table_name_the_same_sites() {
    let repo = repository();
    let found = Command::new("git")
        .args(["grep", "-l", "-F", "audit_ledger::cap_hit", "--", "*.rs"])
        .current_dir(&repo)
        .output()
        .unwrap();
    assert!(found.status.success(), "{}", String::from_utf8_lossy(&found.stderr));
    let mut recorded = BTreeSet::new();
    for name in String::from_utf8(found.stdout).unwrap().lines() {
        // Comparator fixtures/catalog literals are not producer instrumentation;
        // letting this test see itself could mask a lost production CAP record.
        if name.starts_with("targo-trust/src/audit_comparison/") {
            continue;
        }
        recorded.extend(quoted_sites(&fs::read_to_string(repo.join(name)).unwrap()));
    }
    let table = caps::DELETED_CAPS
        .iter()
        .chain(caps::MOVED_CAPS)
        .flat_map(|(_, sites)| sites.iter().map(|site| (*site).to_owned()))
        .collect::<BTreeSet<_>>();
    assert!(
        recorded.is_subset(&table),
        "sites the table lacks: {:?}",
        recorded.difference(&table).collect::<Vec<_>>()
    );
    let unrecorded = table.difference(&recorded).cloned().collect::<BTreeSet<_>>();
    let moved = caps::MOVED_CAPS
        .iter()
        .flat_map(|(_, sites)| sites.iter().map(|site| (*site).to_owned()))
        .collect::<BTreeSet<_>>();
    assert!(
        unrecorded.is_disjoint(&moved),
        "a moved site still records its hits: {:?}",
        unrecorded.intersection(&moved).collect::<Vec<_>>()
    );
    let still_defined = unrecorded
        .iter()
        .filter(|site| {
            let (file, constant) = site.rsplit_once(':').unwrap();
            defines(&repo.join(file), constant)
        })
        .collect::<Vec<_>>();
    assert!(
        still_defined.is_empty(),
        "sites nothing records whose constant is still defined: {still_defined:?}"
    );
}

#[test]
fn cap_deleted_constant_is_told_from_a_kept_one() {
    let root = tempfile::tempdir().unwrap();
    let path = root.path().join("lib.rs");
    fs::write(&path, "pub const KEPT: usize = 1;\n    pub(crate) static ALSO_KEPT: u8 = 0;\n// The deleted GONE was 65,536.\nlet text = \"const NAMED: usize\";\n").unwrap();
    assert!(defines(&path, "KEPT"));
    assert!(defines(&path, "ALSO_KEPT"));
    assert!(!defines(&path, "GONE"));
    assert!(!defines(&path, "NAMED"));
    assert!(!defines(&root.path().join("missing.rs"), "KEPT"));
}

#[test]
fn obligations_identical_records_pass() {
    let h = Harness::new();
    let p = h.records("p", &[("demo::f#0", "proved", "solved")]);
    let c = h.records("t", &[("demo::f#0", "proved", "solved")]);
    h.check(&["--obligations"], &p, &c, 0);
}

#[test]
fn obligations_moved_status_with_a_reproducible_stop_is_a_violation() {
    let h = Harness::new();
    let p = h.records("p", &[("demo::f#0", "proved", "solved")]);
    let c = h.records("t", &[("demo::f#0", "unknown", "effort")]);
    contains(
        &h.check(&["--obligations"], &p, &c, 1),
        "VIOLATION\tobligation moved\tdemo\tdemo::f#0",
    );
}

#[test]
fn obligations_a_record_that_states_no_cause_excuses_nothing() {
    let h = Harness::new();
    let p = h.records(
        "p",
        &[("demo::f#0", "unknown", "unclassified"), ("demo::f#1", "proved", "solved")],
    );
    let c = h.records("t", &[("demo::f#0", "proved", "solved"), ("demo::f#1", "failed", "solved")]);
    let out = h.check(&["--obligations"], &p, &c, 1);
    contains(&out, "VIOLATION\tobligation moved\tdemo\tdemo::f#0");
    contains(&out, "VIOLATION\tobligation moved\tdemo\tdemo::f#1");
    excludes(&out, "LISTED");
}

#[test]
fn obligations_a_clock_record_lists_only_its_own_function() {
    let h = Harness::new();
    let p = h.records(
        "p",
        &[("demo::f#0", "proved", "solved"), ("demo::g#0", "unknown", "wall-backstop")],
    );
    let c = h.records(
        "t",
        &[("demo::f#0", "failed", "solved"), ("demo::g#0", "unknown", "wall-backstop")],
    );
    contains(
        &h.check(&["--obligations"], &p, &c, 1),
        "VIOLATION\tobligation moved\tdemo\tdemo::f#0",
    );
}

#[test]
fn obligations_moved_status_with_a_clock_stop_is_listed() {
    let h = Harness::new();
    let p = h.records("p", &[("demo::f#0", "proved", "solved")]);
    let c = h.records("t", &[("demo::f#0", "unknown", "wall-backstop")]);
    contains(&h.check(&["--obligations"], &p, &c, 0), "LISTED\tobligation clock-stopped");
}

#[test]
fn obligations_audit_rows_beside_the_records_widen_the_clock_rule() {
    let h = Harness::new();
    let p = h.records("p", &[("demo::f#0", "proved", "solved")]);
    let c = h.records("t", &[("demo::f#0", "failed", "solved")]);
    h.check(&["--obligations"], &p, &c, 1);
    let other = h.records("t2", &[("demo::f#0", "failed", "solved")]);
    h.side(
        "t2",
        &[
            verdict(&FN, "demo::f#0", "failed", "solved", "k", "l", None),
            row("STOP", &OTHER, &["solver", "wall-backstop"]),
        ],
        None,
    );
    h.check(&["--obligations"], &p, &other, 1);
    h.side(
        "t",
        &[
            verdict(&FN, "demo::f#0", "failed", "solved", "k", "l", None),
            row("STOP", &FN, &["solver", "wall-backstop"]),
        ],
        None,
    );
    h.check(&["--obligations"], &p, &c, 0);
}

#[test]
fn obligations_no_records_could_not_run() {
    let h = Harness::new();
    let p = h.records("p", &[("demo::f#0", "proved", "solved")]);
    let empty = h.root.join("empty");
    fs::create_dir(&empty).unwrap();
    h.check(&["--obligations"], &p, &empty, 3);
}

fn replace_package_header(directory: &Path, package: Option<&serde_json::Value>) {
    let path = directory.join("demo.obligations.ndjson");
    let text = fs::read_to_string(&path).unwrap();
    let (header, body) = text.split_once('\n').unwrap();
    let mut header: serde_json::Value = serde_json::from_str(header).unwrap();
    let header = header.as_object_mut().unwrap();
    match package {
        Some(package) => {
            header.insert("package".into(), package.clone());
        }
        None => {
            header.remove("package");
        }
    }
    fs::write(path, format!("{}\n{body}", serde_json::Value::Object(header.clone()))).unwrap();
}

#[test]
fn obligations_nonstring_package_headers_never_alias_string_identities() {
    let h = Harness::new();
    for (index, package) in [
        serde_json::Value::Null,
        serde_json::json!(true),
        serde_json::json!(42),
        serde_json::json!([]),
        serde_json::json!({"nested": 1}),
    ]
    .into_iter()
    .enumerate()
    {
        let p = h.records(&format!("p-{index}"), &[("demo::f#0", "proved", "solved")]);
        let c = h.records(&format!("c-{index}"), &[("demo::f#0", "proved", "solved")]);
        replace_package_header(&p, Some(&package));
        replace_package_header(&c, Some(&serde_json::Value::String(package.to_string())));
        h.check(&["--obligations"], &p, &c, 3);
    }
    // Missing package labels retain the historical explicit "-" identity.
    let p = h.records("p-missing", &[("demo::f#0", "proved", "solved")]);
    let c = h.records("c-dash", &[("demo::f#0", "proved", "solved")]);
    replace_package_header(&p, None);
    replace_package_header(&c, Some(&serde_json::Value::String("-".into())));
    h.check(&["--obligations"], &p, &c, 0);
}

#[test]
fn non_utf8_corpus_names_cannot_merge_required_oracle_coverage() {
    #[cfg(unix)]
    {
        use std::ffi::OsString;
        use std::os::unix::ffi::OsStringExt as _;

        let h = Harness::new();
        let p = h.side("p", &base(), Some("one"));
        h.side("p", &base(), Some("two"));
        let c = h.root.join("c");
        assert_eq!(
            super::parse::corpus_name(Path::new("one/elide-audit-input.tsv")).unwrap(),
            "one"
        );
        assert_eq!(super::parse::corpus_name(Path::new("elide-audit-input.tsv")).unwrap(), ".");
        for suffix in [0xff, 0xfe] {
            let relative =
                PathBuf::from(OsString::from_vec(vec![b'a', suffix])).join("elide-audit-input.tsv");
            let error = super::parse::corpus_name(&relative).unwrap_err();
            assert_eq!(error.kind(), std::io::ErrorKind::InvalidData);
        }
        let mut filesystem_refused_invalid_name = false;
        for (suffix, rows) in [(0xff, "rows=1"), (0xfe, "rows=0")] {
            let corpus = c.join(OsString::from_vec(vec![b'a', suffix]));
            match fs::create_dir_all(&corpus) {
                Ok(()) => {}
                Err(error)
                    if cfg!(target_os = "macos") && error.raw_os_error() == Some(libc::EILSEQ) =>
                {
                    // Darwin rejects these names before comparison can read
                    // them. The actual production conversion above must still
                    // refuse both raw components, with valid-name controls.
                    filesystem_refused_invalid_name = true;
                    break;
                }
                Err(error) => panic!("could not create corpus fixture: {error}"),
            }
            let audit = with_extra(base(), [row("PARITY", &FN, &["row", rows, "mismatches=0"])]);
            fs::write(corpus.join("elide-audit-input.tsv"), format!("{}\n", audit.join("\n")))
                .unwrap();
        }
        // Both row multisets otherwise agree. Lossy decoding would merge the
        // two candidate corpora and let the exercised one cover the idle one.
        if !filesystem_refused_invalid_name {
            h.check(&["--l4", "--oracles", "row"], &p, &c, 3);
        }
    }
}

#[test]
fn unreadable_obligation_headers_cannot_hide_one_file_of_the_population() {
    let h = Harness::new();
    let deep = format!("{}0{}", "[".repeat(160), "]".repeat(160));
    for (index, (metadata, malformed)) in [
        ("NaN".to_owned(), true),
        ("Infinity".to_owned(), true),
        ("-Infinity".to_owned(), true),
        ("1e999".to_owned(), true),
        (deep, false),
    ]
    .into_iter()
    .enumerate()
    {
        let p = h.records(&format!("p-{index}"), &[("demo::f#0", "proved", "solved")]);
        let c = h.records(&format!("c-{index}"), &[("demo::f#0", "proved", "solved")]);
        let extra = serde_json::json!({"key":"demo::extra#0", "status":"proved", "stop":"solved"});
        fs::write(p.join("extra.obligations.ndjson"), format!(
            "{{\"schema\":\"trust.obligations.v1\",\"package\":\"demo\",\"unused\":{metadata}}}\n{extra}\n"
        )).unwrap();
        let (code, out) = h.run(&["--obligations"], &p, &c);
        if malformed {
            assert_eq!(code, 3, "a non-JSON header must refuse, not disappear:\n{out}");
        } else {
            // A future deep decoder may read the entire valid header instead
            // of refusing it. In that case it must count the extra obligation.
            assert!(matches!(code, 1 | 3), "deep metadata cannot yield partial PASS:\n{out}");
            if code == 1 {
                contains(&out, "obligation moved\tdemo\tdemo::extra#0");
            }
        }
    }
}

#[test]
fn historical_newline_boundaries_cannot_be_new_identity_text() {
    let h = Harness::new();
    for (index, separator) in [
        '\r', '\u{000b}', '\u{000c}', '\u{001c}', '\u{001d}', '\u{001e}', '\u{0085}', '\u{2028}',
        '\u{2029}',
    ]
    .into_iter()
    .enumerate()
    {
        let rows = base()
            .into_iter()
            .map(|line| line.replacen("demo::f", &format!("demo::f{separator}tail"), 1))
            .collect::<Vec<_>>();
        let p = h.side(&format!("p-{index}"), &rows, None);
        let c = h.side(&format!("c-{index}"), &rows, None);
        h.check(&["--l4"], &p, &c, 3);
    }
    // Bare CR is also a legitimate historical record separator. Supporting
    // that grammar must not turn CR-separated complete files into refusals.
    let p = h.side("p-cr", &base(), None);
    let c = h.side("c-cr", &base(), None);
    for directory in [&p, &c] {
        let path = directory.join("elide-audit-1.tsv");
        let text = fs::read_to_string(&path).unwrap();
        fs::write(path, text.replace('\n', "\r")).unwrap();
    }
    h.check(&["--l4"], &p, &c, 0);
    let p = h.records("p-records-cr", &[("demo::f#0", "proved", "solved")]);
    let c = h.records("c-records-cr", &[("demo::f#0", "proved", "solved")]);
    for directory in [&p, &c] {
        let path = directory.join("demo.obligations.ndjson");
        let text = fs::read_to_string(&path).unwrap();
        fs::write(path, text.replace('\n', "\r")).unwrap();
    }
    h.check(&["--obligations"], &p, &c, 0);
    let p =
        h.side("p-attributed-cr", &with_extra(base(), [row("CAP", &CRATE, &[DELETED_SITE])]), None);
    let c = h.side("c-attributed-cr", &base(), None);
    let attributed =
        h.attribution(format!("# review\rlib\tlib\tdemo\t{DELETED_SITE}\t-\tno affected row\r"));
    h.check(
        &["--l4", "--deleted-caps", "C09d", "--attributed", attributed.to_str().unwrap()],
        &p,
        &c,
        0,
    );
}
