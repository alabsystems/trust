//! Controls for `targo trust land --check`.
//!
//! Four kinds. The conformance fixture
//! (`targo-trust/tests/fixtures/land_select_cases.json`): every expected value
//! in it is the Python reader's own answer, `scripts/tests/land_gate_test.py`
//! recomputes each one, and the tests here hold the Rust reader to the same.
//! One test per rule the table reader refuses a table by, each over the
//! fixture's base table, which loads. The verb through its own path
//! ([`run_with`]) over a checkout on disk, with a checkout and a runner that
//! answer from memory. And the real pieces: the row's process against
//! `/bin/sh`, and the change against a git repository the test makes.

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};
use std::time::Duration;

use serde::Deserialize;

use super::cli::{Host, run_with};
use super::run::{self, RowRunner, RowSpec, Verdict};
use super::select::{self, Change, Checkout, MANIFEST_ROW};
use super::table::{self, NotRunKind, TABLE, Table};
use super::{EXIT_COULD_NOT_RUN, EXIT_FAIL, EXIT_USAGE};
use crate::logged_child::ChildExit;

// --- the conformance fixture ---------------------------------------------------

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Fixture {
    schema: String,
    what: String,
    real_table: Vec<RealCase>,
    base_table: String,
    tables: Vec<TableCase>,
    coverage: Vec<CoverageCase>,
    covered_match: Vec<GlobCase>,
    covered_match_paths: Vec<String>,
    python_whitespace: Vec<u32>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct RealCase {
    name: String,
    changed: Vec<String>,
    rows: Vec<String>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct TableCase {
    name: String,
    edits: Vec<(String, String)>,
    accepted: bool,
    /// For a refused table: words of the rule it breaks, which both readers'
    /// messages hold.
    says: Option<String>,
    /// For an accepted table: changes, and the rows each selects.
    select: Option<Vec<Selection>>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Selection {
    changed: Vec<String>,
    rows: Vec<String>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct CoverageCase {
    name: String,
    tracked: Vec<String>,
    problems: Vec<String>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct GlobCase {
    pattern: String,
    matches: Vec<String>,
}

fn fixture() -> Fixture {
    let fixture: Fixture =
        serde_json::from_str(include_str!("../../tests/fixtures/land_select_cases.json"))
            .expect("the conformance fixture is the shape this test reads");
    assert_eq!(fixture.schema, "trust.land-select-cases.v1");
    assert!(fixture.what.contains("scripts/tests/land_gate_test.py"));
    fixture
}

/// `base` with each edit applied. An edit names text that is there exactly
/// once, so a case cannot stop changing the table unnoticed.
fn edited<S: AsRef<str>>(base: &str, edits: &[(S, S)]) -> String {
    let mut text = base.to_owned();
    for (old, new) in edits {
        let (old, new) = (old.as_ref(), new.as_ref());
        assert_eq!(text.matches(old).count(), 1, "the edit's text is not there once: {old:?}");
        text = text.replace(old, new);
    }
    text
}

fn ids(selected: &BTreeSet<String>) -> Vec<&str> {
    selected.iter().map(String::as_str).collect()
}

fn owned(paths: &[&str]) -> Vec<String> {
    paths.iter().map(|path| (*path).to_owned()).collect()
}

/// This checkout, from the package directory Cargo compiled this test in.
fn checkout() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("targo-trust is in a checkout")
        .to_path_buf()
}

#[test]
fn the_fixtures_changes_select_the_rows_the_python_selector_selects() {
    let fixture = fixture();
    // The table is compiled into this test, so a change to it is a change to
    // this test's inputs whoever selects tests by what they read; and it is
    // the file the verb loads from this checkout.
    let table = table::parse(include_str!("../../../gates/land.toml")).unwrap();
    assert_eq!(table::load(&checkout()).unwrap(), table);
    for case in &fixture.real_table {
        let selected = select::selected(&table, &case.changed);
        assert_eq!(ids(&selected), case.rows, "{}: {:?}", case.name, case.changed);
    }
    // The kinds of change the port's review asked for are all here, and the
    // instrument: the cases do not all select nothing, and the two files both
    // readers' tests read select the Python test that reads them.
    let rows = |name: &str| -> Vec<&str> {
        let case = fixture.real_table.iter().find(|case| case.name == name);
        let case = case.unwrap_or_else(|| panic!("the fixture has no case named {name:?}"));
        case.rows.iter().map(String::as_str).collect()
    };
    assert!(rows("an empty change").is_empty());
    assert!(rows("an exact subject path (additive)").len() > 1);
    assert!(rows("a validation program").len() > 1);
    assert!(rows("the table itself").contains(&"validation.land_gate_test"));
    assert_eq!(rows("this fixture"), ["validation.land_gate_test"]);
    assert!(rows("an unmapped path").is_empty());
    assert!(rows("a docs-only change that no row names").is_empty());
    assert_eq!(rows("a module's own file under scripts/tests").len(), 1);
    assert_eq!(rows("a Cargo.toml in another letter case"), [MANIFEST_ROW]);
    assert!(rows("names that only resemble Cargo.toml").is_empty());
}

#[test]
fn the_fixtures_tables_are_accepted_and_refused_as_the_python_reader_does() {
    let fixture = fixture();
    let (mut accepted, mut refused) = (0, 0);
    for case in &fixture.tables {
        let text = edited(&fixture.base_table, &case.edits);
        match (table::parse(&text), case.accepted) {
            (Ok(table), true) => {
                accepted += 1;
                let select = case.select.as_ref().expect("an accepted case says what selects");
                for selection in select {
                    let selected = select::selected(&table, &selection.changed);
                    assert_eq!(
                        ids(&selected),
                        selection.rows,
                        "{}: {:?}",
                        case.name,
                        selection.changed
                    );
                }
            }
            (Err(error), false) => {
                refused += 1;
                let says = case.says.as_ref().expect("a refused case names its rule");
                assert!(error.contains(says.as_str()), "{}: {error:?} lacks {says:?}", case.name);
            }
            (Ok(_), false) => panic!("{}: the Python reader refuses it; this one loads", case.name),
            (Err(error), true) => {
                panic!("{}: the Python reader loads it; this one says {error}", case.name)
            }
        }
    }
    assert!(accepted >= 10 && refused >= 50, "{accepted} accepted, {refused} refused");
}

#[test]
fn the_fixtures_coverage_problems_are_the_python_readers_word_for_word() {
    let fixture = fixture();
    let table = table::parse(&fixture.base_table).unwrap();
    for case in &fixture.coverage {
        let tracked: BTreeSet<String> = case.tracked.iter().cloned().collect();
        assert_eq!(table.coverage(&tracked), case.problems, "{}", case.name);
    }
    assert!(fixture.coverage.iter().any(|case| case.problems.is_empty()));
    assert!(fixture.coverage.iter().any(|case| case.problems.len() > 2));
}

#[test]
fn the_fixtures_covered_globs_match_as_pythons_fnmatch_does() {
    let fixture = fixture();
    let mut matched = 0;
    for case in &fixture.covered_match {
        for path in &fixture.covered_match_paths {
            let expected = case.matches.contains(path);
            matched += usize::from(expected);
            assert_eq!(
                table::covered_match(path, &case.pattern),
                expected,
                "glob {:?} over {path:?}",
                case.pattern
            );
        }
    }
    assert!(matched > 50 && fixture.covered_match.len() > 40, "{matched} matches");
    // The instrument: the fixture holds the classes whose negation is decided
    // by what a reversed range leaves behind, and they are not all one answer.
    let matches = |pattern: &str| -> Vec<&str> {
        let case = fixture.covered_match.iter().find(|case| case.pattern == pattern);
        let case = case.unwrap_or_else(|| panic!("the fixture has no glob {pattern:?}"));
        case.matches.iter().map(String::as_str).collect()
    };
    let one_character: Vec<&str> = fixture
        .covered_match_paths
        .iter()
        .map(String::as_str)
        .filter(|path| path.chars().count() == 1)
        .collect();
    assert!(one_character.contains(&"q") && one_character.contains(&"x"));
    assert_eq!(matches("[z-a!]"), one_character, "a class left as `!` is any one character");
    assert_eq!(matches("[!b-a]"), one_character);
    let but = |left_out: &[&str]| -> Vec<&str> {
        one_character.iter().copied().filter(|path| !left_out.contains(path)).collect()
    };
    assert_eq!(matches("[b-a!x]"), but(&["x"]), "what is left opens with `!`: negated");
    assert_eq!(matches("[b-a!-z]"), but(&["-", "z"]));
    assert_eq!(matches("[b-a^x]"), ["^", "x"], "only `!` negates");
    assert_eq!(matches("[b-a]"), Vec::<&str>::new(), "nothing left matches nothing");
}

#[test]
fn a_class_is_negated_by_what_its_reversed_ranges_leave() {
    let covered = |pattern: &str, name: &str| {
        table::covered_match(&format!("scripts/tests/{name}_test.py"), pattern)
    };
    // The control: a class written negated, and one written plain.
    assert!(covered("scripts/tests/[!x]_test.py", "q"));
    assert!(!covered("scripts/tests/[!x]_test.py", "x"));
    assert!(covered("scripts/tests/[x]_test.py", "x"));
    // `b-a` is dropped with both its ends, and `!x` is what is left.
    assert!(covered("scripts/tests/[b-a!x]_test.py", "q"));
    assert!(covered("scripts/tests/[b-a!x]_test.py", "!"));
    assert!(!covered("scripts/tests/[b-a!x]_test.py", "x"));
    // `!` alone is left: any one character, and exactly one.
    assert!(covered("scripts/tests/[z-a!]_test.py", "q"));
    assert!(!covered("scripts/tests/[z-a!]_test.py", ""));
    assert!(!covered("scripts/tests/[z-a!]_test.py", "qq"));
    // A range after that `!` still holds: `c` to `e`, negated.
    assert!(covered("scripts/tests/[b-a!c-e]_test.py", "q"));
    assert!(!covered("scripts/tests/[b-a!c-e]_test.py", "d"));
    // `!-z` is left, and a hyphen that opens a class is a hyphen.
    assert!(covered("scripts/tests/[b-a!-z]_test.py", "q"));
    assert!(!covered("scripts/tests/[b-a!-z]_test.py", "-"));
    assert!(!covered("scripts/tests/[b-a!-z]_test.py", "z"));
    // A range in order is untouched, so its `!` is a character of the class.
    assert!(covered("scripts/tests/[a-b!x]_test.py", "!"));
    assert!(!covered("scripts/tests/[a-b!x]_test.py", "q"));
}

#[test]
fn a_blank_text_is_what_pythons_strip_empties() {
    let fixture = fixture();
    let python: BTreeSet<u32> = fixture.python_whitespace.iter().copied().collect();
    assert!(python.contains(&0x1f) && python.contains(&0x3000) && !python.contains(&0x200b));
    for code in 0..=0x0010_ffff_u32 {
        let Some(c) = char::from_u32(code) else { continue };
        assert_eq!(table::python_space(c), python.contains(&code), "U+{code:04X}");
    }
    assert!(table::blank("") && table::blank(" \t\u{1f}\u{a0}") && !table::blank(" x "));
}

#[test]
fn a_manifest_is_cargo_toml_in_either_letter_case_and_nothing_else() {
    for path in ["Cargo.toml", "a/b/Cargo.toml", "CARGO.TOML", "a/cargo.Toml"] {
        assert!(select::names_a_manifest(path), "{path}");
    }
    for path in ["a/Cargo.toml.orig", "a/Cargo.toml/b", "a/xCargo.toml", "Cargo.lock", ""] {
        assert!(!select::names_a_manifest(path), "{path}");
    }
    // KELVIN SIGN folds to `k`, which is no letter of the name.
    assert!(!select::names_a_manifest("a/\u{212a}argo.toml"));
}

#[test]
fn the_checked_in_table_loads_and_covers_this_checkouts_test_modules() {
    let root = checkout();
    let table = table::load(&root).unwrap();
    assert!(table.rows.len() > 150, "{} rows", table.rows.len());
    assert_eq!(table.covered, ["scripts/tests/*_test.py"]);
    // Rule 1 of the design's section 5 is not met by any row yet, and each
    // says why.
    assert!(table.rows.iter().all(|row| !row.is_targo() && !table::blank(&row.not_yet_targo)));
    for kind in NotRunKind::ALL {
        assert!(table.not_run.iter().any(|entry| entry.kind == kind), "{}", kind.word());
    }
    // The `covered` rule, over the files that are there (the verb asks git
    // for the tracked ones; scripts/tests/land_gate_test.py holds the tree to
    // the same rule through the Python reader).
    let mut present = BTreeSet::new();
    for entry in fs::read_dir(root.join("scripts/tests")).unwrap() {
        let entry = entry.unwrap();
        if entry.file_type().unwrap().is_file() {
            present.insert(format!("scripts/tests/{}", entry.file_name().to_str().unwrap()));
        }
    }
    assert_eq!(table.coverage(&present), Vec::<String>::new());
    // The instrument: the rule sees a module with no entry, and an entry with
    // no file.
    let stray = "scripts/tests/zz_no_such_module_test.py".to_owned();
    present.insert(stray.clone());
    assert_eq!(table.coverage(&present), [format!("{stray}: neither a [[row]] nor a [[not_run]]")]);
    present.remove(&stray);
    let gone = table.rows[0].file.clone();
    present.remove(&gone);
    assert_eq!(
        table.coverage(&present),
        [format!("[[row]] {}: {gone} is not a tracked file", table.rows[0].id)]
    );
}

#[test]
fn a_lean_only_change_selects_only_the_row_that_names_the_lean_file() {
    // R2: the base table's beta row names a .lean file and its alpha row a
    // .rs file. Path selection cannot see a `clean { }` island inside a .rs
    // file; that needs the per-declaration delta (PKG-LIVE-2).
    let table = table::parse(&fixture().base_table).unwrap();
    let select = |paths: &[&str]| -> Vec<String> {
        select::selected(&table, &owned(paths)).into_iter().collect()
    };
    assert_eq!(select(&["proofs/Beta.lean"]), ["validation.beta_test"]);
    assert_eq!(select(&["src/alpha.rs"]), ["validation.alpha_test"]);
    assert_eq!(
        select(&["proofs/Beta.lean", "src/alpha.rs"]),
        ["validation.alpha_test", "validation.beta_test"]
    );
    assert!(select(&["proofs/Other.lean"]).is_empty());
}

/// The table the verb's tests run over is the fixture's base table: two rows,
/// neither a targo command, and one `[[not_run]]` of each kind.
#[test]
fn the_base_table_is_what_the_verbs_tests_count() {
    let table: Table = table::parse(&fixture().base_table).unwrap();
    assert_eq!(table.rows.len(), 2);
    assert!(table.rows.iter().all(|row| !row.is_targo()));
    let kinds: Vec<NotRunKind> = table.not_run.iter().map(|entry| entry.kind).collect();
    assert_eq!(kinds, [NotRunKind::Unjudgeable, NotRunKind::Red]);
    let files: Vec<&str> = table
        .rows
        .iter()
        .map(|row| row.file.as_str())
        .chain(table.not_run.iter().map(|entry| entry.path.as_str()))
        .collect();
    assert_eq!(files, MODULES);
    assert!(!table.rows[0].catches.is_empty() && table.row("validation.zz").is_none());
}

// --- one test per rule the reader refuses a table by ----------------------------

/// The fixture's base table with `edits` applied is refused, and the refusal
/// says `needle`. The control: the base table, without the defect, loads.
fn refused(edits: &[(&str, &str)], needle: &str) {
    let base = fixture().base_table;
    let loaded = table::parse(&base).expect("the base table loads");
    assert_eq!((loaded.rows.len(), loaded.not_run.len(), loaded.programs.len()), (2, 2, 2));
    let text = edited(&base, edits);
    match table::parse(&text) {
        Ok(_) => panic!("the table loads with the defect: {edits:?}"),
        Err(error) => assert!(error.contains(needle), "{error:?} lacks {needle:?}"),
    }
}

const SCHEMA_LINE: &str = "schema = \"trust.land-rows.v1\"";
const COVERED: &str = "covered = [\"scripts/tests/*_test.py\"]";
const ALPHA_ID: &str = "id = \"validation.alpha_test\"";
const BETA_ID: &str = "id = \"validation.beta_test\"";
const ALPHA_COMMAND: &str = "command = [\"python3\", \"-B\", \"scripts/land_gate.py\", \
     \"validation-tests\", \"scripts.tests.alpha_test\"]";
const ALPHA_SELECTS: &str =
    "selects_on = [\"scripts/alpha.py\", \"scripts/tests/alpha_test.py\", \"src/alpha.rs\"]";
const ALPHA_CATCHES: &str = "catches = \"alpha's defect\"";
const ALPHA_NOT_YET: &str = "not_yet_targo = \"alpha is a Python unittest\"";
const GAMMA_ID: &str = "id = \"validation.gamma_test\"";
const GAMMA_PATH: &str = "path = \"scripts/tests/gamma_test.py\"";
const GAMMA_KIND: &str = "kind = \"red\"";
const GAMMA_WHY: &str = "why = \"gamma: 1 FAIL\"";
const DELTA_ID: &str = "id = \"validation.delta_test\"";
const DELTA_PATH: &str = "path = \"scripts/tests/delta_test.py\"";
const ALPHA_PROGRAM: &str = "\"scripts/alpha.py\" = [\"validation.beta_test\", \
     \"validation.alpha_test\"]";
const ALPHA_FILE_PROGRAM: &str = "\"scripts/tests/alpha_test.py\" = [\"validation.alpha_test\"]";

macro_rules! refuses {
    ($($(#[$note:meta])* $name:ident: $needle:literal, [$(($old:expr, $new:expr)),+ $(,)?];)+) => {
        $(
            $(#[$note])*
            #[test]
            fn $name() {
                refused(&[$(($old, $new)),+], $needle);
            }
        )+
    };
}

refuses! {
    a_table_that_is_not_toml_is_refused: "not TOML",
        [(GAMMA_WHY, "why = \"gamma: 1 FAIL\"\n[[row")];
    /// `tomllib` refuses a byte-order mark; the `toml` crate alone would not.
    a_table_that_opens_with_a_byte_order_mark_is_refused: "not TOML",
        [(SCHEMA_LINE, "\u{feff}schema = \"trust.land-rows.v1\"")];
    another_schema_is_refused: "schema is", [(SCHEMA_LINE, "schema = \"trust.land-rows.v2\"")];
    an_unknown_key_at_the_top_is_refused: "the table: unknown key",
        [(COVERED, "owner = \"x\"\ncovered = [\"scripts/tests/*_test.py\"]")];
    a_missing_key_at_the_top_is_refused: "the table: missing key", [(SCHEMA_LINE, "")];
    a_mistyped_key_at_the_top_is_refused: "covered is not an array",
        [(COVERED, "covered = \"scripts/tests/*_test.py\"")];
    nothing_covered_is_refused: "covered: empty", [(COVERED, "covered = []")];
    a_blank_covered_glob_is_refused: "is not a non-empty string",
        [(COVERED, "covered = [\"\\u001F\", \"scripts/tests/*_test.py\"]")];
    a_covered_glob_listed_twice_is_refused: "is listed twice",
        [(COVERED, "covered = [\"scripts/tests/*_test.py\", \"scripts/tests/*_test.py\"]")];
    covered_globs_out_of_order_are_refused: "covered: not sorted",
        [(COVERED, "covered = [\"scripts/tests/*_test.sh\", \"scripts/tests/*_test.py\"]")];

    /// `inputs` was the design's first name for `selects_on`.
    an_unknown_key_in_a_row_is_refused: "[[row]] validation.alpha_test: unknown key",
        [(ALPHA_CATCHES, "catches = \"alpha's defect\"\ninputs = [\"scripts/alpha.py\"]")];
    a_missing_key_in_a_row_is_refused: "[[row]] validation.alpha_test: missing key",
        [(ALPHA_CATCHES, "")];
    a_mistyped_key_in_a_row_is_refused: "catches is not a string",
        [(ALPHA_CATCHES, "catches = 7")];
    a_row_without_a_string_id_is_refused: "[[row]] #1: no string id", [(ALPHA_ID, "id = 7")];
    a_row_id_of_another_kind_is_refused: "the id is not validation.<module>",
        [(ALPHA_ID, "id = \"push.alpha_test\"")];
    a_row_id_declared_twice_is_refused: "[[row]] validation.alpha_test: duplicate id",
        [(BETA_ID, ALPHA_ID)];
    row_ids_out_of_order_are_refused: "ids are not sorted (it follows validation.calpha_test)",
        [(ALPHA_ID, "id = \"validation.calpha_test\""),
         (ALPHA_COMMAND, "command = [\"python3\", \"-B\", \"scripts/land_gate.py\", \
          \"validation-tests\", \"scripts.tests.calpha_test\"]")];
    a_command_that_is_not_the_rows_runner_is_refused:
        "command is not this row's validation runner",
        [(ALPHA_COMMAND, "command = [\"python3\", \"-m\", \"unittest\", \
          \"scripts.tests.alpha_test\"]")];
    another_modules_runner_is_refused: "command is not this row's validation runner",
        [(ALPHA_COMMAND, "command = [\"python3\", \"-B\", \"scripts/land_gate.py\", \
          \"validation-tests\", \"scripts.tests.beta_test\"] ")];
    /// No row is a targo verb or a test target yet, and the Python reader
    /// refuses any command but the validation runner: so does this one, or
    /// the two would disagree about a table.
    a_targo_command_is_refused_until_both_readers_know_one:
        "command is not this row's validation runner",
        [(ALPHA_COMMAND, "command = [\"targo\", \"--unverified\", \"test\", \"-p\", \"alpha\"]")];
    a_row_no_path_selects_is_refused: "empty selects_on", [(ALPHA_SELECTS, "selects_on = []")];
    selecting_paths_out_of_order_are_refused: "selects_on: not sorted",
        [(ALPHA_SELECTS, "selects_on = [\"scripts/tests/alpha_test.py\", \"scripts/alpha.py\", \
          \"src/alpha.rs\"]")];
    a_selecting_path_listed_twice_is_refused: "is listed twice",
        [(ALPHA_SELECTS, "selects_on = [\"scripts/alpha.py\", \"scripts/alpha.py\", \
          \"scripts/tests/alpha_test.py\", \"src/alpha.rs\"]")];
    an_empty_selecting_path_is_refused: "is not a non-empty string",
        [(ALPHA_SELECTS, "selects_on = [\"\", \"scripts/alpha.py\", \
          \"scripts/tests/alpha_test.py\", \"src/alpha.rs\"]")];
    a_row_that_names_no_defect_is_refused: "empty catches",
        [(ALPHA_CATCHES, "catches = \" \\t\"")];
    /// The design's section 5, rule 1: a command that does not start `targo`
    /// says why it is not yet a targo verb or a test target.
    a_row_that_is_not_targo_must_carry_not_yet_targo: "missing key \"not_yet_targo\"",
        [(ALPHA_NOT_YET, "")];
    a_row_whose_not_yet_targo_says_nothing_is_refused: "empty not_yet_targo",
        [(ALPHA_NOT_YET, "not_yet_targo = \"\"")];

    an_unknown_key_in_a_not_run_is_refused: "[[not_run]] validation.gamma_test: unknown key",
        [(GAMMA_KIND, "kind = \"red\"\nseconds = 900")];
    a_missing_key_in_a_not_run_is_refused: "[[not_run]] validation.gamma_test: missing key",
        [(GAMMA_KIND, "")];
    a_module_that_is_a_row_and_a_not_run_is_refused: "also a [[row]]",
        [(GAMMA_ID, BETA_ID),
         (GAMMA_PATH, "path = \"scripts/tests/beta_test.py\""),
         (DELTA_ID, "id = \"validation.aaa_test\""),
         (DELTA_PATH, "path = \"scripts/tests/aaa_test.py\"")];
    a_not_run_path_that_is_not_its_modules_file_is_refused: "path is",
        [(GAMMA_PATH, "path = \"scripts/tests/other_test.py\"")];
    a_not_run_of_an_unknown_kind_is_refused: "kind is", [(GAMMA_KIND, "kind = \"slow\"")];
    a_not_run_without_a_reason_is_refused: "empty why", [(GAMMA_WHY, "why = \"\"")];
    a_not_run_id_declared_twice_is_refused: "[[not_run]] validation.gamma_test: duplicate id",
        [(DELTA_ID, GAMMA_ID), (DELTA_PATH, GAMMA_PATH)];
    not_run_ids_out_of_order_are_refused: "ids are not sorted (it follows validation.zeta_test)",
        [(DELTA_ID, "id = \"validation.zeta_test\""),
         (DELTA_PATH, "path = \"scripts/tests/zeta_test.py\"")];

    a_program_that_is_not_an_array_is_refused: "not an array of row ids",
        [(ALPHA_PROGRAM, "\"scripts/alpha.py\" = \"validation.alpha_test\"")];
    a_program_without_rows_is_refused: ": empty", [(ALPHA_PROGRAM, "\"scripts/alpha.py\" = []")];
    a_program_row_listed_twice_is_refused: "is listed twice",
        [(ALPHA_PROGRAM, "\"scripts/alpha.py\" = [\"validation.beta_test\", \
          \"validation.alpha_test\", \"validation.beta_test\"]")];
    a_program_row_that_is_no_row_is_refused: "validation.omega_test is not a [[row]]",
        [(ALPHA_FILE_PROGRAM, "\"scripts/tests/alpha_test.py\" = [\"validation.omega_test\"]")];
    a_program_short_of_the_rows_that_name_it_is_refused:
        "its rows are not exactly the rows whose selects_on names the path",
        [(ALPHA_PROGRAM, "\"scripts/alpha.py\" = [\"validation.alpha_test\"]")];
    a_program_beyond_the_rows_that_name_it_is_refused:
        "its rows are not exactly the rows whose selects_on names the path",
        [(ALPHA_FILE_PROGRAM, "\"scripts/tests/alpha_test.py\" = [\"validation.alpha_test\", \
          \"validation.beta_test\"]")];
    a_program_no_row_names_is_refused:
        "its rows are not exactly the rows whose selects_on names the path",
        [(ALPHA_FILE_PROGRAM, "\"scripts/tests/alpha_test.py\" = [\"validation.alpha_test\"]\n\
          \"scripts/other.py\" = [\"validation.alpha_test\"]")];
}

// --- the table's file ----------------------------------------------------------

/// A checkout on disk with a row table.
struct World {
    root: tempfile::TempDir,
}

impl World {
    fn new() -> Self {
        Self::with_table(&fixture().base_table)
    }

    fn with_table(table: &str) -> Self {
        let world = Self { root: tempfile::tempdir().unwrap() };
        world.write(TABLE, table);
        world
    }

    /// The checkout's root, resolved: what the verb hands its runner.
    fn root(&self) -> PathBuf {
        fs::canonicalize(self.root.path()).unwrap()
    }

    fn path(&self, relative: &str) -> PathBuf {
        self.root.path().join(relative)
    }

    fn write(&self, relative: &str, text: &str) {
        let path = self.path(relative);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, text).unwrap();
    }
}

#[cfg(unix)]
#[test]
fn the_table_is_read_only_from_a_regular_file_in_a_real_directory() {
    use std::os::unix::fs::symlink;

    let base = fixture().base_table;
    let world = World::new();
    // The control: the same bytes load from a regular file.
    assert_eq!(table::load(world.root.path()).unwrap(), table::parse(&base).unwrap());

    // A link at the file's name.
    world.write("elsewhere/rows.toml", &base);
    fs::remove_file(world.path(TABLE)).unwrap();
    symlink("../elsewhere/rows.toml", world.path(TABLE)).unwrap();
    assert_eq!(fs::read_to_string(world.path(TABLE)).unwrap(), base, "the link resolves");
    let error = table::load(world.root.path()).unwrap_err();
    assert!(error.contains("gates/land.toml is a symbolic link"), "{error}");

    // A link at the directory's name.
    fs::remove_file(world.path(TABLE)).unwrap();
    fs::remove_dir(world.path("gates")).unwrap();
    world.write("elsewhere/land.toml", &base);
    symlink("elsewhere", world.path("gates")).unwrap();
    assert_eq!(fs::read_to_string(world.path(TABLE)).unwrap(), base, "the link resolves");
    let error = table::load(world.root.path()).unwrap_err();
    assert!(error.contains("gates is a symbolic link"), "{error}");

    // A directory at the file's name, and a file at the directory's.
    fs::remove_file(world.path("gates")).unwrap();
    fs::create_dir_all(world.path(TABLE)).unwrap();
    let error = table::load(world.root.path()).unwrap_err();
    assert!(error.contains("gates/land.toml is not a regular file"), "{error}");
    fs::remove_dir(world.path(TABLE)).unwrap();
    fs::remove_dir(world.path("gates")).unwrap();
    fs::write(world.path("gates"), &base).unwrap();
    let error = table::load(world.root.path()).unwrap_err();
    assert!(error.contains("gates is not a directory"), "{error}");

    // The control again, in the same directory.
    fs::remove_file(world.path("gates")).unwrap();
    world.write(TABLE, &base);
    assert!(table::load(world.root.path()).is_ok());
}

#[test]
fn a_table_that_is_missing_or_not_utf8_is_refused() {
    let world = World::new();
    assert!(table::load(world.root.path()).is_ok());
    fs::write(world.path(TABLE), b"\xff\xfe").unwrap();
    let error = table::load(world.root.path()).unwrap_err();
    assert!(error.contains("cannot read gates/land.toml") && error.contains("UTF-8"), "{error}");
    fs::remove_file(world.path(TABLE)).unwrap();
    let error = table::load(world.root.path()).unwrap_err();
    assert!(error.contains("cannot read gates/land.toml"), "{error}");
    fs::remove_dir(world.path("gates")).unwrap();
    let error = table::load(world.root.path()).unwrap_err();
    assert!(error.contains("cannot read gates under"), "{error}");
}

// --- the verb ------------------------------------------------------------------

const BASE_COMMIT: &str = "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb";
const MERGE_BASE: &str = "cccccccccccccccccccccccccccccccccccccccc";
const HEAD: &str = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
/// The files of the base table's two rows and two `[[not_run]]` entries.
const MODULES: [&str; 4] = [
    "scripts/tests/alpha_test.py",
    "scripts/tests/beta_test.py",
    "scripts/tests/delta_test.py",
    "scripts/tests/gamma_test.py",
];
const ALPHA: &str = "validation.alpha_test";
const BETA: &str = "validation.beta_test";
const FOOTER: &str = "validation rows only; this is not the landing gate";

/// A row's line of the report: its verdict's word, then the rest.
fn row_line(word: &str, rest: &str) -> String {
    format!("{word:<11} {rest}")
}

/// Stands in for git: answers from memory and records what it was asked.
struct FakeCheckout {
    tracked: Result<Vec<String>, String>,
    committed: Vec<String>,
    working: Vec<String>,
    /// Bases that do not resolve.
    unresolved: Vec<String>,
    asked: Vec<String>,
}

impl FakeCheckout {
    fn changing(committed: &[&str], working: &[&str]) -> Self {
        Self {
            tracked: Ok(owned(&MODULES)),
            committed: owned(committed),
            working: owned(working),
            unresolved: Vec::new(),
            asked: Vec::new(),
        }
    }
}

impl Checkout for FakeCheckout {
    fn tracked(&mut self, _root: &Path) -> Result<BTreeSet<String>, String> {
        self.tracked.clone().map(|paths| paths.into_iter().collect())
    }

    fn change(&mut self, _root: &Path, base: &str) -> Result<Change, String> {
        self.asked.push(base.to_owned());
        if self.unresolved.iter().any(|unresolved| unresolved == base) {
            return Err(format!("the base {base:?} does not resolve to a commit"));
        }
        Ok(Change {
            base: BASE_COMMIT.into(),
            merge_base: MERGE_BASE.into(),
            head: HEAD.into(),
            committed: self.committed.iter().cloned().collect(),
            working: self.working.iter().cloned().collect(),
        })
    }
}

/// Stands in for a row's process: says how the command ended, by row id.
#[derive(Default)]
struct FakeRunner {
    exits: BTreeMap<String, ChildExit>,
    specs: Vec<RowSpec>,
}

impl FakeRunner {
    fn ending(exits: &[(&str, ChildExit)]) -> Self {
        Self {
            exits: exits.iter().map(|(id, exit)| ((*id).to_owned(), exit.clone())).collect(),
            specs: Vec::new(),
        }
    }
}

impl RowRunner for FakeRunner {
    fn run(&mut self, spec: &RowSpec) -> ChildExit {
        self.specs.push(spec.clone());
        self.exits.get(&spec.id).cloned().unwrap_or(ChildExit::Exited(0))
    }
}

struct Run {
    code: u8,
    text: String,
    specs: Vec<RowSpec>,
    asked: Vec<String>,
    progress: Vec<String>,
}

impl Run {
    fn has_line(&self, line: &str) -> bool {
        self.text.lines().any(|candidate| candidate == line)
    }

    fn line_starting(&self, start: &str) -> &str {
        self.text
            .lines()
            .find(|line| line.starts_with(start))
            .unwrap_or_else(|| panic!("no line starts {start:?} in:\n{}", self.text))
    }

    /// The directory the run's logs were in.
    fn logs(&self) -> &Path {
        self.specs[0].log.parent().unwrap()
    }
}

/// Run the verb with exactly `args`, from `cwd`.
fn land_from(
    cwd: &Path,
    args: &[&str],
    checkout: &mut FakeCheckout,
    runner: &mut FakeRunner,
) -> Run {
    let args = owned(args);
    let mut lines = Vec::new();
    let mut progress = |line: &str| lines.push(line.to_owned());
    let (code, text) = run_with(
        &args,
        &mut Host { cwd: cwd.to_path_buf(), checkout, runner, progress: &mut progress },
    );
    Run {
        code,
        text,
        specs: std::mem::take(&mut runner.specs),
        asked: std::mem::take(&mut checkout.asked),
        progress: lines,
    }
}

fn land(world: &World, args: &[&str], checkout: &mut FakeCheckout, runner: &mut FakeRunner) -> Run {
    land_from(world.root.path(), args, checkout, runner)
}

/// `--check` over the base table, for a change to `committed`.
fn check(committed: &[&str], exits: &[(&str, ChildExit)]) -> Run {
    land(
        &World::new(),
        &["--check"],
        &mut FakeCheckout::changing(committed, &[]),
        &mut FakeRunner::ending(exits),
    )
}

/// What a run prints when it stops before a table has loaded: it has no rows
/// to count, and it still ends by saying what the verb is.
fn assert_says_it_is_not_the_gate_and_counts_nothing(run: &Run) {
    assert_eq!(run.text.lines().last(), Some(FOOTER), "{}", run.text);
    assert!(run.text.ends_with(&format!("\n{FOOTER}\n")), "{}", run.text);
    assert!(!run.text.contains("rows are not yet a targo verb"), "{}", run.text);
    assert!(!run.text.contains("[[not_run]] row(s)"), "{}", run.text);
}

/// What every run of a loaded table prints, whatever its exit.
fn assert_says_what_it_is(run: &Run) {
    assert!(run.has_line("2 of 2 rows are not yet a targo verb or test target"), "{}", run.text);
    assert!(run.has_line("not run: 2 [[not_run]] row(s): 1 red, 1 unjudgeable"), "{}", run.text);
    assert!(run.line_starting("not judged here: ").contains("owner refresh"));
    assert!(run.line_starting("not judged here: ").contains("scripts/lib/land_development.py"));
    assert_eq!(run.text.lines().last(), Some(FOOTER), "{}", run.text);
}

#[test]
fn every_selected_row_runs_and_has_one_verdict() {
    let world = World::new();
    let mut checkout = FakeCheckout::changing(&["scripts/alpha.py", "docs/x.md"], &["notes.txt"]);
    let run = land(&world, &["--check"], &mut checkout, &mut FakeRunner::default());
    assert_eq!(run.code, 0, "{}", run.text);
    assert!(run.has_line(
        "land --check: base origin/main (bbbbbbbbbbbb), merge base cccccccccccc, HEAD \
         aaaaaaaaaaaa"
    ));
    assert!(run.has_line(
        "changed: 3 path(s) (2 between the merge base and HEAD, 1 staged, changed in the \
         working tree or untracked)"
    ));
    assert!(run.has_line("selected: 2 of 2 rows"));
    assert!(run.has_line(&row_line("PASS", ALPHA)));
    assert!(run.has_line(&row_line("PASS", BETA)));
    assert!(run.has_line("land --check: 2 PASS, 0 FAIL, 0 NOT JUDGED of 2 selected row(s)"));
    assert_says_what_it_is(&run);
    assert_eq!(run.asked, ["origin/main"], "the default base");

    // Each row ran once: its argv from the table, from the checkout's root,
    // for the default bound, its log named by its id.
    let ran: Vec<&str> = run.specs.iter().map(|spec| spec.id.as_str()).collect();
    assert_eq!(ran, [ALPHA, BETA]);
    let spec = &run.specs[0];
    assert_eq!(
        spec.argv,
        ["python3", "-B", "scripts/land_gate.py", "validation-tests", "scripts.tests.alpha_test"]
    );
    assert_eq!(spec.root, world.root());
    assert_eq!(spec.bound, Duration::from_secs(900));
    assert_eq!(spec.log.file_name().unwrap(), "validation.alpha_test.log");
    assert_eq!(run.specs[1].log.parent(), spec.log.parent());
    assert!(!spec.log.starts_with(world.root()), "a log is never written into the checkout");
    assert_eq!(run.progress.len(), 2);
    assert!(run.progress[0].starts_with("land --check: validation.alpha_test (1 of 2), at most"));
    // Every row passed, so nothing names a log and none is left behind.
    assert!(!run.logs().exists());
}

#[test]
fn a_path_in_the_working_tree_selects_as_a_committed_one_does() {
    let world = World::new();
    let mut checkout = FakeCheckout::changing(&[], &["x.py"]);
    let run = land(&world, &["--check"], &mut checkout, &mut FakeRunner::default());
    assert_eq!(run.code, 0, "{}", run.text);
    assert!(run.has_line("selected: 1 of 2 rows"));
    assert!(run.has_line(&row_line("PASS", BETA)));
}

#[test]
fn land_without_check_exits_2_and_says_the_landing_is_not_in_targo() {
    let world = World::new();
    for args in [&[][..], &["--base", "HEAD~1"], &["--row-seconds", "5"]] {
        let mut checkout = FakeCheckout::changing(&["scripts/alpha.py"], &[]);
        let run = land(&world, args, &mut checkout, &mut FakeRunner::default());
        assert_eq!(run.code, EXIT_USAGE, "{args:?}");
        assert!(
            run.text.starts_with("targo trust land: the landing is not implemented in Targo yet"),
            "{}",
            run.text
        );
        assert!(run.text.contains("python3 scripts/land_gate.py run"));
        assert!(run.text.contains("Usage: targo trust land --check"));
        assert!(run.text.contains(FOOTER), "the usage says what the verb is");
        assert!(run.specs.is_empty() && run.asked.is_empty(), "nothing ran");
    }
}

#[test]
fn help_is_the_usage_and_the_usage_says_what_every_run_prints() {
    let world = World::new();
    for flag in ["--help", "-h"] {
        let mut checkout = FakeCheckout::changing(&[], &[]);
        let run = land(&world, &[flag], &mut checkout, &mut FakeRunner::default());
        assert_eq!(run.code, 0);
        assert!(run.text.starts_with("Usage: targo trust land --check [--base REV]"));
        let flat = run.text.split_whitespace().collect::<Vec<_>>().join(" ");
        for said in [
            "\"N of M rows are not yet a targo verb or test target\"",
            "the count of [[not_run]] rows by kind",
            "\"validation rows only; this is not the landing gate\"",
            "the base and how many paths changed",
            "each selected row and its verdict",
            "is not implemented in Targo yet",
            "default: origin/main",
            "default 900",
            "2 outranks 3, and 3 outranks 1",
            "No gate calls this verb yet",
            "Every --check run ends with",
            "one a signal stops ends with that signal's COULD NOT RUN line",
            "marked assume-unchanged or skip-worktree",
            "an N past the end of the clock is no bound",
        ] {
            assert!(flat.contains(said), "the usage lacks {said:?}");
        }
    }
}

#[test]
fn targo_trust_help_lists_the_verb_and_says_it_is_not_the_gate() {
    let line = super::USAGE_LINE;
    let help = crate::cli::usage_text();
    assert_eq!(help.lines().filter(|listed| *listed == line).count(), 1, "{help}");
    assert!(line.starts_with(&format!("  targo trust {} --check ", super::SUBCOMMAND)), "{line}");
    assert!(line.ends_with("validation rows only, not the landing gate"), "{line}");
    assert!(!line.contains('\n'));
}

#[test]
fn arguments_are_named_and_each_is_given_once() {
    let world = World::new();
    for (args, error) in [
        (&["--check", "--bogus"][..], "unknown argument \"--bogus\""),
        (&["--check", "HEAD~1"], "unknown argument \"HEAD~1\""),
        (&["--check", "--check"], "--check is given twice"),
        (&["--check=yes"], "--check takes no value"),
        (&["--check", "--base"], "--base requires a value"),
        (&["--check", "--base", "--repo-root"], "--base requires a value"),
        (&["--check", "--base", "a", "--base", "b"], "--base is given twice"),
        (&["--check", "--row-seconds", "0"], "--row-seconds: \"0\" is not a number of seconds"),
        (&["--check", "--row-seconds", "soon"], "--row-seconds: \"soon\" is not a number"),
        (&["--bogus"], "unknown argument \"--bogus\""),
    ] {
        let mut checkout = FakeCheckout::changing(&["scripts/alpha.py"], &[]);
        let run = land(&world, args, &mut checkout, &mut FakeRunner::default());
        assert_eq!(run.code, EXIT_USAGE, "{args:?}: {}", run.text);
        assert!(run.text.starts_with(&format!("targo trust land: {error}")), "{}", run.text);
        assert!(run.text.contains("Usage: targo trust land --check"));
        assert!(run.text.contains(FOOTER), "the usage says what the verb is");
        assert!(run.specs.is_empty() && run.asked.is_empty(), "{args:?}: nothing ran");
    }
}

#[test]
fn the_base_and_the_bound_are_the_callers() {
    let world = World::new();
    for args in [
        &["--check", "--base", "HEAD~1", "--row-seconds", "7200"][..],
        &["--base=HEAD~1", "--row-seconds=7200", "--check"],
    ] {
        let mut checkout = FakeCheckout::changing(&["x.py"], &[]);
        let run = land(&world, args, &mut checkout, &mut FakeRunner::default());
        assert_eq!(run.code, 0, "{}", run.text);
        assert_eq!(run.asked, ["HEAD~1"]);
        assert!(run.line_starting("land --check: base ").contains(" base HEAD~1 (bbbbbbbbbbbb)"));
        assert_eq!(run.specs[0].bound, Duration::from_secs(7200));
    }
    // Any number of seconds above 0 is a bound, the largest included: it is
    // handed on as it is (the row's process shows it is no overflow).
    let most = u64::MAX.to_string();
    let mut checkout = FakeCheckout::changing(&["x.py"], &[]);
    let args = ["--check", "--base", "HEAD", "--row-seconds", most.as_str()];
    let run = land(&world, &args, &mut checkout, &mut FakeRunner::default());
    assert_eq!(run.code, 0, "{}", run.text);
    assert_eq!(run.specs[0].bound, Duration::from_secs(u64::MAX));
    assert!(run.progress[0].contains(&format!("at most {most}s: ")), "{:?}", run.progress);
    let over = "18446744073709551616";
    let args = ["--check", "--row-seconds", over];
    let run = land(&world, &args, &mut checkout, &mut FakeRunner::default());
    assert_eq!(run.code, EXIT_USAGE, "{}", run.text);
    assert!(run.text.starts_with("targo trust land: --row-seconds: \"18446744073709551616\" is"));
}

#[test]
fn the_checkout_is_the_callers_directory_or_repo_root() {
    let changing = || FakeCheckout::changing(&["x.py"], &[]);
    // From a directory under the checkout, the table above it is found.
    let world = World::new();
    world.write("crates/x/src/lib.rs", "");
    let under = world.path("crates/x/src");
    let run = land_from(&under, &["--check"], &mut changing(), &mut FakeRunner::default());
    assert_eq!(run.code, 0, "{}", run.text);
    assert_eq!(run.specs[0].root, world.root());

    // --repo-root, relative, is resolved against the caller's directory.
    world.write("inner/gates/land.toml", &fixture().base_table);
    let args = ["--check", "--repo-root", "inner"];
    let run = land(&world, &args, &mut changing(), &mut FakeRunner::default());
    assert_eq!(run.code, 0, "{}", run.text);
    assert_eq!(run.specs[0].root, world.root().join("inner"));

    // No table at or above the directory, and a --repo-root that is not there.
    let elsewhere = tempfile::tempdir().unwrap();
    let run =
        land_from(elsewhere.path(), &["--check"], &mut changing(), &mut FakeRunner::default());
    assert_eq!(run.code, EXIT_USAGE);
    assert!(run.text.starts_with("targo trust land: no gates/land.toml in "), "{}", run.text);
    assert!(run.text.contains("pass --repo-root"));
    assert_says_it_is_not_the_gate_and_counts_nothing(&run);
    let args = ["--check", "--repo-root", "no-such-directory"];
    let run = land(&world, &args, &mut changing(), &mut FakeRunner::default());
    assert_eq!(run.code, EXIT_USAGE);
    assert!(run.text.starts_with("targo trust land: no checkout at"), "{}", run.text);
    assert_says_it_is_not_the_gate_and_counts_nothing(&run);
}

#[test]
fn zero_rows_selected_is_exit_0_and_says_so_and_why() {
    // Nothing changed.
    let run = check(&[], &[]);
    assert_eq!(run.code, 0, "{}", run.text);
    assert!(run.has_line(
        "changed: 0 path(s) (0 between the merge base and HEAD, 0 staged, changed in the \
         working tree or untracked)"
    ));
    assert!(run.has_line("selected: 0 of 2 rows: nothing changed"));
    assert!(run.specs.is_empty());
    assert_says_what_it_is(&run);

    // Paths changed, and none selects a row.
    let run = check(&["docs/STATUS.md", "scripts/tests/delta_test.py", "gates/land.toml"], &[]);
    assert_eq!(run.code, 0, "{}", run.text);
    assert!(run.has_line(
        "selected: 0 of 2 rows: no changed path is a row's selects_on path, the table, or a \
         Cargo.toml"
    ));
    assert!(run.specs.is_empty());
    assert!(!run.text.contains("PASS"), "no row ran, so none passed:\n{}", run.text);
    assert_says_what_it_is(&run);
}

#[test]
fn a_row_passes_only_on_exit_0() {
    // The control: both rows exit 0.
    assert_eq!(check(&["scripts/alpha.py"], &[]).code, 0);

    for (exit, word, says) in [
        (ChildExit::Exited(1), "FAIL", "exit 1 (log: "),
        (ChildExit::Exited(7), "FAIL", "exit 7 (log: "),
        (ChildExit::Exited(-1), "FAIL", "exit -1 (log: "),
        (ChildExit::Signalled(9), "FAIL", "ended by signal 9 (log: "),
        (ChildExit::Exited(2), "NOT JUDGED", "exit 2, the runner's \"no test ran\" (log: "),
        (ChildExit::PastBound, "NOT JUDGED", "no verdict within 900s"),
        (
            ChildExit::Failed("cannot start python3: No such file or directory".into()),
            "NOT JUDGED",
            "cannot start python3",
        ),
    ] {
        let run = check(&["scripts/alpha.py"], &[(ALPHA, exit.clone())]);
        let line = run.line_starting(&row_line(word, &format!("{ALPHA}: ")));
        assert!(line.contains(says), "{exit:?}: {line}");
        assert!(!run.has_line(&row_line("PASS", ALPHA)), "{exit:?}");
        assert!(run.has_line(&row_line("PASS", BETA)), "the other row still ran");
        let code = if word == "FAIL" { EXIT_FAIL } else { EXIT_COULD_NOT_RUN };
        assert_eq!(run.code, code, "{exit:?}: {}", run.text);
        assert_says_what_it_is(&run);
        // The line names a log, so the logs outlive the run.
        assert!(run.logs().is_dir(), "{exit:?}");
        fs::remove_dir_all(run.logs()).unwrap();
    }
}

#[test]
fn a_row_past_its_bound_is_not_judged_and_carries_the_command_to_rerun() {
    let world = World::new();
    let mut checkout = FakeCheckout::changing(&["x.py"], &[]);
    let mut runner = FakeRunner::ending(&[(BETA, ChildExit::PastBound)]);
    let run = land(&world, &["--check", "--row-seconds", "30"], &mut checkout, &mut runner);
    assert_eq!(run.code, EXIT_COULD_NOT_RUN, "{}", run.text);
    let line = run.line_starting(&row_line("NOT JUDGED", &format!("{BETA}: ")));
    assert!(line.contains("no verdict within 30s (--row-seconds raises the bound; log: "));
    assert!(line.ends_with(
        "; rerun: python3 -B scripts/land_gate.py validation-tests scripts.tests.beta_test"
    ));
    assert!(run.has_line("land --check: 0 PASS, 0 FAIL, 1 NOT JUDGED of 1 selected row(s)"));
    assert!(run.has_line(
        "LAND-CHECK: COULD NOT RUN — 1 selected row(s) had no verdict, so the change is not \
         judged"
    ));
    fs::remove_dir_all(run.logs()).unwrap();
}

#[test]
fn a_changed_manifest_selects_a_row_the_table_may_not_have() {
    // The base table has no row for the manifest rule's id. The selector
    // names it all the same, as the Python selector does, and nothing can
    // judge it.
    let run = check(&["crates/x/Cargo.toml"], &[]);
    assert_eq!(run.code, EXIT_COULD_NOT_RUN, "{}", run.text);
    assert!(run.has_line("selected: 1 of 2 rows"));
    assert!(run.has_line(&row_line(
        "NOT JUDGED",
        &format!(
            "{MANIFEST_ROW}: selected, and gates/land.toml has no [[row]] of that id (a changed \
             Cargo.toml selects it)"
        )
    )));
    assert!(run.specs.is_empty(), "there is no command to run");
    assert_says_what_it_is(&run);
}

// --- exit precedence: 2 > 3 > 1 > 0, one test per boundary ---------------------

#[test]
fn a_table_error_outranks_a_base_that_does_not_resolve() {
    let broken = fixture().base_table.replace("trust.land-rows.v1", "trust.land-rows.v2");
    for (table, code) in [(broken, EXIT_USAGE), (fixture().base_table, EXIT_COULD_NOT_RUN)] {
        let world = World::with_table(&table);
        let mut checkout = FakeCheckout::changing(&["scripts/alpha.py"], &[]);
        checkout.unresolved.push("origin/main".into());
        let run = land(&world, &["--check"], &mut checkout, &mut FakeRunner::default());
        assert_eq!(run.code, code, "{}", run.text);
        assert!(run.specs.is_empty());
        if code == EXIT_USAGE {
            assert!(run.text.starts_with("targo trust land: gates/land.toml: schema is"));
            assert_says_it_is_not_the_gate_and_counts_nothing(&run);
        } else {
            assert_says_what_it_is(&run);
        }
    }
}

#[test]
fn a_usage_error_outranks_a_table_that_does_not_load() {
    let broken = fixture().base_table.replace("trust.land-rows.v1", "trust.land-rows.v2");
    let world = World::with_table(&broken);
    let mut checkout = FakeCheckout::changing(&["scripts/alpha.py"], &[]);
    let run = land(&world, &["--check", "--bogus"], &mut checkout, &mut FakeRunner::default());
    assert_eq!(run.code, EXIT_USAGE);
    assert!(run.text.starts_with("targo trust land: unknown argument"), "{}", run.text);
}

#[test]
fn a_base_that_does_not_resolve_could_not_run_and_is_never_no_change() {
    let world = World::new();
    let mut checkout = FakeCheckout::changing(&["scripts/alpha.py"], &[]);
    checkout.unresolved.push("no-such-branch".into());
    let args = ["--check", "--base", "no-such-branch"];
    let run = land(&world, &args, &mut checkout, &mut FakeRunner::default());
    assert_eq!(run.code, EXIT_COULD_NOT_RUN, "{}", run.text);
    assert!(run.text.starts_with(
        "LAND-CHECK: COULD NOT RUN — the base \"no-such-branch\" does not resolve to a commit"
    ));
    assert!(!run.text.contains("selected:") && !run.text.contains("nothing changed"));
    assert!(run.specs.is_empty(), "no row ran");
    assert_says_what_it_is(&run);

    // The control: the same change against a base that resolves runs its rows.
    let mut checkout = FakeCheckout::changing(&["scripts/alpha.py"], &[]);
    let run = land(&world, &["--check"], &mut checkout, &mut FakeRunner::default());
    assert_eq!((run.code, run.specs.len()), (0, 2));
}

#[test]
fn tracked_files_that_cannot_be_listed_could_not_run() {
    let world = World::new();
    let mut checkout = FakeCheckout::changing(&["scripts/alpha.py"], &[]);
    checkout.tracked = Err("git ls-files exited 128".into());
    let run = land(&world, &["--check"], &mut checkout, &mut FakeRunner::default());
    assert_eq!(run.code, EXIT_COULD_NOT_RUN, "{}", run.text);
    assert!(
        run.text
            .starts_with("LAND-CHECK: COULD NOT RUN — the tracked files: git ls-files exited 128")
    );
    assert!(run.specs.is_empty() && run.asked.is_empty());
    assert_says_what_it_is(&run);
}

#[test]
fn a_row_not_judged_outranks_a_row_that_failed() {
    // 3 > 1: one row fails and the other has no verdict.
    let exits = [(ALPHA, ChildExit::Exited(1)), (BETA, ChildExit::Exited(2))];
    let run = check(&["scripts/alpha.py"], &exits);
    assert_eq!(run.code, EXIT_COULD_NOT_RUN, "{}", run.text);
    assert!(run.has_line("land --check: 0 PASS, 1 FAIL, 1 NOT JUDGED of 2 selected row(s)"));
    fs::remove_dir_all(run.logs()).unwrap();

    // The control for the boundary: the same failure beside a pass is exit 1.
    let run = check(&["scripts/alpha.py"], &exits[..1]);
    assert_eq!(run.code, EXIT_FAIL, "{}", run.text);
    assert!(run.has_line("land --check: 1 PASS, 1 FAIL, 0 NOT JUDGED of 2 selected row(s)"));
    assert!(!run.text.contains("COULD NOT RUN"));
    fs::remove_dir_all(run.logs()).unwrap();
}

#[test]
fn a_failed_row_outranks_the_rows_that_passed() {
    // 1 > 0, and both rows run whichever fails.
    for failing in [ALPHA, BETA] {
        let run = check(&["scripts/alpha.py"], &[(failing, ChildExit::Exited(1))]);
        assert_eq!(run.code, EXIT_FAIL, "{}", run.text);
        assert_eq!(run.specs.len(), 2, "a failure does not stop the rows after it");
        fs::remove_dir_all(run.logs()).unwrap();
    }
    assert_eq!(check(&["scripts/alpha.py"], &[]).code, 0);
}

// --- the covered rule, through the verb ----------------------------------------

#[test]
fn a_tree_that_breaks_the_covered_rule_is_a_table_error() {
    let world = World::new();
    // The control: the four modules' files, and files the glob does not cover.
    let mut checkout = FakeCheckout::changing(&["x.py"], &[]);
    let mut tracked = owned(&MODULES);
    tracked.extend(owned(&["scripts/tests/helper.py", "scripts/tests/sub/zz_test.py"]));
    checkout.tracked = Ok(tracked);
    let run = land(&world, &["--check"], &mut checkout, &mut FakeRunner::default());
    assert_eq!(run.code, 0, "{}", run.text);

    // A covered file that is neither a row nor a not_run, and an entry whose
    // file is not tracked. The base does not resolve either: 2 outranks 3.
    let mut checkout = FakeCheckout::changing(&["x.py"], &[]);
    checkout.unresolved.push("origin/main".into());
    checkout.tracked =
        Ok(owned(&[MODULES[0], MODULES[1], MODULES[2], "scripts/tests/zz_new_test.py"]));
    let run = land(&world, &["--check"], &mut checkout, &mut FakeRunner::default());
    assert_eq!(run.code, EXIT_USAGE, "{}", run.text);
    assert!(
        run.text
            .starts_with("targo trust land: gates/land.toml: 2 file(s) break its `covered` rule")
    );
    assert!(run.has_line("  scripts/tests/zz_new_test.py: neither a [[row]] nor a [[not_run]]"));
    assert!(run.has_line(
        "  [[not_run]] validation.gamma_test: scripts/tests/gamma_test.py is not a tracked file"
    ));
    assert!(run.specs.is_empty() && run.asked.is_empty(), "nothing was selected or run");
    // The table loaded, so the run still says what it is.
    assert_says_what_it_is(&run);
}

// --- the row's process ---------------------------------------------------------

#[cfg(unix)]
mod process {
    use std::time::Instant;

    use super::super::run::RowProcess;
    use super::*;

    const LONG: Duration = Duration::from_secs(120);

    /// Run `script` as a row's command, from a directory of its own.
    fn sh(script: &str, bound: Duration) -> (ChildExit, Verdict, String, tempfile::TempDir) {
        let directory = tempfile::tempdir().unwrap();
        let root = fs::canonicalize(directory.path()).unwrap();
        let spec = RowSpec {
            id: "validation.sh_test".into(),
            argv: owned(&["/bin/sh", "-c", script]),
            log: run::log_path(&root, "validation.sh_test"),
            root,
            bound,
        };
        let exit = RowProcess.run(&spec);
        let verdict = run::judge(&spec, &exit);
        let log = fs::read_to_string(&spec.log).unwrap_or_default();
        (exit, verdict, log, directory)
    }

    #[test]
    fn a_command_runs_from_the_root_with_no_stdin_and_its_output_in_the_log() {
        // `cat` returns at once on an empty stdin; a terminal's would hold it.
        let (exit, verdict, log, directory) =
            sh("pwd; echo to-stderr >&2; cat; echo after-stdin", LONG);
        assert_eq!(exit, ChildExit::Exited(0));
        assert_eq!(verdict, Verdict::Pass);
        let root = fs::canonicalize(directory.path()).unwrap();
        assert_eq!(log, format!("{}\nto-stderr\nafter-stdin\n", root.display()));
    }

    #[test]
    fn only_exit_0_passes() {
        for (script, word) in [
            ("exit 0", "PASS"),
            ("exit 1", "FAIL"),
            ("exit 2", "NOT JUDGED"),
            ("exit 3", "FAIL"),
            ("exit 255", "FAIL"),
            ("kill -9 $$", "FAIL"),
            ("kill -15 $$", "FAIL"),
        ] {
            let (exit, verdict, _log, _directory) = sh(script, LONG);
            assert_eq!(verdict.word(), word, "{script}: {exit:?}");
        }
        let (exit, _verdict, _log, _directory) = sh("kill -9 $$", LONG);
        assert_eq!(exit, ChildExit::Signalled(9));
    }

    #[test]
    fn a_command_still_running_at_its_bound_is_stopped_and_not_judged() {
        let started = Instant::now();
        let script = "echo started; sleep 600; echo finished";
        let (exit, verdict, log, _directory) = sh(script, Duration::from_secs(1));
        assert_eq!(exit, ChildExit::PastBound);
        assert!(started.elapsed() < Duration::from_secs(60), "{:?}", started.elapsed());
        assert!(log.starts_with("started\n") && !log.contains("finished"), "{log:?}");
        match verdict {
            Verdict::NotJudged(why) => {
                assert!(why.starts_with("no verdict within 1s"), "{why}");
                assert!(why.ends_with(&format!("; rerun: /bin/sh -c '{script}'")), "{why}");
            }
            other => panic!("a row past its bound is {other:?}"),
        }
    }

    #[test]
    fn a_bound_past_the_end_of_the_clock_is_no_bound_and_no_overflow() {
        for bound in [Duration::from_secs(u64::MAX), Duration::from_secs(i64::MAX as u64)] {
            // The instrument: this bound is one the clock cannot add.
            assert!(Instant::now().checked_add(bound).is_none(), "{bound:?}");
            // A command that outlives several polls, so the deadline is read.
            let (exit, verdict, log, _directory) = sh("sleep 1; echo done", bound);
            assert_eq!((exit, verdict), (ChildExit::Exited(0), Verdict::Pass), "{bound:?}");
            assert_eq!(log, "done\n");
            let (exit, verdict, _log, _directory) = sh("exit 1", bound);
            assert_eq!((exit, verdict.word()), (ChildExit::Exited(1), "FAIL"), "{bound:?}");
        }
        // The control: a bound the clock can add still stops a command.
        let (exit, _verdict, _log, _directory) = sh("sleep 600", Duration::from_millis(200));
        assert_eq!(exit, ChildExit::PastBound);
    }

    #[test]
    fn what_a_command_leaves_running_is_stopped_before_its_exit_is_a_verdict() {
        // The leader exits 0 with a child of its own still running.
        let (exit, verdict, log, _directory) = sh("sleep 600 & echo $!", LONG);
        assert_eq!((exit, verdict), (ChildExit::Exited(0), Verdict::Pass));
        let pid: i32 = log.trim().parse().unwrap();
        let deadline = Instant::now() + Duration::from_secs(30);
        // SAFETY: signal 0 sends nothing; it only asks whether the pid is there.
        while unsafe { libc::kill(pid, 0) } == 0 {
            assert!(Instant::now() < deadline, "the row's descendant {pid} is still running");
            std::thread::sleep(Duration::from_millis(20));
        }
    }

    #[test]
    fn a_command_that_cannot_be_started_is_not_judged() {
        let directory = tempfile::tempdir().unwrap();
        let root = fs::canonicalize(directory.path()).unwrap();
        let spec = RowSpec {
            id: "validation.gone_test".into(),
            argv: vec![root.join("no-such-program").display().to_string()],
            log: run::log_path(&root, "validation.gone_test"),
            root,
            bound: LONG,
        };
        let exit = RowProcess.run(&spec);
        match run::judge(&spec, &exit) {
            Verdict::NotJudged(why) => assert!(why.starts_with("cannot start "), "{why}"),
            other => panic!("{other:?}"),
        }
        let empty = RowSpec { argv: Vec::new(), ..spec };
        assert_eq!(RowProcess.run(&empty), ChildExit::Failed("the row has no command".into()));
    }

    #[test]
    fn a_rerun_line_reads_back_as_the_argv() {
        assert_eq!(
            run::command_line(&owned(&["python3", "-B", "scripts/land_gate.py", "a.b_c"])),
            "python3 -B scripts/land_gate.py a.b_c"
        );
        assert_eq!(
            run::command_line(&owned(&["sh", "-c", "it's; x", ""])),
            "sh -c 'it'\\''s; x' ''"
        );
    }
}

// --- the change, from a real repository ----------------------------------------

#[cfg(unix)]
mod repository {
    use std::process::Command;

    use super::super::select::GitCheckout;
    use super::*;
    use crate::controlled_git;

    struct Repository {
        directory: tempfile::TempDir,
    }

    impl Repository {
        /// A repository with one commit on `main`: `a.txt`, `b.txt` and a
        /// `.gitignore`.
        fn new() -> Self {
            let repository = Self { directory: tempfile::tempdir().unwrap() };
            repository.git(&["init", "--quiet", "--initial-branch=main"]);
            repository.write(".gitignore", "*.log\n");
            repository.write("a.txt", "a\n");
            repository.write("b.txt", "b\n");
            repository.commit("base");
            repository
        }

        fn root(&self) -> PathBuf {
            fs::canonicalize(self.directory.path()).unwrap()
        }

        fn git(&self, args: &[&str]) -> String {
            let output = Command::new(controlled_git::executable().unwrap())
                .env_clear()
                .env("LC_ALL", "C")
                .env("GIT_CONFIG_NOSYSTEM", "1")
                .env("GIT_CONFIG_GLOBAL", "/dev/null")
                .arg("-C")
                .arg(self.directory.path())
                .args(["-c", "user.name=Trust Tests", "-c", "user.email=tests@example.invalid"])
                .args(args)
                .output()
                .unwrap();
            assert!(
                output.status.success(),
                "git {args:?}: {}",
                String::from_utf8_lossy(&output.stderr)
            );
            String::from_utf8(output.stdout).unwrap().trim().to_owned()
        }

        fn write(&self, relative: &str, text: &str) {
            let path = self.directory.path().join(relative);
            fs::create_dir_all(path.parent().unwrap()).unwrap();
            fs::write(path, text).unwrap();
        }

        fn commit(&self, message: &str) -> String {
            self.git(&["add", "--all"]);
            self.git(&["commit", "--quiet", "-m", message]);
            self.git(&["rev-parse", "HEAD"])
        }
    }

    fn set(paths: &[&str]) -> BTreeSet<String> {
        owned(paths).into_iter().collect()
    }

    #[test]
    fn the_change_is_the_commits_since_the_merge_base_and_the_working_tree() {
        let repository = Repository::new();
        let base = repository.git(&["rev-parse", "HEAD"]);
        // A side branch that main never merges: its change is not main's.
        repository.git(&["checkout", "--quiet", "-b", "side"]);
        repository.write("side.txt", "side\n");
        let side = repository.commit("side");
        repository.git(&["checkout", "--quiet", "main"]);
        // main: change a file, delete one and add one; then move the new one.
        repository.write("a.txt", "a changed\n");
        fs::remove_file(repository.directory.path().join("b.txt")).unwrap();
        repository.write("dir/c.txt", "c\n");
        let first = repository.commit("first");
        repository.git(&["mv", "dir/c.txt", "dir/d.txt"]);
        let head = repository.commit("second");
        // The working tree: one file staged, one changed and not staged, one
        // untracked, one ignored.
        repository.write("staged.txt", "staged\n");
        repository.git(&["add", "staged.txt"]);
        repository.write("a.txt", "a changed again\n");
        repository.write("new/untracked.txt", "untracked\n");
        repository.write("build.log", "ignored\n");

        let root = repository.root();
        let working = set(&["a.txt", "new/untracked.txt", "staged.txt"]);

        // Against the side branch: the merge base is the commit both hold,
        // and the side branch's own file is no part of the change.
        let change = GitCheckout.change(&root, "side").unwrap();
        assert_eq!(change.base, side);
        assert_eq!(change.merge_base, base);
        assert_eq!(change.head, head);
        assert_eq!(change.committed, set(&["a.txt", "b.txt", "dir/d.txt"]));
        assert_eq!(change.working, working);
        assert_eq!(
            change.paths(),
            ["a.txt", "b.txt", "dir/d.txt", "new/untracked.txt", "staged.txt"]
        );

        // Against the commit before HEAD: only what the last commit moved. A
        // move is both of its paths: nothing is paired into a rename.
        let change = GitCheckout.change(&root, "HEAD~1").unwrap();
        assert_eq!((change.base.as_str(), change.merge_base.as_str()), (&*first, &*first));
        assert_eq!(change.committed, set(&["dir/c.txt", "dir/d.txt"]));
        assert_eq!(change.working, working);

        // Against HEAD: nothing committed, and the working tree is still a
        // change.
        let change = GitCheckout.change(&root, "HEAD").unwrap();
        assert!(change.committed.is_empty());
        assert_eq!(change.working, working);

        // The tracked files are the index's: the staged file, and neither the
        // untracked nor the ignored one.
        assert_eq!(
            GitCheckout.tracked(&root).unwrap(),
            set(&[".gitignore", "a.txt", "dir/d.txt", "staged.txt"])
        );
    }

    #[test]
    fn a_base_that_does_not_resolve_is_an_error_and_never_an_empty_change() {
        let repository = Repository::new();
        let root = repository.root();
        // The control: a base that resolves, with nothing changed since.
        let change = GitCheckout.change(&root, "main").unwrap();
        assert!(change.paths().is_empty());

        for base in ["origin/main", "no-such-branch", "HEAD~7", "0000000", "a.txt", "--all"] {
            let error = GitCheckout.change(&root, base).unwrap_err();
            assert!(error.contains("does not resolve to a commit"), "{base}: {error}");
            assert!(error.contains(&format!("{base:?}")), "{base}: {error}");
        }

        // A base with no history in common with HEAD has no merge base.
        repository.git(&["checkout", "--quiet", "--orphan", "island"]);
        repository.write("island.txt", "island\n");
        repository.commit("island");
        repository.git(&["checkout", "--quiet", "main"]);
        let error = GitCheckout.change(&root, "island").unwrap_err();
        assert!(error.contains("have no merge base"), "{error}");
    }

    #[test]
    fn a_git_listing_that_fails_is_an_error_and_never_an_empty_listing() {
        let repository = Repository::new();
        let root = repository.root();
        repository.write("a.txt", "a changed\n");
        // The control: the listings of an intact repository.
        assert_eq!(GitCheckout.tracked(&root).unwrap(), set(&[".gitignore", "a.txt", "b.txt"]));
        assert_eq!(GitCheckout.change(&root, "HEAD").unwrap().paths(), ["a.txt"]);

        // An index git cannot read: every listing of it exits non-zero. The
        // error is the exit, whatever git wrote beside it.
        fs::write(root.join(".git/index"), "not an index").unwrap();
        let error = GitCheckout.tracked(&root).unwrap_err();
        assert!(error.starts_with("git ls-files exited "), "{error}");
        assert!(error.contains("128"), "{error}");
        let error = GitCheckout.change(&root, "HEAD").unwrap_err();
        assert!(error.starts_with("git ls-files of the index exited "), "{error}");

        // Through the verb: COULD NOT RUN, and no "nothing changed".
        repository.write(TABLE, &fixture().base_table);
        let mut runner = FakeRunner::default();
        let mut progress = |_: &str| {};
        let (code, text) = run_with(
            &owned(&["--check", "--base", "HEAD"]),
            &mut Host {
                cwd: root,
                checkout: &mut GitCheckout,
                runner: &mut runner,
                progress: &mut progress,
            },
        );
        assert_eq!(code, EXIT_COULD_NOT_RUN, "{text}");
        assert!(text.starts_with("LAND-CHECK: COULD NOT RUN — the tracked files: git ls-files"));
        assert!(!text.contains("selected:") && runner.specs.is_empty(), "{text}");
    }

    #[test]
    fn a_path_the_index_hides_from_git_is_an_error_and_never_a_smaller_change() {
        for (mark, clear) in [
            ("--assume-unchanged", "--no-assume-unchanged"),
            ("--skip-worktree", "--no-skip-worktree"),
        ] {
            let repository = Repository::new();
            let root = repository.root();
            repository.git(&["update-index", mark, "a.txt"]);
            repository.write("a.txt", "a changed\n");
            repository.write("b.txt", "b changed\n");
            // Git itself shows the one change and not the other.
            assert_eq!(repository.git(&["diff", "--name-only"]), "b.txt", "{mark}");

            let error = GitCheckout.change(&root, "HEAD").unwrap_err();
            assert!(
                error.starts_with(
                    "1 index entry is marked assume-unchanged or skip-worktree (a.txt): "
                ),
                "{mark}: {error}"
            );
            // The tracked files are the index's whatever its marks.
            assert_eq!(GitCheckout.tracked(&root).unwrap(), set(&[".gitignore", "a.txt", "b.txt"]));

            // The control: the same tree without the mark is the whole change.
            repository.git(&["update-index", clear, "a.txt"]);
            let change = GitCheckout.change(&root, "HEAD").unwrap();
            assert_eq!(change.paths(), ["a.txt", "b.txt"], "{mark}");
        }

        // Two marked entries are counted, and the first is named.
        let repository = Repository::new();
        repository.git(&["update-index", "--assume-unchanged", "a.txt"]);
        repository.git(&["update-index", "--skip-worktree", "b.txt"]);
        let error = GitCheckout.change(&repository.root(), "HEAD").unwrap_err();
        assert!(error.starts_with("2 index entries are marked "), "{error}");
        assert!(error.contains("(a.txt, ...)"), "{error}");
    }

    #[test]
    fn a_hidden_entry_is_a_lower_case_tag_or_skip_worktree() {
        let entries = |listed: &[&str]| -> BTreeSet<String> { set(listed) };
        // `H` is an entry git compares; `M` is unmerged, which git's diff lists.
        assert_eq!(select::hidden_paths(&entries(&["H a.txt", "M dir/b c.txt"])), Ok(Vec::new()));
        assert_eq!(
            select::hidden_paths(&entries(&["H a", "h b", "S c", "s d", "m e", "H  f"])),
            Ok(owned(&["b", "c", "d", "e"])),
            "by path, whatever the tag"
        );
        for entry in ["", "H", "Hx", "a.txt"] {
            let error = select::hidden_paths(&entries(&["H a", entry])).unwrap_err();
            assert!(error.contains("an entry that has no tag"), "{entry:?}: {error}");
        }
    }

    #[test]
    fn the_verb_over_a_real_repository_runs_the_rows_its_change_selects() {
        // The base table and its four modules' files, committed; then a
        // change to one selecting path, not committed.
        let repository = Repository::new();
        repository.write(TABLE, &fixture().base_table);
        for module in MODULES {
            repository.write(module, "");
        }
        repository.write("x.py", "");
        repository.commit("table");
        repository.write("x.py", "changed\n");

        let run = |args: &[&str]| {
            let mut runner = FakeRunner::default();
            let mut progress = |_: &str| {};
            let (code, text) = run_with(
                &owned(args),
                &mut Host {
                    cwd: repository.root(),
                    checkout: &mut GitCheckout,
                    runner: &mut runner,
                    progress: &mut progress,
                },
            );
            (code, text, runner.specs.len())
        };
        let (code, text, ran) = run(&["--check", "--base", "HEAD"]);
        assert_eq!((code, ran), (0, 1), "{text}");
        assert!(text.contains("changed: 1 path(s) (0 between the merge base and HEAD, 1 staged"));
        let rows = format!("\nselected: 1 of 2 rows\n{}\n", row_line("PASS", BETA));
        assert!(text.contains(&rows), "{text}");

        // The default base is origin/main, which this repository does not have.
        let (code, text, ran) = run(&["--check"]);
        assert_eq!((code, ran), (EXIT_COULD_NOT_RUN, 0), "{text}");
        assert!(text.starts_with(
            "LAND-CHECK: COULD NOT RUN — the base \"origin/main\" does not resolve to a commit"
        ));

        // A module's file breaks the covered rule once git tracks it, and not
        // before.
        repository.write("scripts/tests/zz_untracked_test.py", "");
        let (code, text, _ran) = run(&["--check", "--base", "HEAD"]);
        assert_eq!(code, 0, "an untracked file is not a covered file: {text}");
        repository.git(&["add", "scripts/tests/zz_untracked_test.py"]);
        let (code, text, ran) = run(&["--check", "--base", "HEAD"]);
        assert_eq!((code, ran), (EXIT_USAGE, 0), "{text}");
        assert!(
            text.contains(
                "scripts/tests/zz_untracked_test.py: neither a [[row]] nor a [[not_run]]"
            )
        );
    }
}
