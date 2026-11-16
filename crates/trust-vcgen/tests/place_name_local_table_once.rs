// Trust (2026-10-13): an uncached place name builds the function's local-name table ONCE.
//
// `place_to_var_name` mints a name from the function's local-name table
// (`LocalNameTable`: one pass over every local of the body). Inside a VC-generation
// scope `place_memo` builds that table once per function. OUTSIDE a scope nothing is
// memoized, so the mint builds a table for every name: that is what an unscoped replay
// pays, and until 2026-10-19 the compiler's StepBy-constructor root-charge gate was one
// (`rustc_mir_transform::trust_verify::step_by_constructor`:
// `ConstructorPlan::root_charges` -> `generate_callsite_precondition_vcs`, which now
// opens its own scope, `generate::EntryScope`).
//
// From `dec56db17b` (UNION-SIBLING-WRITE-2) the unscoped mint built the table TWICE:
// it asked `place_memo::local_names`, then took its canonical place from
// `canonical_place`, which asked again. Measured on stage-1 compilers one commit apart,
// that second table took a function from 108.8 s to 152.9 s of wall time (aterm-census
// `run_mainloop_census`: one replayed root of about 350 source lines), which carried it
// over its 120 s per-function clock: its `[unreach]` row went PROVED -> TIMEOUT with
// nothing about the proof changed. The mint now hands the table it holds to the fold
// (`canonical_place_in`).
//
// What is pinned is WORK, never wall time: `AnalysisMemoStats` counts the tables
// actually built (`local_name_tables_computed`) and the names actually minted
// (`place_names_computed`). The bodies are the crate's own extracted-MIR corpora, every
// JSON `VerifiableFunction` under `tests/data` and `tests/fixtures`, and the places are
// the ones those bodies spell. The same walk answers the other question a refactor of
// the mint has to answer, that no NAME moved: a place is named alike inside and outside
// a scope, and `TRUST_VCGEN_PLACE_NAME_DUMP=<file>` writes every name so that two
// builds of this crate can be compared byte for byte.

use std::collections::HashSet;
use std::fmt::Write as _;
use std::path::{Path, PathBuf};

use trust_types::{Place, VerifiableFunction};
use trust_vcgen::{analysis_memo_stats, place_to_var_name, reset_analysis_memo_stats};

/// One corpus body, with the places it spells.
struct Body {
    /// Its file, relative to `tests/` (`#i` appended for a file holding a list).
    label: String,
    func: VerifiableFunction,
    places: Vec<Place>,
}

fn json_files(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = std::fs::read_dir(dir) else { return };
    for path in entries.flatten().map(|entry| entry.path()) {
        if path.is_dir() {
            json_files(&path, out);
        } else if path.extension().is_some_and(|ext| ext == "json") {
            out.push(path);
        }
    }
}

/// Every `Place` the JSON `value` holds: each object that is exactly a `Place`.
fn harvest_places(value: &serde_json::Value, out: &mut Vec<Place>) {
    match value {
        serde_json::Value::Object(map) => {
            if map.len() == 2
                && map.contains_key("local")
                && map.contains_key("projections")
                && let Ok(place) = serde_json::from_value::<Place>(value.clone())
            {
                out.push(place);
            }
            for inner in map.values() {
                harvest_places(inner, out);
            }
        }
        serde_json::Value::Array(items) => {
            for inner in items {
                harvest_places(inner, out);
            }
        }
        _ => {}
    }
}

/// The places of one body: every declared local, whole, then every place its JSON
/// `body` spells, each once, in that order.
fn places_of(func: &VerifiableFunction, json: &serde_json::Value) -> Vec<Place> {
    let mut out: Vec<Place> =
        func.body.locals.iter().map(|decl| Place::local(decl.index)).collect();
    if let Some(body) = json.get("body") {
        harvest_places(body, &mut out);
    }
    let mut seen = HashSet::new();
    out.retain(|place| seen.insert(place.clone()));
    out
}

/// Every JSON-serialised `VerifiableFunction` (or list of them) under the crate's test
/// data directories, in path order. A JSON file of another shape is not a body and is
/// skipped.
fn corpus() -> Vec<Body> {
    let tests = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests");
    let mut paths = Vec::new();
    for dir in ["data", "fixtures"] {
        json_files(&tests.join(dir), &mut paths);
    }
    paths.sort();
    let mut out = Vec::new();
    for path in paths {
        let Ok(text) = std::fs::read_to_string(&path) else { continue };
        let Ok(json) = serde_json::from_str::<serde_json::Value>(&text) else { continue };
        let label = path.strip_prefix(&tests).unwrap_or(&path).to_string_lossy().to_string();
        if let Ok(func) = serde_json::from_str::<VerifiableFunction>(&text) {
            let places = places_of(&func, &json);
            out.push(Body { label, func, places });
        } else if let Ok(funcs) = serde_json::from_str::<Vec<VerifiableFunction>>(&text) {
            for (i, func) in funcs.into_iter().enumerate() {
                let places = json.get(i).map(|one| places_of(&func, one)).unwrap_or_default();
                out.push(Body { label: format!("{label}#{i}"), func, places });
            }
        }
    }
    out
}

/// The corpus is the instrument: a walk that found almost nothing would pin nothing.
fn assert_corpus_is_not_vacuous(corpus: &[Body]) {
    let places: usize = corpus.iter().map(|body| body.places.len()).sum();
    let projected = corpus
        .iter()
        .flat_map(|body| &body.places)
        .filter(|place| !place.projections.is_empty())
        .count();
    assert!(
        corpus.len() >= 1_500 && places >= 20_000 && projected >= 3_000,
        "the corpus shrank: {} bodies, {places} places, {projected} of them projected",
        corpus.len()
    );
}

/// THE PIN. Outside a generation scope every `place_to_var_name` is an uncached mint,
/// and one mint builds ONE local-name table.
///
/// FAILS BEFORE: with the mint taking its canonical place from `canonical_place`
/// (which asks `place_memo::local_names` for a table of its own) every one of these
/// names builds two.
#[test]
fn outside_a_scope_an_uncached_place_name_builds_one_local_name_table() {
    let corpus = corpus();
    assert_corpus_is_not_vacuous(&corpus);
    let mut names = 0u64;
    let mut tables = 0u64;
    let mut wrong = Vec::new();
    for body in &corpus {
        for place in &body.places {
            reset_analysis_memo_stats();
            let name = place_to_var_name(&body.func, place);
            let stats = analysis_memo_stats();
            names += stats.place_names_computed;
            tables += stats.local_name_tables_computed;
            if (stats.place_names_computed, stats.local_name_tables_computed) != (1, 1)
                && wrong.len() < 20
            {
                wrong.push(format!(
                    "{}: {place:?} (`{name}`): {} name(s) minted, {} local-name table(s) built",
                    body.label, stats.place_names_computed, stats.local_name_tables_computed
                ));
            }
        }
    }
    assert!(
        wrong.is_empty(),
        "an unscoped place name must mint once and build one local-name table \
         ({names} names minted, {tables} tables built over the corpus); first offenders:\n{}",
        wrong.join("\n")
    );
    assert_eq!(names, tables, "one local-name table per uncached place name");
    println!(
        "LOCAL-NAME-TABLES outside a scope: {} bodies, {names} names minted, {tables} tables built",
        corpus.len()
    );
}

/// The control, and what a scope buys: inside a generation scope the table is built
/// once per FUNCTION, however many of its places are named. (This held before the
/// mint handed its table through, and must keep holding: the handed table is the
/// memoized one.)
#[test]
fn inside_a_scope_a_function_builds_one_local_name_table_for_all_its_names() {
    let corpus = corpus();
    assert_corpus_is_not_vacuous(&corpus);
    let mut wrong = Vec::new();
    let mut names = 0u64;
    let mut tables = 0u64;
    for body in &corpus {
        if body.places.is_empty() {
            continue;
        }
        let _scope = trust_vcgen::row_replay_scope();
        reset_analysis_memo_stats();
        for place in &body.places {
            let _ = place_to_var_name(&body.func, place);
        }
        let stats = analysis_memo_stats();
        names += stats.place_names_computed;
        tables += stats.local_name_tables_computed;
        if stats.local_name_tables_computed != 1 && wrong.len() < 20 {
            wrong.push(format!(
                "{}: {} places, {} names minted, {} local-name tables built",
                body.label,
                body.places.len(),
                stats.place_names_computed,
                stats.local_name_tables_computed
            ));
        }
    }
    assert!(
        wrong.is_empty(),
        "inside a scope a function's local-name table is built once; first offenders:\n{}",
        wrong.join("\n")
    );
    println!(
        "LOCAL-NAME-TABLES inside a scope: {} bodies, {names} names minted, {tables} tables built",
        corpus.len()
    );
}

/// No name depends on who holds the table: every corpus place is named alike outside a
/// scope (a fresh table per mint) and inside one (the memoized table).
///
/// With `TRUST_VCGEN_PLACE_NAME_DUMP=<file>` it also writes one line per place,
/// `<body>\t<place as JSON>\t<name outside a scope>\t<name inside one>`, in corpus
/// order: the instrument for comparing two builds of this crate name by name.
#[test]
fn a_place_is_named_alike_inside_and_outside_a_generation_scope() {
    let corpus = corpus();
    assert_corpus_is_not_vacuous(&corpus);
    let dump_to = std::env::var_os("TRUST_VCGEN_PLACE_NAME_DUMP");
    let mut dump = String::new();
    let mut differing = Vec::new();
    let mut compared = 0usize;
    for body in &corpus {
        let unscoped: Vec<String> =
            body.places.iter().map(|place| place_to_var_name(&body.func, place)).collect();
        let scoped: Vec<String> = {
            let _scope = trust_vcgen::row_replay_scope();
            body.places.iter().map(|place| place_to_var_name(&body.func, place)).collect()
        };
        for ((place, outside), inside) in body.places.iter().zip(&unscoped).zip(&scoped) {
            compared += 1;
            if outside != inside && differing.len() < 20 {
                differing.push(format!(
                    "{}: {place:?}: `{outside}` outside a scope, `{inside}` inside one",
                    body.label
                ));
            }
            if dump_to.is_some() {
                let spelled = serde_json::to_string(place).expect("a place serialises");
                writeln!(dump, "{}\t{spelled}\t{outside}\t{inside}", body.label)
                    .expect("writing to a String");
            }
        }
    }
    assert!(
        differing.is_empty(),
        "a place name differs with the scope ({compared} places compared); first:\n{}",
        differing.join("\n")
    );
    println!(
        "PLACE-NAMES {} bodies, {compared} places named alike in and out of a scope",
        corpus.len()
    );
    if let Some(path) = dump_to {
        std::fs::write(&path, dump).unwrap_or_else(|e| panic!("{path:?}: {e}"));
    }
}
