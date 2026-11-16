// Trust (2026-10-13): `canonical_place_in` handed its caller's local-name table folds a
// place exactly as `canonical_place` does asking for a table of its own.
//
// `place_to_var_name_uncached` holds the function's `LocalNameTable` for the rest of its
// mint. From UNION-SIBLING-WRITE-2 (`dec56db17b`) it took its canonical place from
// `canonical_place`, which asked `place_memo::local_names` for the table AGAIN: a memo
// hit inside a generation scope, a second whole-table build per name outside one. The
// mint now hands its table to `canonical_place_in` (`tests/place_name_local_table_once.rs`
// pins the count). The fold must not notice: `canonical_place` (the table asked for,
// the path the mint took before and every other caller still takes) is the reference
// here, over every place of the crate's extracted-MIR corpora, outside a scope and
// inside one, and on the duplicate-index bodies whose fold is declined.

use std::collections::HashSet;
use std::path::{Path, PathBuf};

use trust_types::{LocalDecl, Place, VerifiableFunction};

use crate::{LocalNameTable, canonical_place, canonical_place_in, place_memo};

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

/// Every declared local, whole, then every place the JSON `body` spells, each once.
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
/// data directories, in path order, with the places it spells.
fn corpus() -> Vec<(String, VerifiableFunction, Vec<Place>)> {
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
            out.push((label, func, places));
        } else if let Ok(funcs) = serde_json::from_str::<Vec<VerifiableFunction>>(&text) {
            for (i, func) in funcs.into_iter().enumerate() {
                let places = json.get(i).map(|one| places_of(&func, one)).unwrap_or_default();
                out.push((format!("{label}#{i}"), func, places));
            }
        }
    }
    out
}

fn assert_corpus_is_not_vacuous(corpus: &[(String, VerifiableFunction, Vec<Place>)]) {
    let places: usize = corpus.iter().map(|(_, _, places)| places.len()).sum();
    let projected = corpus
        .iter()
        .flat_map(|(_, _, places)| places)
        .filter(|place| !place.projections.is_empty())
        .count();
    assert!(
        corpus.len() >= 1_500 && places >= 20_000 && projected >= 3_000,
        "the corpus shrank: {} bodies, {places} places, {projected} of them projected",
        corpus.len()
    );
}

/// Outside a scope (nothing memoized: `canonical_place` builds a table per ask) and
/// inside one (each side in a scope of its own, so neither reads the other's memo), the
/// handed table gives the place the asked one gives. `folded` is the anti-vacuity
/// count: places the fold actually moves.
#[test]
fn a_handed_local_name_table_folds_every_corpus_place_as_an_asked_one_does() {
    let corpus = corpus();
    assert_corpus_is_not_vacuous(&corpus);
    let mut folded = 0usize;
    for (label, func, places) in &corpus {
        let table = LocalNameTable::of(func);
        for place in places {
            let asked = canonical_place(func, place);
            let handed = canonical_place_in(func, place, Some(&table));
            assert_eq!(asked, handed, "{label}: {place:?}, outside a scope");
            folded += usize::from(asked != *place);
        }
        let asked: Vec<Place> = {
            let _scope = crate::row_replay_scope();
            places.iter().map(|place| canonical_place(func, place)).collect()
        };
        let handed: Vec<Place> = {
            let _scope = crate::row_replay_scope();
            let table = place_memo::local_names(func);
            places
                .iter()
                .map(|place| canonical_place_in(func, place, Some(table.as_ref())))
                .collect()
        };
        assert_eq!(asked, handed, "{label}: inside a scope");
    }
    assert!(folded >= 500, "the fold moved only {folded} corpus places: the comparison is vacuous");
}

/// A body whose declaration indices are NOT unique declines the fold (the mint keeps
/// its `_N` fallback there). Both paths decline alike, and the place comes back as
/// given.
#[test]
fn a_handed_table_declines_the_fold_on_duplicate_indices_as_an_asked_one_does() {
    let corpus = corpus();
    let mut checked = 0usize;
    let mut would_fold = 0usize;
    for (label, func, places) in corpus.iter().filter(|(_, func, _)| !func.body.locals.is_empty()) {
        if !places.iter().any(|place| canonical_place(func, place) != *place) {
            continue;
        }
        let mut duplicated = func.clone();
        let first = &func.body.locals[0];
        duplicated.body.locals.push(LocalDecl {
            index: first.index,
            ty: first.ty.clone(),
            name: None,
        });
        let table = LocalNameTable::of(&duplicated);
        assert!(!table.indices_unique(&duplicated), "{label}: the copy duplicates an index");
        for place in places {
            would_fold += usize::from(canonical_place(func, place) != *place);
            let asked = canonical_place(&duplicated, place);
            let handed = canonical_place_in(&duplicated, place, Some(&table));
            assert_eq!(asked, *place, "{label}: {place:?}: an asked table declines the fold");
            assert_eq!(handed, *place, "{label}: {place:?}: a handed table declines the fold");
            let _ = crate::place_to_var_name(&duplicated, place);
        }
        checked += 1;
        if checked == 200 {
            break;
        }
    }
    assert!(
        checked >= 100 && would_fold >= 200,
        "only {checked} duplicate-index bodies, {would_fold} places the fold would have moved"
    );
}
