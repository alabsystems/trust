// VGAPS-G1 (the verifier-gaps design §2.3, its finding F6c): every site that conjoins
// `generate::build_global_invariant_facts` is classified by WHERE the facts' names are
// rendered, because the element-read congruence (`build_element_read_congruence_facts`,
// one of the set) is a theorem only when every name of one fact is rendered at ONE point
// (the design's (I2)):
//
// * `RowPoint`: the facts are conjoined into the row's formula BEFORE the whole-row
//   version rename, so every name takes the version that reaches the row
//   (`safety.rs`: `conjoin_preconditions_versioned_at_point_recorded`; `hardened.rs`:
//   `conjoin_preconditions_versioned` at the assert's block);
// * `BareEntry`: the facts are conjoined after the rename, or into a formula that is
//   never renamed, so an element name in them carries no token: the entry/unwritten
//   version (`normalize_ssa_version_tokens` collapses only names that resolve to a
//   WHOLE local), and the fact is a theorem about the entry state.
//
// A new site fails this test until it is classified here, with the argument for its
// class. It is a SOURCE SCAN, not a proof: it cannot see a site that conjoins the facts
// and then renames part of the formula, and it keys a site on its file and enclosing
// `fn`. Evidence rung: test.
//
// A SITE IS WHERE THE SET IS BUILT FOR A ROW, under every spelling that builds it
// ([`PRODUCERS`]). Trust: 2026-11-07 (VCGEN-CENSUS-SITE-REDS-1): the scan keyed on the
// one spelling `build_global_invariant_facts(` while PERF-COMPILER-VCGEN-72
// (`f20149a3a9`) re-spelled all eight sites `RowGlobalFacts::for_function(func)`, so it
// found NO site and a new unclassified one could not fail it (the census silently
// empty; PERF-COMPILER-VCGEN-68, `59a4d3a26c`, had already moved one `callsite.rs` site
// into `generate_callsite_precondition_vcs_with_shared`). PERF-COMPILER-VCGEN-81
// (`d701fb1959`) then spelled them `build_global_invariant_facts(func)` again, now the
// per-scope cache `row_global_facts_for` over `RowGlobalFacts::for_function`. Every
// rename and move was re-read at its site: each set is conjoined where it was before,
// so every class stands.
use std::path::{Path, PathBuf};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Class {
    RowPoint,
    BareEntry,
}

/// (file under `trust-vcgen/src`, enclosing `fn`, class), one row per call.
const SITES: &[(&str, &str, Class)] = &[
    ("generate/safety.rs", "generate_v2_safety_vcs_impl_with_origins_checked", Class::RowPoint),
    ("hardened.rs", "append_assert_panic_vcs", Class::RowPoint),
    // PERF-COMPILER-VCGEN-68 split the single-database body out of `_for_each` into
    // `_with_shared`, and PERF-COMPILER-VCGEN-81 folded it back (the caller-only analyses,
    // the set among them, in per-call `OnceCell`s); re-read at `d701fb1959`: the set is
    // still conjoined after the semantic guards (`for_row`), then only alias-freshened
    // and SSA-normalised.
    ("generate/callsite.rs", "generate_callsite_precondition_vcs_for_each", Class::BareEntry),
    ("generate/callsite.rs", "generate_callsite_precondition_vcs_attributed", Class::BareEntry),
    ("generate/callsite_replay.rs", "generate_callsite_l0_replay_candidates", Class::BareEntry),
    ("generate/contract_vcs.rs", "generate_v2_contract_vcs_impl", Class::BareEntry),
    ("generate/unwrap_panic.rs", "unwrap_panic_freedom_vcs_with_blocks", Class::BareEntry),
    ("generate/alloc_vcs.rs", "generate_unbounded_allocation_vcs_with_width", Class::BareEntry),
];

fn rust_files(dir: &Path, out: &mut Vec<PathBuf>) {
    for entry in std::fs::read_dir(dir).unwrap_or_else(|e| panic!("read {dir:?}: {e}")) {
        let path = entry.expect("dir entry").path();
        if path.is_dir() {
            rust_files(&path, out);
        } else if path.extension().is_some_and(|x| x == "rs") {
            out.push(path);
        }
    }
}

/// Every spelling that builds the global invariant fact set (or the per-row view of it,
/// `generate::RowGlobalFacts`) at a site: the cached view, the row filter's
/// constructors and the raw builder.
const PRODUCERS: &[&str] = &[
    "build_global_invariant_facts(",
    "row_global_facts_for(",
    "RowGlobalFacts::for_function(",
    "RowGlobalFacts::new(",
    "build_global_invariant_facts_with_congruence_range(",
];

/// The producers' own definitions, (file, top-level `fn`), which compose one another: a
/// producer call inside one of these is the set being BUILT, not a site, and it must be
/// one of the [`COMPOSITION`] edges.
const PRODUCER_FNS: &[(&str, &str)] = &[
    ("generate/value_facts.rs", "build_global_invariant_facts"),
    ("generate/value_facts.rs", "build_global_invariant_facts_with_congruence_range"),
    ("generate/mod.rs", "row_global_facts_for"),
];
/// The file of `impl RowGlobalFacts`, and its methods that compose the set.
const PRODUCER_IMPL_FILE: &str = "generate/value_facts.rs";
const PRODUCER_METHODS: &[&str] = &["for_function", "new", "from_congruence_slice"];

/// Every producer call INSIDE a producer's own body, (file, producer, spelling called),
/// a method named `RowGlobalFacts::<method>`. The skip above is keyed on these edges and
/// no others: a producer call in a producer's body that is not listed here fails the
/// scan, so the skip can hide only the composition stated here. There are TWO
/// functions that build the set, one chain long: the cached view
/// `build_global_invariant_facts` (`Rc<RowGlobalFacts>`, PERF-COMPILER-VCGEN-81) asks
/// the per-scope cache `row_global_facts_for`, which builds `RowGlobalFacts::for_function`
/// once per `FuncAnalysisScope`, which calls the ONE raw builder,
/// `build_global_invariant_facts_with_congruence_range` (the `Vec` and the index range
/// of its element-read congruences). Trust: 2026-11-07 (VCGEN-CENSUS-SITE-REDS-1): a
/// fold of the two at `9db7a252ac` was undone by the PERF-COMPILER-VCGEN-81 merge
/// (`a3c3bf63f1`), which made the first a cached view of the second; this list is
/// what the census checks, so a re-fold or a new edge must restate it here.
const COMPOSITION: &[(&str, &str, &str)] = &[
    ("generate/mod.rs", "row_global_facts_for", "RowGlobalFacts::for_function("),
    (
        "generate/value_facts.rs",
        "RowGlobalFacts::for_function",
        "build_global_invariant_facts_with_congruence_range(",
    ),
    ("generate/value_facts.rs", "build_global_invariant_facts", "row_global_facts_for("),
];

/// The name a line DECLARES (`fn name`, after any visibility/qualifier words), if any.
fn declared_fn(line: &str) -> Option<String> {
    let at = line.find("fn ")?;
    if !line[..at]
        .split_whitespace()
        .all(|w| w.starts_with("pub") || matches!(w, "const" | "async" | "unsafe"))
    {
        return None;
    }
    let name: String =
        line[at + 3..].chars().take_while(|c| c.is_ascii_alphanumeric() || *c == '_').collect();
    (!name.is_empty()).then_some(name)
}

/// Every producer CALL ([`PRODUCERS`]) in `text`, the source of `file` (comment lines
/// and the producers' own definitions skipped), as the name of the last TOP-LEVEL `fn`
/// item (one that starts in column 0) opened before it: a nested `fn` closes before the
/// call that follows it. A call inside a producer's own body (a top-level
/// [`PRODUCER_FNS`] item of its file, or a [`PRODUCER_METHODS`] method of
/// `impl RowGlobalFacts` in [`PRODUCER_IMPL_FILE`]) is that producer composing the set,
/// and is skipped.
fn call_sites(text: &str, file: &str) -> Vec<String> {
    scan(text, file).0
}

/// [`call_sites`], and each composing call it skipped as (producer, spelling called):
/// the producer is the top-level `fn`, or `RowGlobalFacts::<method>` inside
/// `impl RowGlobalFacts`; one entry per [`PRODUCERS`] spelling the line contains.
fn scan(text: &str, file: &str) -> (Vec<String>, Vec<(String, String)>) {
    let mut sites = Vec::new();
    let mut composed = Vec::new();
    let mut current_fn = String::new();
    let mut current_method = String::new();
    let mut in_row_facts_impl = false;
    for line in text.lines() {
        let trimmed = line.trim_start();
        if trimmed.starts_with("//") {
            continue;
        }
        let top_level = trimmed.len() == line.len();
        if top_level && !trimmed.is_empty() && !trimmed.starts_with('}') {
            in_row_facts_impl = trimmed.starts_with("impl RowGlobalFacts");
        }
        if let Some(name) = declared_fn(trimmed) {
            if top_level {
                current_fn = name;
                current_method.clear();
            } else {
                current_method = name;
            }
        }
        if !PRODUCERS.iter().any(|p| trimmed.contains(p)) {
            continue;
        }
        // A producer's own definition line (`fn for_function(`) declares, it does not call.
        if declared_fn(trimmed).is_some_and(|name| {
            PRODUCERS.iter().any(|p| p.trim_end_matches('(').rsplit("::").next() == Some(&name))
        }) {
            continue;
        }
        let composing = (!in_row_facts_impl
            && PRODUCER_FNS.iter().any(|&(f, name)| f == file && name == current_fn))
            || (in_row_facts_impl
                && file == PRODUCER_IMPL_FILE
                && PRODUCER_METHODS.contains(&current_method.as_str()));
        if !composing {
            sites.push(current_fn.clone());
        } else {
            let producer = if in_row_facts_impl {
                format!("RowGlobalFacts::{current_method}")
            } else {
                current_fn.clone()
            };
            for p in PRODUCERS.iter().filter(|p| trimmed.contains(*p)) {
                composed.push((producer.clone(), p.to_string()));
            }
        }
    }
    (sites, composed)
}

#[test]
fn every_global_fact_site_is_classified() {
    let src = Path::new(env!("CARGO_MANIFEST_DIR")).join("src");
    let mut files = Vec::new();
    rust_files(&src, &mut files);
    files.sort();
    assert!(files.len() > 50, "the scan must actually see the sources: {}", files.len());
    let mut found = Vec::new();
    let mut composed = Vec::new();
    let mut producer_files_seen = std::collections::BTreeSet::new();
    for file in &files {
        let text = std::fs::read_to_string(file).expect("readable source");
        let rel = file.strip_prefix(&src).unwrap().to_string_lossy().replace('\\', "/");
        // A `#[cfg(test)]` unit module (`*_tests.rs` or a `*_tests/` child module)
        // conjoins nothing onto a dispatched row: it builds `RowGlobalFacts` over
        // hand-made fact lists to pin the filter.
        if rel.ends_with("_tests.rs") || rel.contains("_tests/") {
            continue;
        }
        if PRODUCER_FNS.iter().any(|&(f, _)| f == rel) {
            producer_files_seen.insert(rel.clone());
        }
        let (sites, edges) = scan(&text, &rel);
        for site in sites {
            found.push((rel.clone(), site));
        }
        for (producer, spelling) in edges {
            composed.push((rel.clone(), producer, spelling));
        }
    }
    let producer_files: std::collections::BTreeSet<String> =
        PRODUCER_FNS.iter().map(|&(f, _)| f.to_string()).collect();
    assert_eq!(producer_files_seen, producer_files, "every producers' file must be scanned");
    composed.sort();
    let mut chain: Vec<(String, String, String)> =
        COMPOSITION.iter().map(|&(f, p, s)| (f.into(), p.into(), s.into())).collect();
    chain.sort();
    assert_eq!(
        composed, chain,
        "a producer call inside a producer's own body is not the listed composition: the \
         skip hides only `COMPOSITION`'s edges, so a call that conjoins the set there is a \
         site to classify, and a new or re-folded producer chain must be restated in \
         `COMPOSITION` (and in the DQ entry that describes how the set is built)"
    );
    found.sort();
    let mut listed: Vec<(String, String)> =
        SITES.iter().map(|(f, s, _)| (f.to_string(), s.to_string())).collect();
    listed.sort();
    assert_eq!(
        found, listed,
        "a `build_global_invariant_facts` call site is not classified (or a classified one \
         is gone): give each site its class, `RowPoint` or `BareEntry`, with the argument \
         this file's header states — the element-read congruence among those facts is a \
         theorem only at ONE point"
    );
    assert_eq!(SITES.iter().filter(|(_, _, c)| *c == Class::RowPoint).count(), 2);
    assert_eq!(SITES.iter().filter(|(_, _, c)| *c == Class::BareEntry).count(), 6);
}

#[test]
fn the_scan_sees_the_calls_it_classifies() {
    let text = "fn a() {\n    let f = build_global_invariant_facts(func);\n}\n\
                // build_global_invariant_facts(func) in a comment\n\
                pub(crate) fn build_global_invariant_facts(func: &F) -> Vec<Formula> {}\n\
                pub(super) fn b() {\n    fn nested() {}\n\
                \x20   let g = crate::generate::build_global_invariant_facts(v);\n}\n";
    assert_eq!(call_sites(text, "x.rs"), vec!["a".to_string(), "b".to_string()]);
    // The spelling every site uses since PERF-COMPILER-VCGEN-72, in a `OnceCell`, a
    // `get_or_insert_with` and a plain `let`, and the test-only constructor.
    let row = "fn c() {\n    let s = shared\n        .get_or_init(|| RowGlobalFacts::for_function(func));\n}\n\
               pub(crate) fn d() {\n    let r = g.get_or_insert_with(|| crate::generate::RowGlobalFacts::for_function(f));\n}\n\
               fn e() {\n    let t = RowGlobalFacts::for_function(func_view);\n    let u = RowGlobalFacts::new(f, v);\n}\n";
    assert_eq!(call_sites(row, "x.rs"), vec!["c", "d", "e", "e"]);
    // The producers' own files: their definitions and their composition of one another
    // are no site, and a call from any other `fn` of those files still is.
    let producers = "pub(crate) fn build_global_invariant_facts(\n\
                     \x20   func: &F,\n) -> Rc<RowGlobalFacts> {\n\
                     \x20   super::row_global_facts_for(func)\n}\n\
                     pub(crate) fn build_global_invariant_facts_with_congruence_range(\n\
                     \x20   func: &F,\n) -> (Vec<Formula>, Range<usize>) {\n\
                     \x20   let mut global_facts = build_min_max_facts(func);\n}\n\
                     pub(crate) struct RowGlobalFacts {}\n\
                     impl RowGlobalFacts {\n\
                     \x20   pub(crate) fn for_function(func: &F) -> Self {\n\
                     \x20       let (facts, range) = build_global_invariant_facts_with_congruence_range(func);\n\
                     \x20   }\n\
                     \x20   #[cfg(test)]\n\
                     \x20   pub(crate) fn new(func: &F, facts: Vec<Formula>) -> Self {}\n\
                     }\n\
                     fn other_lane(func: &F) {\n    let s = build_global_invariant_facts(func);\n}\n";
    assert_eq!(call_sites(producers, "generate/value_facts.rs"), vec!["other_lane"]);
    // What the skip hid is recorded edge by edge, so the census can hold it to
    // `COMPOSITION` (a method as `RowGlobalFacts::<method>`).
    let edge = |p: &str, s: &str| (p.to_string(), s.to_string());
    assert_eq!(
        scan(producers, "generate/value_facts.rs").1,
        vec![
            edge("build_global_invariant_facts", "row_global_facts_for("),
            edge(
                "RowGlobalFacts::for_function",
                "build_global_invariant_facts_with_congruence_range("
            ),
        ]
    );
    // A producer that also conjoins the set where it composes it: the call is skipped as
    // a site but is an edge `COMPOSITION` does not list, so the census still sees it.
    let conjoining = "pub(crate) fn build_global_invariant_facts(\n\
                      \x20   func: &F,\n) -> Rc<RowGlobalFacts> {\n\
                      \x20   let raw = build_global_invariant_facts_with_congruence_range(func);\n\
                      \x20   super::row_global_facts_for(func)\n}\n";
    let (sites, edges) = scan(conjoining, "generate/value_facts.rs");
    assert!(sites.is_empty(), "inside a producer's body the call is no site: {sites:?}");
    assert_eq!(
        edges,
        vec![
            edge(
                "build_global_invariant_facts",
                "build_global_invariant_facts_with_congruence_range("
            ),
            edge("build_global_invariant_facts", "row_global_facts_for("),
        ]
    );
    assert_eq!(
        call_sites(producers, "x.rs"),
        vec![
            "build_global_invariant_facts",
            "build_global_invariant_facts_with_congruence_range",
            "other_lane"
        ],
        "outside the producers' file the same composition counts: the skip is keyed on it"
    );
    let cache = "pub(crate) fn row_global_facts_for(func: &F) -> Rc<RowGlobalFacts> {\n\
                 \x20   let built = Rc::new(RowGlobalFacts::for_function(func));\n}\n\
                 fn lane(func: &F) {\n    let g = row_global_facts_for(func);\n}\n";
    assert_eq!(call_sites(cache, "generate/mod.rs"), vec!["lane"]);
    assert_eq!(
        scan(cache, "generate/mod.rs").1,
        vec![("row_global_facts_for".to_string(), "RowGlobalFacts::for_function(".to_string())]
    );
    assert_eq!(call_sites(cache, "x.rs"), vec!["row_global_facts_for", "lane"]);
}
