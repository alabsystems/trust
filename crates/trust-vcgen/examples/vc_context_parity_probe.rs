//! The VC-context parity probe (T3 L4, "PP" of `docs/design/2026-10-11-t3-l4-commit-plan.md`):
//! over the in-tree fixtures, every row `generate_vcs` emits is interned into one
//! per-function `trust_types::vc_context::VcContext`, and the context is checked against
//! the eager rows. Separate from the C01 row-parity probe, which is never edited.
//!
//! The oracles, each with its row and mismatch counts:
//!
//! * `i1`: the materialized row is the eager row in every field (and in its canonical
//!   JSON, the exact-VC payload's encoding);
//! * `i4`: the row's node count in the context is `query_size` of its formula;
//! * `i5`: the row's digest in the context is `formula_digest` of its formula, and the
//!   same in a second context that interned the function's rows in reverse order;
//! * `sink` (T3 C08s): a context and return-path check, not a per-pass one (both entries
//!   run the same sink and passes, `generate_vcs` with no Spine attempt; the per-pass
//!   parity against the old whole-list code is `row_sink_tests`', and V's against the
//!   parent's pipeline). The generation's sink, writing into a context of the probe's
//!   (`generate_vcs_rows`), returns exactly the rows `generate_vcs` returns, and its
//!   context holds at least one row per returned row, every one checked by the row oracle
//!   with no disagreement (a generation the work meter refused leaves the rows that joined
//!   before the refusal), and the oracle materialized at most one row at a time (a
//!   function whose context disagrees counts one mismatch, row `-`);
//! * `spine` (T3 C08): every Spine row that sink context holds (a block-def row the
//!   generation joined as one) has the node count and the digest of its materialized
//!   formula (I4, I5); its read-back against the eager row is the `sink` oracle's row
//!   oracle count. A `PP-SPINES` line gives the block-def rows, the Spine rows among them,
//!   and each decline; with no Spine row the `spine` oracle checked nothing, and the line
//!   says `VACUOUS` instead of passing for one that held.
//!
//! * `identity` (T3 C09): the function's rows partitioned by row identity in the context
//!   (`VcContext::same_identity`, the Merkle digest selecting the candidates) against their
//!   partition by canonical JSON, the key every exact site of the compiler compares until
//!   C11. Each row counts once; it mismatches when the first row of its canonical class is
//!   not the first of its identity class, so a merge or a split in either direction is
//!   counted. A row with no canonical JSON or no identity counts as a mismatch.
//!
//! The dedup partition and lowering (I3) join at C10.
//!
//! Output: one `PP <oracle> rows=<n> mismatches=<m>` line per oracle, the first mismatches
//! (`PP-MISMATCH <oracle> <fixture> <row> <detail>`), and a verdict line. Exit 0 when no
//! oracle mismatched, 1 when one did, 2 on usage, 3 when no row was checked.
//!
//! Usage: `vc_context_parity_probe [--limit <fixtures>] [--details] <fixture root>...`
//! The default still reads the full census. A limit selects the sorted prefix (across
//! roots in argument order) and prints its scope explicitly. `--details` adds each
//! fixture's recipe counts and each retained context row's root representation/counts;
//! these are diagnostic observations, not additional parity or proof authority.
//!
//! Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.

use std::collections::HashMap;
use std::ffi::OsString;
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::path::{Path, PathBuf};

use trust_types::determinism::query_size;
use trust_types::formula_merkle::{FormulaDigest, formula_digest};
use trust_types::vc_context::{RowFormula, RowId, RowIdentity, VcContext, VcRow};
use trust_types::{
    SourceSpan, VerifiableFunction, VerificationCondition, canonical_digest_json_value,
};
use trust_vcgen::{RecipeCounts, SpineDecline, generate_vcs, generate_vcs_rows, recipe_counts};

const SHOWN: usize = 20;

#[derive(Debug, Default, PartialEq, Eq)]
struct Options {
    roots: Vec<PathBuf>,
    limit: Option<usize>,
    details: bool,
}

impl Options {
    fn parse(args: impl IntoIterator<Item = OsString>) -> Result<Self, &'static str> {
        let mut options = Self::default();
        let mut args = args.into_iter();
        let mut positional = false;
        while let Some(arg) = args.next() {
            if positional {
                options.roots.push(arg.into());
            } else if arg == "--" {
                positional = true;
            } else if arg == "--details" {
                options.details = true;
            } else if arg == "--limit" {
                if options.limit.is_some() {
                    return Err("duplicate --limit");
                }
                let limit = args
                    .next()
                    .and_then(|value| value.to_str().and_then(|value| value.parse().ok()))
                    .filter(|value| *value > 0)
                    .ok_or("--limit requires a positive fixture count")?;
                options.limit = Some(limit);
            } else if arg.to_str().is_some_and(|arg| arg.starts_with('-')) {
                return Err("unknown option (use -- before a root beginning with '-')");
            } else {
                options.roots.push(arg.into());
            }
        }
        if options.roots.is_empty() {
            return Err("at least one fixture root is required");
        }
        Ok(options)
    }
}

fn json_files(root: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = std::fs::read_dir(root) else { return };
    for entry in entries.filter_map(Result::ok) {
        let path = entry.path();
        if path.is_dir() {
            json_files(&path, out);
        } else if path.extension().is_some_and(|x| x == "json") {
            out.push(path);
        }
    }
}

#[derive(Default)]
struct Oracle {
    rows: u64,
    mismatches: u64,
}

struct Report {
    oracles: [(&'static str, Oracle); 6],
    shown: usize,
    /// What the sink contexts' block-def rows became, summed.
    recipes: RecipeCounts,
}

impl Report {
    fn check(
        &mut self,
        slot: usize,
        ok: bool,
        fixture: &str,
        row: impl std::fmt::Display,
        detail: impl FnOnce() -> String,
    ) {
        let Some((name, oracle)) = self.oracles.get_mut(slot) else { return };
        oracle.rows += 1;
        if !ok {
            oracle.mismatches += 1;
            if self.shown < SHOWN {
                self.shown += 1;
                println!("PP-MISMATCH {name} {fixture} {row} {}", detail());
            }
        }
    }
}

/// Whether every field of `a` and `b` is equal, and their canonical JSON too.
fn same_row(a: &VerificationCondition, b: &VerificationCondition) -> bool {
    a.kind == b.kind
        && a.function == b.function
        && a.location == b.location
        && a.formula == b.formula
        && a.contract_metadata == b.contract_metadata
        && a.obligation == b.obligation
        && canonical_digest_json_value(a).ok() == canonical_digest_json_value(b).ok()
}

fn check_function(report: &mut Report, fixture: &str, vcs: &[VerificationCondition]) {
    let mut context = VcContext::new();
    let ids: Vec<_> = vcs.iter().map(|vc| context.push_node_row(vc).unwrap()).collect();
    let mut reversed = VcContext::new();
    let mut reversed_ids: Vec<_> =
        vcs.iter().rev().map(|vc| reversed.push_node_row(vc).unwrap()).collect();
    reversed_ids.reverse();
    for (row, ((id, again), vc)) in ids.iter().zip(&reversed_ids).zip(vcs).enumerate() {
        let materialized = context.materialize(*id);
        let i1 = materialized.as_ref().is_ok_and(|m| same_row(m.vc(), vc));
        report.check(0, i1, fixture, row, || "materialized row differs".to_string());
        let count = context.row_node_count(*id).ok();
        let size = query_size(&[&vc.formula]);
        report.check(1, count == Some(size), fixture, row, || {
            format!("row_node_count {count:?} query_size {size}")
        });
        let digest = context.digest(*id).ok();
        let fresh = formula_digest(&vc.formula).ok();
        let other = reversed.digest(*again).ok();
        report.check(
            2,
            digest.is_some() && digest == fresh && digest == other,
            fixture,
            row,
            || format!("digest {digest:?} fresh {fresh:?} reversed {other:?}"),
        );
    }
    check_identity_partition(report, fixture, &mut context, &ids, vcs);
}

/// The `identity` oracle over one function's rows (module docs): their partition by
/// identity in `context`, where `ids` are their rows, against their partition by canonical
/// JSON.
fn check_identity_partition(
    report: &mut Report,
    fixture: &str,
    context: &mut VcContext,
    ids: &[RowId],
    vcs: &[VerificationCondition],
) {
    let canonical: Vec<Option<serde_json::Value>> =
        vcs.iter().map(|vc| canonical_digest_json_value(vc).ok()).collect();
    let identities: Vec<Option<RowIdentity>> =
        ids.iter().map(|id| context.identity(*id).ok()).collect();
    // Equal canonical JSON implies an equal span, so the span selects the candidates.
    let mut by_span: HashMap<&SourceSpan, Vec<usize>> = HashMap::new();
    let mut by_digest: HashMap<FormulaDigest, Vec<usize>> = HashMap::new();
    for (row, vc) in vcs.iter().enumerate() {
        let first_canonical = canonical[row].as_ref().map(|value| {
            let class = by_span.entry(&vc.location).or_default();
            let found =
                class.iter().copied().find(|&earlier| canonical[earlier].as_ref() == Some(value));
            if found.is_none() {
                class.push(row);
            }
            found.unwrap_or(row)
        });
        let first_identity = identities[row].as_ref().map(|identity| {
            let class = by_digest.entry(identity.digest).or_default();
            let found = class.iter().copied().find(|&earlier| {
                identities[earlier]
                    .as_ref()
                    .is_some_and(|other| context.same_identity(other, identity))
            });
            if found.is_none() {
                class.push(row);
            }
            found.unwrap_or(row)
        });
        let agrees = first_canonical.is_some() && first_canonical == first_identity;
        report.check(5, agrees, fixture, row, || {
            format!("canonical class {first_canonical:?} identity class {first_identity:?}")
        });
    }
}

/// The `sink` oracle over one function: `generate_vcs_rows` into a fresh context against
/// `vcs`, the rows `generate_vcs` returned.
fn check_sink(
    report: &mut Report,
    fixture: &str,
    func: &VerifiableFunction,
    vcs: &[VerificationCondition],
    details: bool,
) {
    let mut sink = VcContext::new();
    let Ok(rows) = catch_unwind(AssertUnwindSafe(|| generate_vcs_rows(func, &mut sink))) else {
        report.check(3, false, fixture, "-", || "generate_vcs_rows panicked".to_string());
        return;
    };
    if rows.len() != vcs.len() {
        report.check(3, false, fixture, "-", || {
            format!("{} rows through the sink, {} from generate_vcs", rows.len(), vcs.len())
        });
        return;
    }
    for (row, (got, vc)) in rows.iter().zip(vcs).enumerate() {
        report.check(3, same_row(got, vc), fixture, row, || "the sink's row differs".to_string());
    }
    let parity = sink.parity(trust_types::vc_context::Oracle::Row);
    let stats = sink.stats();
    let agrees = parity.mismatches == 0
        && parity.rows == stats.rows
        && stats.rows >= vcs.len() as u64
        && stats.trees_alive == 0
        && stats.trees_alive_max <= 1;
    if !agrees {
        report.check(3, false, fixture, "-", || {
            format!(
                "context rows={} parity={parity:?} trees_alive={} trees_alive_max={}",
                stats.rows, stats.trees_alive, stats.trees_alive_max
            )
        });
    }
    report.recipes.absorb(&recipe_counts(&sink));
    check_spines(report, fixture, &mut sink);
    if details {
        describe_sink(fixture, func, vcs.len(), &mut sink);
    }
}

/// Describe the actual retained rows after the unchanged parity checks. Context rows
/// can include intermediate rows, so their indices are explicitly not eager-row IDs.
fn describe_sink(
    fixture: &str,
    func: &VerifiableFunction,
    eager_rows: usize,
    sink: &mut VcContext,
) {
    let recipes = recipe_counts(sink);
    let ids: Vec<_> = sink.row_ids().collect();
    let declines: HashMap<_, _> =
        SpineDecline::ALL.iter().map(|reason| (reason.name(), recipes.declined(*reason))).collect();
    println!(
        "PP-FIXTURE {}",
        serde_json::json!({
            "fixture": fixture, "function": func.def_path, "eager_rows": eager_rows,
            "context_rows": ids.len(), "recorded": recipes.recorded,
            "block_def_rows": recipes.block_def_rows, "spine_rows": recipes.spine_rows,
            "declines": declines,
        })
    );
    for (index, id) in ids.into_iter().enumerate() {
        let row = sink.row(id).expect("the context's own row");
        let kind = format!("{:?}", row.kind());
        let root = row.formula();
        let (representation, candidates, kept) = match root {
            RowFormula::Node(_) => ("node", None, None),
            RowFormula::Spine(id) => {
                let spine = *sink.spine(id).expect("the row's own spine");
                (
                    "spine",
                    sink.seq_nodes(spine.candidates).ok().map(|nodes| nodes.len()),
                    sink.kept(&spine).ok().map(|nodes| nodes.len()),
                )
            }
        };
        let materialized = sink.materialize(id).expect("the context's own row");
        let formula = serde_json::to_value(&materialized.vc().formula).expect("a formula");
        let formula_root = formula.as_object().and_then(|value| value.keys().next()).cloned();
        let location = materialized.vc().location.clone();
        drop(materialized);
        println!(
            "PP-ROW {}",
            serde_json::json!({
                "fixture": fixture, "context_row": index, "kind": kind,
                "representation": representation, "candidates": candidates, "kept": kept,
                "formula_root": formula_root, "location": location,
                "nodes": sink.row_node_count(id).ok(),
                "digest": format!("{:?}", sink.digest(id)),
            })
        );
    }
}

/// The `spine` oracle over one sink context: each Spine row's node count and digest are
/// its materialized formula's.
fn check_spines(report: &mut Report, fixture: &str, sink: &mut VcContext) {
    let ids: Vec<RowId> = sink.row_ids().collect();
    for (row, id) in ids.into_iter().enumerate() {
        if !matches!(sink.row(id).map(VcRow::formula), Ok(RowFormula::Spine(_))) {
            continue;
        }
        let Ok(materialized) = sink.materialize(id) else {
            report.check(4, false, fixture, row, || "the Spine row does not read back".into());
            continue;
        };
        let formula = materialized.vc().formula.clone();
        drop(materialized);
        let count = sink.row_node_count(id).ok();
        let size = query_size(&[&formula]);
        let digest = sink.digest(id).ok();
        let fresh = formula_digest(&formula).ok();
        let ok = count == Some(size) && digest.is_some() && digest == fresh;
        report.check(4, ok, fixture, row, || {
            format!("row_node_count {count:?} query_size {size} digest {digest:?} fresh {fresh:?}")
        });
    }
}

fn main() {
    let options = Options::parse(std::env::args_os().skip(1)).unwrap_or_else(|error| {
        eprintln!("{error}\nusage: vc_context_parity_probe [--limit <fixtures>] [--details] <fixture root>...");
        std::process::exit(2)
    });
    // A generator panic skips the fixture (the row-parity probe reports those).
    std::panic::set_hook(Box::new(|_| {}));
    let mut report = Report {
        oracles: [
            ("i1", Oracle::default()),
            ("i4", Oracle::default()),
            ("i5", Oracle::default()),
            ("sink", Oracle::default()),
            ("spine", Oracle::default()),
            ("identity", Oracle::default()),
        ],
        shown: 0,
        recipes: RecipeCounts::default(),
    };
    let (mut fixtures, mut skipped) = (0usize, 0usize);
    let mut selected = Vec::new();
    for root in &options.roots {
        let mut files = Vec::new();
        json_files(root, &mut files);
        files.sort();
        selected.extend(files.into_iter().map(|path| (root, path)));
    }
    if let Some(limit) = options.limit {
        println!(
            "PP-SCOPE full_census=false limit={limit} available={} selected={}",
            selected.len(),
            selected.len().min(limit)
        );
        selected.truncate(limit);
    }
    for (root, path) in selected {
        let fixture = path.strip_prefix(root).unwrap_or(&path).display().to_string();
        fixtures += 1;
        let parsed = std::fs::read_to_string(&path)
            .ok()
            .and_then(|text| serde_json::from_str::<VerifiableFunction>(&text).ok());
        let Some(func) = parsed else {
            skipped += 1;
            if options.details {
                println!(
                    "PP-SKIP {}",
                    serde_json::json!({"fixture": fixture, "reason": "read-or-parse"})
                );
            }
            continue;
        };
        let Ok(vcs) = catch_unwind(AssertUnwindSafe(|| generate_vcs(&func))) else {
            skipped += 1;
            if options.details {
                println!(
                    "PP-SKIP {}",
                    serde_json::json!({"fixture": fixture, "reason": "generate_vcs-panic"})
                );
            }
            continue;
        };
        if catch_unwind(AssertUnwindSafe(|| check_function(&mut report, &fixture, &vcs))).is_err() {
            println!("PP-MISMATCH context {fixture} - the check panicked");
            report.oracles[0].1.mismatches += 1;
        }
        check_sink(&mut report, &fixture, &func, &vcs, options.details);
    }
    let mut mismatches = 0;
    let mut rows = 0;
    for (name, oracle) in &report.oracles {
        println!("PP {name} rows={} mismatches={}", oracle.rows, oracle.mismatches);
        mismatches += oracle.mismatches;
        rows += oracle.rows;
    }
    println!("PP fixtures={fixtures} skipped={skipped}");
    let declines: Vec<String> = SpineDecline::ALL
        .iter()
        .map(|reason| format!("{}={}", reason.name(), report.recipes.declined(*reason)))
        .collect();
    let vacuous = if report.recipes.spine_rows == 0 { " VACUOUS: no Spine row" } else { "" };
    println!(
        "PP-SPINES recorded={} block_def_rows={} spine_rows={} {}{vacuous}",
        report.recipes.recorded,
        report.recipes.block_def_rows,
        report.recipes.spine_rows,
        declines.join(" ")
    );
    if mismatches > 0 {
        println!("VC CONTEXT PARITY: {mismatches} mismatch(es)");
        std::process::exit(1);
    }
    if rows == 0 {
        println!("VC CONTEXT PARITY: COULD NOT RUN — no row was checked");
        std::process::exit(3);
    }
    println!("VC CONTEXT PARITY: 0 mismatches");
}

#[cfg(test)]
mod option_tests {
    use super::*;

    fn parse(args: &[&str]) -> Result<Options, &'static str> {
        Options::parse(args.iter().map(OsString::from))
    }

    #[test]
    fn the_default_is_an_unlimited_census_in_root_argument_order() {
        assert_eq!(
            parse(&["tests", "other"]).unwrap(),
            Options { roots: vec!["tests".into(), "other".into()], ..Options::default() }
        );
    }

    #[test]
    fn explicit_limits_are_validated_and_literal_roots_are_preserved() {
        assert_eq!(
            parse(&["--details", "--limit", "400", "--", "-tests"]).unwrap(),
            Options { roots: vec!["-tests".into()], limit: Some(400), details: true }
        );
        for args in [
            vec![],
            vec!["--limit", "0", "tests"],
            vec!["--limit", "-1", "tests"],
            vec!["--limit", "400"],
            vec!["--limit", "2", "--limit", "3", "tests"],
            vec!["--unknown", "tests"],
        ] {
            assert!(parse(&args).is_err(), "{args:?}");
        }
    }
}
