//! DIFFERENTIAL PARITY of the SSA statement-version oracle (`version_ssa`,
//! `block_writes`, `cfg_index`, `rebind_index`) against the retired dense-map oracle
//! it replaced (`legacy_version_oracle`: two whole-CFG reaching-version fixpoints).
//!
//! The retired oracle is the specification: every version token decides which SMT
//! variable a read names, so ONE differing token can merge a stale fact into a live
//! read (a false PROVE) or split a live one (a false FAIL). These tests require the
//! two oracles to agree
//!
//!  * on the whole `generate_vcs` output, BYTE FOR BYTE (the full `Debug` rendering of
//!    every VC), generated once per oracle — over every generated family at small
//!    sizes, over every extracted body in `tests/data` and `tests/fixtures`, and over
//!    seeded random CFGs (`version_ssa_random_tests`);
//!  * on every `(block, statement index, name)` query the rename can make, for every
//!    tracked name and projections / look-alikes of it (the per-query differential
//!    `StmtVersionCtx` runs under `cfg(test)`);
//!  * on the raw reaching sets, the gen-sets and the OUT tokens.
//!
//! (Every unit test of this crate additionally runs with the per-query differential
//! on — see `StmtVersionCtx::build` — so the whole suite is a differential over every
//! body it builds.)

use std::collections::BTreeSet;

use trust_types::fx::FxHashMap;
use trust_types::{BlockId, Operand, Rvalue, Statement, Terminator, VerifiableFunction};

use super::legacy_version_oracle::{
    LegacyStmtVersions, legacy_gen_out, with_legacy_answers, without_differential,
};
use super::{StmtVersionCtx, generate_vcs, version_ssa_families as families};

/// The WHOLE VC, every field (`Debug`), not a projection of it: a token difference in
/// any field — a wrapper's facts, a contract's rendering — is a difference.
fn render(vcs: &[trust_types::VerificationCondition]) -> Vec<String> {
    vcs.iter().map(|vc| format!("{vc:?}")).collect()
}

/// `generate_vcs` once with every oracle query answered by the retired oracle, once
/// by the SSA oracle; the rendered outputs must be byte-identical.
fn assert_generation_identical(func: &VerifiableFunction) -> usize {
    let legacy = with_legacy_answers(|| render(&generate_vcs(func)));
    let ssa = render(&generate_vcs(func));
    assert_eq!(
        legacy.len(),
        ssa.len(),
        "`{}`: VC count differs between the oracles",
        func.def_path
    );
    for (i, (a, b)) in legacy.iter().zip(&ssa).enumerate() {
        assert_eq!(
            a, b,
            "`{}`: VC #{i} differs between the retired and the SSA oracle",
            func.def_path
        );
    }
    ssa.iter().filter(|line| line.contains('#')).count()
}

#[test]
fn every_family_generates_byte_identical_vcs() {
    let mut versioned_lines = 0usize;
    let mut vcs = 0usize;
    for n in [1usize, 2, 3, 5, 8, 12] {
        for func in families::all_families(n) {
            versioned_lines += assert_generation_identical(&func);
            vcs += generate_vcs(&func).len();
        }
    }
    assert!(vcs > 50, "the families generate almost no VCs ({vcs}); the comparison is vacuous");
    assert!(
        versioned_lines > 10,
        "no generated VC carries a version token; the comparison is vacuous"
    );
}

/// Every JSON-serialised `VerifiableFunction` (or list of them) under the crate's
/// test data directories.
pub(super) fn corpus() -> Vec<(String, VerifiableFunction)> {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests");
    let mut out = Vec::new();
    for dir in ["data", "fixtures"] {
        let Ok(entries) = std::fs::read_dir(root.join(dir)) else { continue };
        let mut paths: Vec<std::path::PathBuf> = entries.flatten().map(|e| e.path()).collect();
        paths.sort();
        for path in paths {
            if path.extension().is_none_or(|e| e != "json") {
                continue;
            }
            let Ok(text) = std::fs::read_to_string(&path) else { continue };
            let label =
                path.file_name().map(|f| f.to_string_lossy().to_string()).unwrap_or_default();
            if let Ok(func) = serde_json::from_str::<VerifiableFunction>(&text) {
                out.push((label, func));
            } else if let Ok(funcs) = serde_json::from_str::<Vec<VerifiableFunction>>(&text) {
                for (i, func) in funcs.into_iter().enumerate() {
                    out.push((format!("{label}#{i}"), func));
                }
            }
        }
    }
    out
}

#[test]
fn the_extracted_corpus_generates_byte_identical_vcs() {
    let corpus = corpus();
    assert!(corpus.len() >= 60, "the extracted corpus shrank to {} bodies", corpus.len());
    let mut versioned_lines = 0usize;
    for (label, func) in &corpus {
        let lines = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            assert_generation_identical(func)
        }));
        match lines {
            Ok(n) => versioned_lines += n,
            Err(payload) => std::panic::resume_unwind(Box::new(format!(
                "{label}: {}",
                payload
                    .downcast_ref::<String>()
                    .cloned()
                    .or_else(|| payload.downcast_ref::<&str>().map(|s| s.to_string()))
                    .unwrap_or_default()
            ))),
        }
    }
    assert!(
        versioned_lines > 100,
        "the corpus carries almost no version tokens ({versioned_lines})"
    );
}

/// Names a statement or terminator reads or writes, spelled as the rename sees them.
fn place_names(func: &VerifiableFunction) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    let mut add = |p: &trust_types::Place| {
        out.insert(crate::place_to_var_name(func, p));
    };
    let op = |o: &Operand, add: &mut dyn FnMut(&trust_types::Place)| {
        if let Operand::Copy(p) | Operand::Move(p) = o {
            add(p);
        }
    };
    for b in &func.body.blocks {
        for s in &b.stmts {
            if let Statement::Assign { place, rvalue, .. } = s {
                add(place);
                match rvalue {
                    Rvalue::Use(o) | Rvalue::Cast(o, _) | Rvalue::UnaryOp(_, o) => op(o, &mut add),
                    Rvalue::BinaryOp(_, a, c) | Rvalue::CheckedBinaryOp(_, a, c) => {
                        op(a, &mut add);
                        op(c, &mut add);
                    }
                    Rvalue::Ref { place, .. } => add(place),
                    _ => {}
                }
            }
        }
        match &b.terminator {
            Terminator::Call { args, dest, .. } => {
                for a in args {
                    op(a, &mut add);
                }
                add(dest);
            }
            Terminator::Assert { cond, .. } | Terminator::SwitchInt { discr: cond, .. } => {
                op(cond, &mut add);
            }
            Terminator::Drop { place, .. } => add(place),
            _ => {}
        }
    }
    out
}

/// Every name the rename could ask about: the tracked names, every place name, and
/// projections, prefixes, derived and look-alike spellings of each.
fn probes(func: &VerifiableFunction, sv: &StmtVersionCtx) -> Vec<String> {
    let mut base: BTreeSet<String> = sv.ssa().tracked_names().into_iter().collect();
    base.extend(place_names(func));
    let mut out = base.clone();
    for n in &base {
        for step in [".0", "*", "[_1]", "[0]", "@1.0", "__slice_len", "x"] {
            out.insert(format!("{n}{step}"));
        }
        for (i, c) in n.char_indices() {
            if matches!(c, '.' | '[' | '*' | '@') {
                out.insert(n[..i].to_string());
            }
        }
    }
    out.insert("unrelated".into());
    out.into_iter().collect()
}

/// Every `(block, statement index, name)`, the entry-only gate, and the
/// may-reassigned probe: the per-query differential inside `StmtVersionCtx` asserts
/// each answer equal to the retired oracle's.
#[test]
fn every_point_and_name_matches_the_retired_oracle() {
    let mut queries = 0usize;
    let mut versioned = 0usize;
    for n in [1usize, 3] {
        for func in families::all_families(n) {
            let sv = StmtVersionCtx::build(&func);
            let probes = probes(&func, &sv);
            for b in &func.body.blocks {
                for name in &probes {
                    for i in 0..=b.stmts.len() + 1 {
                        versioned +=
                            usize::from(sv.version_token_at(&func, b.id, i, name).is_some());
                        queries += 1;
                    }
                    let _ = sv.full_graph_union_is_entry_only(b.id, name);
                    let _ = sv.may_reassigned_rebinds(b.id, name);
                }
            }
            // Out-of-range blocks answer as the retired maps did (no entry).
            let _ = sv.version_token_at(&func, BlockId(func.body.blocks.len()), 0, "x");
            assert!(!sv.full_graph_union_is_entry_only(BlockId(func.body.blocks.len()), "x"));
        }
    }
    assert!(queries > 10_000 && versioned > 1_000, "too few queries: {queries}/{versioned}");
}

/// THE REBINDER TREE at depth (`version_ssa`, REBINDER UNIONS). A read whose
/// rebinders are many — `self` against every field — is answered through a balanced
/// tree of group subjects; the families' sizes above build trees at most two deep.
/// Here the reads of every local and place are compared, as exact SETS (the retired
/// spelling at every length), with the `#e` gate and the may-reassigned kill, against
/// the retired oracle at sizes whose `self` trees are 3 to 6 deep: defs of a few
/// members at a time along a chain (`confined_store_blocks`), in one block
/// (`confined_store_one_block`), around a cycle of joins (`confined_store_loop`) and
/// under refined havocs (`shared_reborrow_calls`).
#[test]
fn rebinder_tree_unions_match_the_retired_oracle_at_depth() {
    let (mut compared, mut joined) = (0usize, 0usize);
    for n in [5usize, 16, 33] {
        for func in [
            families::confined_store_blocks(n),
            families::confined_store_one_block(n),
            families::confined_store_loop(n),
            families::shared_reborrow_calls(n),
        ] {
            let (c, j) = assert_rebinder_unions_match(&func);
            compared += c;
            joined += j;
        }
    }
    assert!(
        compared > 5_000 && joined > 500,
        "too few rebinder unions compared ({compared}) or joined ({joined})"
    );
}

/// The reads of every local and place of `func` at every block, as exact SETS (the
/// retired spelling at every length), with the `#e` gate and the may-reassigned
/// kill, against the retired oracle. Returns (reads compared, reads whose answer is
/// a spelled set).
fn assert_rebinder_unions_match(func: &VerifiableFunction) -> (usize, usize) {
    let (mut compared, mut joined) = (0usize, 0usize);
    let (sv, legacy) =
        without_differential(|| (StmtVersionCtx::build(func), LegacyStmtVersions::build(func)));
    let mut names = place_names(func);
    for l in &func.body.locals {
        let base = trust_types::Place { local: l.index, projections: Vec::new() };
        names.insert(crate::place_to_var_name(func, &base));
    }
    for b in &func.body.blocks {
        for name in &names {
            let (got, want) = without_differential(|| {
                (
                    sv.ssa().inter_block_token_retired(b.id.0, name),
                    legacy.inter_block_token_retired(b.id, name),
                )
            });
            assert_eq!(got, want, "`{}`: `{name}` at {:?}", func.def_path, b.id);
            joined += usize::from(got.is_some_and(|t| t.contains('_')));
            let (gate, want_gate) = without_differential(|| {
                (
                    sv.full_graph_union_is_entry_only(b.id, name),
                    legacy.full_graph_union_is_entry_only(b.id, name),
                )
            });
            assert_eq!(gate, want_gate, "`{}`: #e gate of `{name}` at {:?}", func.def_path, b.id);
            let (kill, want_kill) = without_differential(|| {
                (sv.may_reassigned_rebinds(b.id, name), legacy.may_reassigned_rebinds(b.id, name))
            });
            assert_eq!(kill, want_kill, "`{}`: kill of `{name}` at {:?}", func.def_path, b.id);
            compared += 1;
        }
    }
    (compared, joined)
}

/// A GROUP's def lists must hold every def site of its members (`version_ssa`,
/// REBINDER UNIONS: a superset is sound, a missing site is the false-accept
/// direction). A group's PART exclusion is the INTERSECTION of its children's — the
/// classes that exclude EVERY havoc member. Here the read `p*.0[_2]` (`(*p).a[j]`)
/// has two havoc rebinders, the pointer `p` and the index fallback `_2` of the
/// borrowed `j` (`families::confined_store_index_havoc`). The confined store `(*p).b =
/// 5` in one arm of a diamond is a PART block whose class excludes `p` alone: it
/// defines `_2` and not `p`, so the join's answer is `{s0_*, s1_0}` (the entry
/// block's confined store through `q`, which defines both, and the arm's store).
/// With `p` borrowed first, `p` is the root's FIRST child and `_2` the second: taking
/// the first child's exclusion alone (or the union of both) drops the arm's store
/// from the group, and the join answers `{s0_*}` — a stale version of `(*p).a[j]`
/// after `j` may have changed. The other order is the mirror image (it catches the
/// second child's exclusion alone, and the union again).
#[test]
fn a_group_keeps_the_part_defs_of_either_childs_havoc_members() {
    for base_first in [true, false] {
        let func = families::confined_store_index_havoc(base_first);
        let (compared, _) = assert_rebinder_unions_match(&func);
        assert!(compared > 10, "`{}`: too few reads compared ({compared})", func.def_path);
        let sv = without_differential(|| StmtVersionCtx::build(&func));
        let read = "p*.0[_2]";
        let want: &[&str] = if base_first { &["p", "_2"] } else { &["_2", "p"] };
        assert_eq!(
            without_differential(|| sv.ssa().rebinder_names(read)),
            want,
            "`{}`: the rebinder tree of `{read}` is not the shape this test is about",
            func.def_path
        );
        assert_eq!(
            without_differential(|| sv.ssa().inter_block_token_retired(2, read)).as_deref(),
            Some(if base_first { "s0_2_s1_0" } else { "s0_1_s1_0" }),
            "`{}`: `{read}` at the join",
            func.def_path
        );
        assert_generation_identical(&func);
    }
}

/// The raw reaching sets: for every block and tracked name, the SSA oracle's set is
/// the retired fixpoint's `IN[b][k]`; and the two track the same name universe.
#[test]
fn reaching_sets_match_the_retired_fixpoint() {
    let mut sets = 0usize;
    for n in [1usize, 2, 4, 7] {
        for func in families::all_families(n) {
            let sv = StmtVersionCtx::build(&func);
            let legacy = LegacyStmtVersions::build(&func);
            let legacy_names: BTreeSet<String> =
                legacy.entry_map().values().flat_map(|em| em.keys().cloned()).collect();
            assert_eq!(
                legacy_names.into_iter().collect::<Vec<_>>(),
                sv.ssa().tracked_names(),
                "`{}`: tracked name universes differ",
                func.def_path
            );
            for b in &func.body.blocks {
                let em = legacy.entry_map().get(&b.id).cloned().unwrap_or_default();
                for k in sv.ssa().tracked_names() {
                    let want = em.get(&k).cloned().unwrap_or_default();
                    assert_eq!(
                        sv.ssa().entry_tokens(b.id.0, &k),
                        want,
                        "`{}`: IN[{:?}][{k}] differs",
                        func.def_path,
                        b.id
                    );
                    sets += 1;
                }
            }
        }
    }
    assert!(sets > 1_000, "too few sets compared: {sets}");
}

/// The write index's gen-sets are `block_written_names` and its OUT tokens are the
/// retired `gen_out` scan, block by block, name by name.
#[test]
fn gen_sets_and_out_tokens_match_the_retired_precompute() {
    let mut checked = 0usize;
    let mut bodies: Vec<VerifiableFunction> =
        [1usize, 2, 5].into_iter().flat_map(families::all_families).collect();
    bodies.extend(corpus().into_iter().map(|(_, f)| f).take(120));
    for func in &bodies {
        let sv = StmtVersionCtx::build(func);
        let legacy = legacy_gen_out(func).expect("no budget installed in parity tests");
        for (b, block) in func.body.blocks.iter().enumerate() {
            let got: FxHashMap<String, String> = sv
                .ssa()
                .writes()
                .gen_with_tokens(b)
                .into_iter()
                .map(|(name, tok)| {
                    let tok = match tok {
                        Some(j) => format!("s{}_{j}", block.id.0),
                        None => format!("s{}_t", block.id.0),
                    };
                    (name, tok)
                })
                .collect();
            let names: BTreeSet<&String> = got.keys().collect();
            let want_names: BTreeSet<&String> = legacy[b].keys().collect();
            assert_eq!(names, want_names, "`{}`: gen-set of bb{b} differs", func.def_path);
            for (name, tok) in &got {
                assert_eq!(
                    Some(tok),
                    legacy[b].get(name),
                    "`{}`: OUT token of `{name}` at bb{b} differs",
                    func.def_path
                );
                checked += 1;
            }
        }
    }
    assert!(checked > 1_000, "too few gen entries compared: {checked}");
}

/// An oracle whose write index was built AFTER the ambient verify budget tripped
/// may carry SHORT gen-sets: the per-statement definition extraction it is built from
/// polls the budget and hands back fewer names on a trip. Two answers must then fail
/// closed, as the retired oracle's did:
///
///  * the `#e` mint gate answers `false` (the retired gate answered `false` whenever
///    its fixpoint had not converged), and
///  * the statement gate does not trust its synthetic-name superset — it recomputes
///    the exact prefix, which is what the retired gate always did.
#[test]
fn an_oracle_built_after_a_budget_trip_fails_closed() {
    use trust_types::verify_budget::VerifyBudgetGuard;
    let mut entry_only_before = 0usize;
    let (mut fallbacks_normal, mut fallbacks_tripped) = (0u64, 0u64);
    let sweep = |func: &VerifiableFunction, sv: &StmtVersionCtx, names: &BTreeSet<String>| {
        crate::fn_memo::reset_analysis_memo_stats();
        for b in &func.body.blocks {
            for n in names {
                let _ = sv.version_token_at(func, b.id, b.stmts.len(), n);
            }
        }
        crate::fn_memo::analysis_memo_stats().gate_fallbacks
    };
    for func in families::all_families(3) {
        let names = place_names(&func);
        // The control: a fresh oracle under no budget.
        let normal = StmtVersionCtx::build(&func);
        let entry_only: Vec<(BlockId, String)> = func
            .body
            .blocks
            .iter()
            .flat_map(|b| names.iter().map(move |n| (b.id, n.clone())))
            .filter(|(b, n)| normal.full_graph_union_is_entry_only(*b, n))
            .collect();
        entry_only_before += entry_only.len();
        fallbacks_normal += sweep(&func, &normal, &names);

        // The same body, the oracle built under a budget whose deadline has passed.
        let guard = VerifyBudgetGuard::install(Some(std::time::Instant::now()), u64::MAX);
        assert!(trust_types::verify_budget::exhausted_readonly());
        let tripped = StmtVersionCtx::build(&func);
        for (b, n) in &entry_only {
            assert!(
                !tripped.full_graph_union_is_entry_only(*b, n),
                "`{}`: the `#e` gate minted `{n}` at {b:?} from an oracle built after a trip",
                func.def_path
            );
        }
        fallbacks_tripped += sweep(&func, &tripped, &names);
        drop(guard);
    }
    assert!(entry_only_before > 20, "vacuous: {entry_only_before} entry-only reads");
    assert!(
        fallbacks_tripped > fallbacks_normal,
        "after a trip the gate must stop trusting the extracted superset and recompute the \
         exact prefix ({fallbacks_normal} exact prefixes normally, {fallbacks_tripped} after a trip)"
    );
}
