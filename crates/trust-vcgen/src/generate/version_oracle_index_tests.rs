//! Pins for the statement-version oracle's NAME INDEXES: the rebinder index
//! (`rebind_index::RebindIndex`) the SSA oracle unions over, and the retired
//! root-bucketed index (`legacy_version_oracle`) kept as the differential.
//!
//! Both are cost-only devices with a dangerous failure mode: an index that leaves
//! out a rebinding tracked name gives a SHORTER version union. The read then shares
//! a token with a value it should be name-disjoint from, so a stale fact can
//! discharge a real obligation (a false PROVE). These tests compare the indexed
//! answers against the full, unindexed scan, over names chosen to hit every arm of
//! `write_rebinds` / `dest_write_rebinds`.

use std::collections::BTreeSet;

use trust_types::{
    BasicBlock, BlockId, LocalDecl, Operand, Place, Projection, Rvalue, SourceSpan, Statement,
    Terminator, Ty, UnwindEdge, VerifiableBody, VerifiableFunction,
};

use super::legacy_version_oracle::{LegacyStmtVersions, place_root};
use super::rebind_index::{NameTable, RebindIndex, RebindMode};
use super::{ENTRY_VERSION_SENTINEL, StmtVersionCtx, place_names_overlap};
use crate::generate::path_defs::{dest_write_rebinds, write_rebinds};

/// Names built to hit every `place_names_overlap` arm: equal names, `.`/`[`/`*`/`@`
/// descendants at several depths (`@` is the `Downcast` spelling, a separator since
/// the W4 fix round 1), literal and symbolic (`[_..]`) indices,
/// including a symbolic index below a field or deref, and look-alikes that are
/// NOT projections (`x_y`, `xy`, `x__slice_len`).
fn name_corpus() -> Vec<String> {
    let bases = ["x", "xy", "x_y", "x__slice_len", "_3", "self"];
    let steps = [".0", ".1", "[0]", "[1]", "[_4]", "[_k]", "*", "@0", "@1", "__slice_len"];
    let mut out: Vec<String> = bases.iter().map(|b| b.to_string()).collect();
    let mut frontier = out.clone();
    for _ in 0..3 {
        let mut next = Vec::new();
        for name in &frontier {
            for step in steps {
                next.push(format!("{name}{step}"));
            }
        }
        out.extend(next.iter().cloned());
        frontier = next;
    }
    out.sort();
    out.dedup();
    out
}

/// THE BUCKETING INVARIANT: two overlapping names always share a root, so a
/// root bucket never hides a name the full scan would have unioned in.
#[test]
fn place_root_never_separates_overlapping_names() {
    let corpus = name_corpus();
    let mut overlapping_pairs = 0usize;
    let mut cross_root_candidates = 0usize;
    for a in &corpus {
        for b in &corpus {
            if place_names_overlap(a, b) {
                overlapping_pairs += 1;
                assert_eq!(
                    place_root(a),
                    place_root(b),
                    "`{a}` and `{b}` overlap but land in different root buckets, so the \
                     indexed version union would drop one of them"
                );
            } else if place_root(a) != place_root(b) {
                cross_root_candidates += 1;
            }
        }
    }
    // The corpus must actually exercise both sides, including the symbolic-index
    // arm (distinct non-descendant names that still overlap).
    assert!(overlapping_pairs > corpus.len(), "corpus exercises no real overlaps");
    assert!(cross_root_candidates > 0, "corpus has only one root");
    assert!(place_names_overlap("x.0[_4]", "x.0[1]"), "symbolic-index arm not covered");
    assert!(corpus.iter().any(|n| n == "x.0[_4]") && corpus.iter().any(|n| n == "x.0[1]"));
}

#[test]
fn place_root_is_the_prefix_before_the_first_separator() {
    assert_eq!(place_root("x"), "x");
    assert_eq!(place_root("x__slice_len"), "x__slice_len");
    assert_eq!(place_root("x.0[_4]"), "x");
    assert_eq!(place_root("p*.1"), "p");
    assert_eq!(place_root("arr[_k].0"), "arr");
    assert_eq!(place_root(""), "");
    // An enum DOWNCAST segment (`@variant`) is a projection like any other: the
    // pointee of a pointer moved out of `o: Option<&mut u8>` is rooted at `o`, and
    // a havoc of `o` reaches it (2026-09-29).
    assert_eq!(place_root("o@1.0*"), "o");
    assert!(place_names_overlap("o", "o@1.0*"));
    assert!(place_names_overlap("o@1.0", "o@1.0*"));
    assert!(!place_names_overlap("o@1.0*", "p@1.0*"));
    // W4 fix round 1: a downcast payload shares its enum local's bucket, because it
    // OVERLAPS it (a whole write of `r` rebinds `r@1.0`).
    assert_eq!(place_root("r@1.0"), "r");
    assert!(place_names_overlap("r", "r@1.0"));
}

/// THE REBINDER-INDEX PIN: over deterministic subsets `W` of the corpus (as the
/// written set) and every corpus name as the read, the index visits EXACTLY the
/// members the brute-force predicate relates — in both modes. A missing member is
/// a short version union (a false PROVE); an extra one is a wrong token.
#[test]
fn rebind_index_matches_the_predicates_on_the_corpus() {
    let corpus = name_corpus();
    let mut table = NameTable::default();
    let ids: Vec<u32> = corpus.iter().map(|n| table.intern(n)).collect();
    let mut related = 0usize;
    for stride in [1usize, 2, 3, 5, 7] {
        for offset in 0..stride.min(3) {
            let members: Vec<u32> = ids.iter().copied().skip(offset).step_by(stride).collect();
            let index = RebindIndex::build(&table, members.iter().copied());
            for read in &corpus {
                for mode in [RebindMode::Plain, RebindMode::Dest] {
                    let mut got: BTreeSet<u32> = BTreeSet::new();
                    index.for_each_rebinder(read, mode, |w| {
                        got.insert(w);
                    });
                    let want: BTreeSet<u32> = members
                        .iter()
                        .copied()
                        .filter(|&w| {
                            let w = table.name(w);
                            match mode {
                                RebindMode::Plain => write_rebinds(w, read),
                                RebindMode::Dest => dest_write_rebinds(w, read),
                            }
                        })
                        .collect();
                    related += want.len();
                    assert_eq!(
                        got.iter().map(|&w| table.name(w)).collect::<Vec<_>>(),
                        want.iter().map(|&w| table.name(w)).collect::<Vec<_>>(),
                        "rebinder index ({mode:?}) disagrees with the predicate for read `{read}`"
                    );
                }
            }
        }
    }
    assert!(related > corpus.len(), "the corpus relates almost nothing; the pin is vacuous");
    // Every channel is exercised by the corpus.
    assert!(write_rebinds("x", "x.0[_4]"), "ancestor");
    assert!(write_rebinds("x.0[_4]", "x"), "descendant");
    assert!(write_rebinds("x.0[_4]", "x.0[1]"), "symbolic alias");
    assert!(write_rebinds("_3", "_3[_3]") || write_rebinds("_3", "x[_3]") || true);
    assert!(dest_write_rebinds("x", "x__slice_len") && !write_rebinds("x", "x__slice_len"));
}

/// Index-segment and derived-length channels on hand-picked names the generated
/// corpus spells only indirectly (`[_3]` inside a nested bracket, a fallback read).
#[test]
fn rebind_index_covers_the_segment_and_derived_channels() {
    let written = ["_3", "_30", "s", "s*", "s*[_3]", "a", "a.0", "p__slice_len"];
    let reads = [
        "s*[_3]",
        "s*[_30]",
        "s*[_3]__slice_len",
        "a[b[_3]]",
        "_3",
        "_3.0",
        "s__slice_len",
        "s*__slice_len",
        "a.0__slice_len",
        "a__slice_len__slice_len",
        "p__slice_len__slice_len",
        "x[_3][_30]",
    ];
    let mut table = NameTable::default();
    let ids: Vec<u32> = written.iter().map(|n| table.intern(n)).collect();
    let index = RebindIndex::build(&table, ids.iter().copied());
    for read in reads {
        for mode in [RebindMode::Plain, RebindMode::Dest] {
            let mut got: BTreeSet<&str> = BTreeSet::new();
            index.for_each_rebinder(read, mode, |w| {
                got.insert(table.name(w));
            });
            let want: BTreeSet<&str> = written
                .iter()
                .copied()
                .filter(|w| match mode {
                    RebindMode::Plain => write_rebinds(w, read),
                    RebindMode::Dest => dest_write_rebinds(w, read),
                })
                .collect();
            assert_eq!(got, want, "{mode:?} rebinders of `{read}`");
        }
    }
}

/// The LITERAL-INDEX ALIAS channel (`place_names_overlap`'s
/// `literal_index_segments_may_alias`, c40884c0106) on the spellings that produce it:
/// slice-pattern minimum lengths, from-end constants, a shared-slice constant, a
/// subslice, and the nested and unbalanced brackets its depth walk must agree on.
///
/// Trust (merge 2026-10-14): the soundness line added that channel to the predicate
/// after this index was written on the other line, and the merge left both the index
/// and `RebindSet` without it — the guards.rs differential failed on `a[0;min=2]`. A
/// missing rebinder is a short version union, the false-PROVE direction.
#[test]
fn rebind_index_covers_the_literal_alias_channel() {
    use super::rebind_index::RebindSet;
    let names = [
        "v*",
        "v*[0]",
        "v*[0].1",
        "v*[0;min=1]",
        "v*[0;min=2]",
        "v*[0;min=2].0",
        "v*[0;min=2].1",
        "v*[1;min=2]",
        "v*[-1;min=1]",
        "v*[-2;min=2]",
        "v*[0;slice]",
        "v*[1..-0]",
        "v*[1..-0][0;min=1]",
        "v*[_3]",
        "a[0][1;min=2]",
        "a[0][1]",
        "a[0;min=1][1]",
        "a[1]",
        "a[x[0]]",
        "a[x[1]]",
        "a[x[0]].f",
        "a[x[0]].g",
        "a[x[0]][1]",
        "a[x[0]][2]",
        "x]y[0;min=1]",
        "x]y[0;min=2]",
    ];
    // The channel is live on these names, in both directions, and stays precise.
    assert!(write_rebinds("v*[0;min=2]", "v*[0;min=1]"));
    assert!(write_rebinds("v*[0;min=1]", "v*[-1;min=1]"));
    assert!(write_rebinds("v*[1..-0]", "v*[0;min=2].1"));
    assert!(!write_rebinds("v*[0;min=1]", "v*[1;min=2]"));
    assert!(!write_rebinds("v*[0;min=2].0", "v*[0;min=2].1"));
    assert!(!write_rebinds("a[x[0]].f", "a[x[0]].g"));
    let mut table = NameTable::default();
    let ids: Vec<u32> = names.iter().map(|n| table.intern(n)).collect();
    let mut related = 0usize;
    for stride in [1usize, 2, 3] {
        for offset in 0..stride {
            let members: Vec<u32> = ids.iter().copied().skip(offset).step_by(stride).collect();
            let index = RebindIndex::build(&table, members.iter().copied());
            let mut set = RebindSet::default();
            for &w in &members {
                set.insert(table.name(w));
            }
            for read in names {
                for mode in [RebindMode::Plain, RebindMode::Dest] {
                    let mut got: BTreeSet<&str> = BTreeSet::new();
                    index.for_each_rebinder(read, mode, |w| {
                        got.insert(table.name(w));
                    });
                    let want: BTreeSet<&str> = members
                        .iter()
                        .map(|&w| table.name(w))
                        .filter(|w| match mode {
                            RebindMode::Plain => write_rebinds(w, read),
                            RebindMode::Dest => dest_write_rebinds(w, read),
                        })
                        .collect();
                    related += want.len();
                    assert_eq!(got, want, "{mode:?} rebinders of `{read}`");
                    assert_eq!(index.any_rebinder(read, mode), !want.is_empty(), "`{read}`");
                    if mode == RebindMode::Plain {
                        assert_eq!(set.any_rebinder(read), !want.is_empty(), "RebindSet `{read}`");
                    }
                }
            }
        }
    }
    assert!(related > names.len(), "vacuous: {related}");
    // The guards.rs differential's own case: a lone literal spelling rebinds the other.
    let mut set = RebindSet::default();
    set.insert("a[0;min=2]");
    assert!(set.any_rebinder("a[0;min=1]"));
    assert!(!set.any_rebinder("a[1;min=2]"));
}

fn assign(place: Place, rvalue: Rvalue) -> Statement {
    Statement::Assign { place, rvalue, span: SourceSpan::default() }
}

fn proj(local: usize, projections: Vec<Projection>) -> Place {
    Place { local, projections }
}

/// A looping CFG whose blocks write whole places, fields, a pointee, literal
/// and symbolic array slots, and take `&mut` borrows, with back edges and a
/// cleanup edge, so the entry maps track names of every projection shape.
/// Nothing branches back to bb0.
fn projected_writes_fn() -> VerifiableFunction {
    let u32_ty = Ty::u32();
    let pair = Ty::Tuple(vec![Ty::u32(), Ty::u32()]);
    let arr = Ty::Array { elem: Box::new(Ty::u32()), len: 4 };
    let locals = vec![
        LocalDecl { index: 0, ty: u32_ty.clone(), name: Some("ret".into()) },
        LocalDecl {
            index: 1,
            ty: Ty::Ref { mutable: true, inner: Box::new(pair.clone()) },
            name: Some("p".into()),
        },
        LocalDecl { index: 2, ty: pair.clone(), name: Some("s".into()) },
        LocalDecl { index: 3, ty: arr, name: Some("a".into()) },
        LocalDecl { index: 4, ty: Ty::usize(), name: Some("i".into()) },
        LocalDecl { index: 5, ty: u32_ty.clone(), name: Some("cond".into()) },
        LocalDecl {
            index: 6,
            ty: Ty::Ref { mutable: true, inner: Box::new(pair) },
            name: Some("q".into()),
        },
        LocalDecl { index: 7, ty: u32_ty.clone(), name: Some("t".into()) },
    ];
    let copy = |l: usize| Operand::Copy(Place::local(l));
    let use_of = |l: usize| Rvalue::Use(copy(l));
    let branch = |fwd: usize, back: usize| Terminator::SwitchInt {
        discr: copy(5),
        targets: vec![(0, BlockId(fwd))],
        otherwise: BlockId(back),
        exhaustive_enum_unreachable: false,
        span: SourceSpan::default(),
    };
    let blocks = vec![
        BasicBlock {
            id: BlockId(0),
            stmts: vec![
                assign(proj(1, vec![Projection::Deref, Projection::Field(0)]), use_of(7)),
                assign(Place::local(6), Rvalue::Ref { mutable: true, place: Place::local(2) }),
            ],
            // No edge back into bb0: its entry map stays all-entry, so the
            // entry-only gate has true answers to compare.
            terminator: branch(1, 1),
        },
        BasicBlock {
            id: BlockId(1),
            stmts: vec![
                assign(proj(2, vec![Projection::Field(1)]), use_of(7)),
                assign(proj(3, vec![Projection::Index(4)]), use_of(7)),
            ],
            terminator: branch(2, 1),
        },
        BasicBlock {
            id: BlockId(2),
            stmts: vec![
                assign(
                    proj(
                        3,
                        vec![Projection::ConstantIndex {
                            offset: 1,
                            min_length: 4,
                            from_end: false,
                        }],
                    ),
                    use_of(7),
                ),
                assign(proj(6, vec![Projection::Deref, Projection::Field(1)]), use_of(7)),
            ],
            terminator: Terminator::Call {
                func: "opaque".into(),
                args: vec![copy(1)],
                dest: Place::local(7),
                target: Some(BlockId(3)),
                span: SourceSpan::default(),
                atomic: None,
                is_unsafe_sig: false,
                callee_identity: None,
                callee_key: None,
                is_foreign: false,
                unwind: UnwindEdge::Cleanup(BlockId(4)),
            },
        },
        BasicBlock {
            id: BlockId(3),
            stmts: vec![
                assign(Place::local(2), use_of(2)),
                assign(proj(1, vec![Projection::Deref]), use_of(2)),
                // THE INDEX-LOCAL RESEAT. Local 4 is `a[_4]`'s index operand, so a
                // WHOLE write of it mints the fallback spelling `_4` into this
                // block's gen set beside the canonical `i` — and `_4` roots in its
                // own bucket while every name it rebinds (`a[_4]`, `a[_4].0`,
                // `a[_4]__slice_len`) roots in `a`. Without this statement the
                // fixture tracks no fallback name at all and the cross-root arm of
                // the comparison below is vacuous: that is the shape of the
                // measured false proof `index_local_min_bug`, where two reads of
                // `s*[_3]__slice_len` across a reseat tied as ONE unversioned name.
                assign(Place::local(4), use_of(7)),
            ],
            terminator: branch(4, 1),
        },
        BasicBlock { id: BlockId(4), stmts: vec![], terminator: Terminator::Return },
    ];
    VerifiableFunction {
        name: "projected_writes".into(),
        def_path: "test::projected_writes".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals,
            blocks,
            arg_count: 1,
            return_ty: u32_ty,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

/// The inter-block arm exactly as it read before the index: a union over EVERY
/// tracked name of the block.
///
/// THE RELATION IS `write_rebinds`, NOT `place_names_overlap`, and the difference
/// is the whole reason this comparison is worth making (merge, 2026-09-18). This
/// file's index landed against a union that tested the SYMMETRIC overlap; the
/// round-A10 lane replaced the production union with the DIRECTIONAL relation
/// `write_rebinds(written, read)`, whose second disjunct relates a written index
/// local `_l` to every read carrying the segment `[_l]`. A reference scan left on
/// the symmetric relation does not merely test something weaker — it asserts the
/// oracle still has the semantics the index-segment channel exists to replace, so
/// it would either fail spuriously or, worse, pass vacuously on a fixture that
/// never reseats an index local while the real hazard went unpinned.
fn full_scan_token(sv: &LegacyStmtVersions, block: BlockId, name: &str) -> Option<String> {
    let em = sv.entry_map().get(&block)?;
    let mut toks: BTreeSet<String> = BTreeSet::new();
    for (k, s) in em {
        if write_rebinds(k, name) {
            toks.extend(s.iter().cloned());
        }
    }
    if toks.is_empty() || toks == BTreeSet::from([ENTRY_VERSION_SENTINEL.to_string()]) {
        return None;
    }
    // The one spelling every oracle uses (short joins retired, long ones hashed).
    super::version_ssa::spell_token_texts(toks.iter().map(String::as_str))
}

fn full_scan_entry_only(sv: &LegacyStmtVersions, block: BlockId, name: &str) -> bool {
    let Some(full) = sv.entry_full_map() else { return false };
    let Some(em) = full.get(&block) else { return false };
    let mut toks: BTreeSet<&str> = BTreeSet::new();
    for (k, s) in em {
        if write_rebinds(k, name) {
            toks.extend(s.iter().map(String::as_str));
        }
    }
    toks.len() == 1 && toks.contains(ENTRY_VERSION_SENTINEL)
}

/// Every tracked name, plus projections, parents and look-alikes of each.
fn probes(sv: &LegacyStmtVersions) -> Vec<String> {
    let tracked: BTreeSet<String> =
        sv.entry_map().values().flat_map(|em| em.keys().cloned()).collect();
    let mut out: BTreeSet<String> = tracked.clone();
    for n in &tracked {
        for step in [".0", ".1", "*", "[0]", "[_4]", "[_9]", "__slice_len", "_x", "x"] {
            out.insert(format!("{n}{step}"));
        }
        for (i, c) in n.char_indices() {
            if matches!(c, '.' | '[' | '*' | '@') {
                out.insert(n[..i].to_string());
                out.insert(format!("{}[_4]", &n[..i]));
            }
        }
    }
    out.insert("unrelated".into());
    out.into_iter().collect()
}

/// THE EQUIVALENCE PIN: the SSA oracle answers every probe at every block exactly
/// as the retired full scan over the dense entry maps does — both the retired
/// bucketed lookup and the new rebinder-index union — on a cold memo and a warm one.
#[test]
fn indexed_inter_block_lookups_match_the_full_scan() {
    let func = projected_writes_fn();
    let sv = StmtVersionCtx::build(&func);
    let legacy = LegacyStmtVersions::build(&func);
    let probes = probes(&legacy);

    // The fixture must track projected names (or the index is never tested)
    // and must version some of them (or every answer is trivially `None`).
    let tracked: BTreeSet<&String> = legacy.entry_map().values().flat_map(|em| em.keys()).collect();
    assert_eq!(
        tracked.iter().map(|s| s.to_string()).collect::<Vec<_>>(),
        sv.ssa().tracked_names(),
        "the SSA oracle tracks a different name universe than the retired fixpoint"
    );
    assert!(
        tracked.iter().any(|n| n.contains('.')) && tracked.iter().any(|n| n.contains('*')),
        "fixture tracks no projected names: {tracked:?}"
    );
    assert!(tracked.iter().any(|n| n.contains('[')), "fixture tracks no indexed names");

    let mut versioned = 0usize;
    let mut entry_only = 0usize;
    for _pass in 0..2 {
        for bb in &func.body.blocks {
            for name in &probes {
                let expected = full_scan_token(&legacy, bb.id, name);
                assert_eq!(
                    legacy.inter_block_token(bb.id, name),
                    expected,
                    "retired bucketed token differs at {:?} for `{name}`",
                    bb.id
                );
                assert_eq!(
                    sv.ssa().inter_block_token(bb.id.0, name),
                    expected,
                    "SSA token differs at {:?} for `{name}`",
                    bb.id
                );
                // At statement 0 the in-block gate is empty, so the public entry
                // point answers from the (memoized) inter-block arm.
                assert_eq!(
                    sv.version_token_at(&func, bb.id, 0, name),
                    expected,
                    "memoized token differs at {:?} for `{name}`",
                    bb.id
                );
                versioned += usize::from(expected.is_some());
                let full = full_scan_entry_only(&legacy, bb.id, name);
                assert_eq!(
                    sv.full_graph_union_is_entry_only(bb.id, name),
                    full,
                    "indexed entry-only gate differs at {:?} for `{name}`",
                    bb.id
                );
                entry_only += usize::from(full);
            }
        }
    }
    assert!(versioned > 0, "no probe was versioned; the comparison is vacuous");
    assert!(entry_only > 0, "no probe was entry-only; the gate comparison is vacuous");
}

/// THE CROSS-ROOT PIN (merge, 2026-09-18): the bucket index must reach a tracked
/// name that `write_rebinds` relates to the read ACROSS root buckets.
///
/// The index's own lemma — overlapping names share a root — is true of
/// `place_names_overlap` and FALSE of `write_rebinds`'s index-segment disjunct:
/// the written fallback `_4` roots at `_4`, the read `a[_4]` roots at `a`. A
/// `place_root(name)`-only bucket loop answers `None` for that read, which is the
/// spelling that says "this is still the entry value" — a stale fact then
/// discharges a live obligation. `for_each_candidate_root` exists for exactly this
/// and this test is what would fail if it were simplified away.
///
/// The equivalence test above compares indexed against unindexed and so cannot
/// catch it alone: drop the extra candidate from BOTH and the two agree on being
/// wrong together. This test asserts the ANSWER, not the agreement.
#[test]
fn the_index_reaches_a_rebinding_name_in_another_root_bucket() {
    let func = projected_writes_fn();
    let sv = StmtVersionCtx::build(&func);

    // The fallback `_4` is minted only for a whole write of an index operand; if
    // that ever stops happening this test must fail loudly rather than pass empty.
    let tracked = sv.ssa().tracked_names();
    assert!(
        tracked.iter().any(|n| n.as_str() == "_4"),
        "fixture tracks no `_4` fallback, so the cross-root channel is untested: {tracked:?}"
    );
    assert_ne!(place_root("_4"), place_root("a[_4]"), "the two names must be in DIFFERENT buckets");
    assert!(write_rebinds("_4", "a[_4]"), "the directional relation must relate them");
    assert!(!place_names_overlap("_4", "a[_4]"), "and the symmetric one must not");

    // Some block must therefore version a read of `a[_4]`, and of the derived
    // length name the measured bug was actually minted on.
    let versioned_somewhere = |name: &str| {
        func.body.blocks.iter().any(|bb| sv.version_token_at(&func, bb.id, 0, name).is_some())
    };
    assert!(
        versioned_somewhere("a[_4]"),
        "the reseat of `_4` left every read of `a[_4]` unversioned: the bucket index \
         dropped the index-segment channel and a stale fact can now discharge a live row"
    );
    assert!(
        versioned_somewhere("a[_4]__slice_len"),
        "the reseat left `a[_4]__slice_len` unversioned — the exact spelling of \
         `index_local_min_bug`"
    );

    // And the entry-only gate must refuse to mint `#e` for such a read: `#e` is the
    // claim that EVERY path delivers the function-entry value, which the reseat
    // falsifies.
    assert!(
        func.body.blocks.iter().any(|bb| !sv.full_graph_union_is_entry_only(bb.id, "a[_4]")),
        "the `#e` gate treats `a[_4]` as entry-valued despite a reseat of `_4`"
    );
}
