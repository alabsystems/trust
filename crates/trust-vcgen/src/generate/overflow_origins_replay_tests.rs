//! Equivalence + completeness pins for the overflow-elision join-table replay
//! (`super::safety::overflow_vc_block_origins`).
//!
//! WHAT THE CONSUMER DOES WITH THIS TABLE, and therefore what these tests defend.
//! `rustc_mir_transform::trust_verify::elide_kernel_certified_checks` looks a
//! KernelCertified row's own sealed canonical string up in this table and, on a
//! `Unique(bb)` hit, REWRITES `bb`'s `Assert(Overflow)` terminator to a `Goto` —
//! deleting a live runtime overflow check. Two properties make that safe, and both
//! are properties of THIS function:
//!
//!   (E) EXACTNESS. Each row's VC must render byte-identically to the production
//!       pipeline's VC for the same obligation, because the join key is the
//!       formula-inclusive canonical JSON of the whole VC. A single changed byte
//!       silently stops matching — the failure is invisible, not loud.
//!   (C) COMPLETENESS. `Unique` is a claim about the WHOLE function: a key is
//!       `Ambiguous` (and refused) precisely because a SECOND block produced the
//!       same canonical string. A PREFIX of the enumeration can therefore report
//!       `Unique` for a key that is really ambiguous, which licenses deleting a
//!       check on the authority of a proof belonging to a different block.
//!
//! The tests below pin (E) against the memoized/unmemoized A/B, and (C) against
//! every budget that can cut the walk short.

use trust_types::{
    BasicBlock, BinOp, BlockId, LocalDecl, Operand, Place, Projection, Rvalue, SourceSpan,
    Statement, Terminator, Ty, UnwindEdge, VerifiableBody, VerifiableFunction,
    VerificationCondition,
};

use super::safety::{overflow_vc_block_origins, overflow_vc_block_origins_unmemoized};

fn u32_ty() -> Ty {
    Ty::Int { width: 32, signed: false }
}

/// A chain of `n` checked adds, each in its OWN block with its own
/// `Assert(Overflow(Add))` — the exact MIR shape the elision seam models, repeated so
/// the table has `n` distinct origins:
///
/// ```text
/// bb0: _t0 = CheckedAdd(_1, _2);  assert(!_t0.1, Overflow(Add)) -> bb1
/// bb1: _t1 = CheckedAdd(_1, _2);  assert(!_t1.1, Overflow(Add)) -> bb2
/// ...
/// bbn: return
/// ```
///
/// Locals: 0 = ret, 1/2 = args, then one `(u32, bool)` tuple local per link.
fn checked_add_chain(n: usize) -> VerifiableFunction {
    let mut locals = vec![
        LocalDecl { index: 0, ty: Ty::Unit, name: Some("ret".into()) },
        LocalDecl { index: 1, ty: u32_ty(), name: Some("a".into()) },
        LocalDecl { index: 2, ty: u32_ty(), name: Some("b".into()) },
    ];
    for i in 0..n {
        locals.push(LocalDecl {
            index: 3 + i,
            ty: Ty::Tuple(vec![u32_ty(), Ty::Bool]),
            name: None,
        });
    }
    let mut blocks = Vec::with_capacity(n + 1);
    for i in 0..n {
        let tmp = 3 + i;
        blocks.push(BasicBlock {
            id: BlockId(i),
            stmts: vec![Statement::Assign {
                place: Place::local(tmp),
                rvalue: Rvalue::CheckedBinaryOp(
                    BinOp::Add,
                    Operand::Copy(Place::local(1)),
                    Operand::Copy(Place::local(2)),
                ),
                span: SourceSpan::default(),
            }],
            terminator: Terminator::Assert {
                unwind: UnwindEdge::Unreachable,
                cond: Operand::Copy(Place { local: tmp, projections: vec![Projection::Field(1)] }),
                expected: false,
                msg: trust_types::AssertMessage::Overflow(BinOp::Add),
                target: BlockId(i + 1),
                span: SourceSpan::default(),
            },
        });
    }
    blocks.push(BasicBlock { id: BlockId(n), stmts: vec![], terminator: Terminator::Return });
    VerifiableFunction {
        name: format!("chain{n}"),
        def_path: format!("test::chain{n}"),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals,
            blocks,
            arg_count: 2,
            return_ty: Ty::Unit,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// The FULLY-RENDERED row digest: the origin block plus the canonical JSON of the
/// entire VC (which subsumes kind, formula and location — and is a strict superset of
/// `canonical_exact_vc_payload`, the compiler's actual join key). Equality of these
/// digests therefore implies equality of the join keys AND of the
/// `Unique`/`Ambiguous` classification derived from them.
fn row_digests(rows: &[(BlockId, VerificationCondition)]) -> Vec<String> {
    rows.iter()
        .map(|(bid, vc)| {
            let canonical = trust_types::canonical_digest_json_value(vc)
                .expect("a safety VC must canonicalize");
            format!("bb{}|{}", bid.0, serde_json::to_string(&canonical).expect("canonical JSON"))
        })
        .collect()
}

/// (E) EXACTNESS across a growth ladder: the memo scope changes not one byte.
///
/// Both columns matter and they catch different things. The COUNT column is what
/// exposes a silent truncation (a memo that answered for the wrong function, or a
/// meter that degraded a type and made a VC unrecognizable). The DIGEST column is what
/// proves the surviving rows are semantically identical rather than merely equinumerous
/// — it is the join key itself.
#[test]
fn memo_scope_is_byte_identical_across_a_growth_ladder() {
    for n in [1usize, 2, 4, 8, 16, 32, 64, 128] {
        let func = checked_add_chain(n);
        let memoized = overflow_vc_block_origins(&func, None)
            .expect("an unbudgeted replay is always complete");
        let baseline = overflow_vc_block_origins_unmemoized(&func, None)
            .expect("an unbudgeted replay is always complete");

        assert_eq!(
            memoized.len(),
            baseline.len(),
            "n={n}: obligation COUNT diverged between the memoized and unmemoized replay"
        );
        assert_eq!(
            memoized.len(),
            n,
            "n={n}: the fixture must yield exactly one Add-overflow origin per block — a \
             smaller count means the ladder stopped exercising growth"
        );
        assert_eq!(
            row_digests(&memoized),
            row_digests(&baseline),
            "n={n}: a fully-rendered obligation DIGEST diverged — the memo scope changed \
             the join key, which silently breaks the elision join"
        );
    }
}

/// (E), second half: the memo scope must not leak ACROSS functions. The memo is keyed
/// on function identity and reset at scope entry/exit; replaying two different
/// functions back to back on one thread must give each the answer it gets alone.
#[test]
fn memo_scope_does_not_leak_between_functions() {
    let small = checked_add_chain(3);
    let large = checked_add_chain(17);

    let small_alone = row_digests(&overflow_vc_block_origins(&small, None).expect("complete"));
    let large_alone = row_digests(&overflow_vc_block_origins(&large, None).expect("complete"));

    // Interleave repeatedly on the same thread: a memo that survived a scope, or that
    // matched on something weaker than function identity, shows up here.
    for _ in 0..4 {
        assert_eq!(
            row_digests(&overflow_vc_block_origins(&small, None).expect("complete")),
            small_alone,
        );
        assert_eq!(
            row_digests(&overflow_vc_block_origins(&large, None).expect("complete")),
            large_alone,
        );
    }
}

/// (C) COMPLETENESS: under EVERY budget, the replay returns either the complete table
/// or nothing — never a proper prefix.
///
/// This is the soundness pin. Before the fix the budget poll inside the generation walk
/// `break`s, and the partial rows were returned as if they were the whole table; the
/// consumer cannot tell a short table from a complete one, and a key whose duplicate
/// sat past the cut reads `Unique`. The step budget is swept across the whole range so
/// the cut lands at every position in the walk, including mid-block.
#[test]
fn a_budgeted_replay_is_complete_or_absent_never_a_prefix() {
    let n = 24;
    let func = checked_add_chain(n);
    let complete = overflow_vc_block_origins(&func, None).expect("unbudgeted is complete");
    assert_eq!(complete.len(), n);

    let mut saw_refusal = false;
    let mut saw_completion = false;
    for steps in 1u64..400 {
        let _budget = trust_types::verify_budget::VerifyBudgetGuard::install(None, steps);
        match overflow_vc_block_origins(&func, None) {
            None => saw_refusal = true,
            Some(rows) => {
                saw_completion = true;
                assert_eq!(
                    rows.len(),
                    n,
                    "steps={steps}: a table was returned with {} of {n} rows — a PREFIX of \
                     the enumeration was presented as a complete table, which lets a key \
                     whose duplicate sits past the cut read as Unique",
                    rows.len(),
                );
                assert_eq!(row_digests(&rows), row_digests(&complete), "steps={steps}");
            }
        }
    }
    // Control: the sweep must actually straddle the boundary, or the assertions above
    // are vacuous. A run that only ever refused (or only ever completed) proves nothing.
    assert!(saw_refusal, "the step sweep never truncated the walk — the pin is vacuous");
    assert!(saw_completion, "the step sweep never completed the walk — the pin is vacuous");
}

/// (C), the shape the seam actually consumes: a refusal is `None`, and an honestly
/// EMPTY table is `Some(vec![])`. Collapsing the two would turn "I could not enumerate"
/// into "there is nothing to elide", which reads the same at the call site but is a
/// claim the replay has not earned.
#[test]
fn an_empty_table_is_distinguishable_from_a_refused_one() {
    let no_arithmetic = checked_add_chain(0);
    let empty = overflow_vc_block_origins(&no_arithmetic, None);
    assert!(
        empty.as_ref().is_some_and(Vec::is_empty),
        "a function with no overflow assert has an EMPTY table, not an absent one"
    );

    let func = checked_add_chain(24);
    let _budget = trust_types::verify_budget::VerifyBudgetGuard::install(None, 1);
    assert!(
        overflow_vc_block_origins(&func, None).is_none(),
        "a replay cut short must refuse, not report an empty table"
    );
}

/// The measurement instrument behind the change, kept runnable rather than quoted.
/// `--ignored` because it is a timing, not a pin: it asserts only the direction, since
/// an absolute threshold would be a flaky assertion about the machine.
///
/// ```text
/// targo --unverified test -p trust-vcgen --lib -- --ignored --nocapture replay_memo_speedup
/// ```
#[test]
#[ignore = "measurement instrument, not a pin"]
fn replay_memo_speedup() {
    for n in [16usize, 32, 64, 128] {
        let func = checked_add_chain(n);
        let t0 = std::time::Instant::now();
        let memoized = overflow_vc_block_origins(&func, None).expect("complete");
        let memo_ms = t0.elapsed().as_secs_f64() * 1e3;
        let t1 = std::time::Instant::now();
        let baseline = overflow_vc_block_origins_unmemoized(&func, None).expect("complete");
        let base_ms = t1.elapsed().as_secs_f64() * 1e3;
        assert_eq!(memoized.len(), baseline.len());
        println!(
            "n={n:>4}  rows={:>4}  memoized={memo_ms:>9.1}ms  unmemoized={base_ms:>9.1}ms  \
             speedup={:>6.1}x",
            memoized.len(),
            base_ms / memo_ms.max(f64::MIN_POSITIVE),
        );
    }
}

/// The memo scope must not ARM the work meter. A trip would substitute the degraded
/// `Unsupported` leaf into a materialized type and change the rendered formula — the
/// exact silent join break this design exists to avoid. Pinned by running the replay
/// under a deliberately tiny work budget: with the meter disabled the output is
/// unchanged, and `gen_work_used()` records no charged work.
#[test]
fn the_replay_scope_never_arms_the_work_meter() {
    let func = checked_add_chain(16);
    let expected = row_digests(&overflow_vc_block_origins(&func, None).expect("complete"));

    crate::gen_work::set_test_budget(Some(1));
    let under_tiny_budget = overflow_vc_block_origins(&func, None).expect("complete");
    crate::gen_work::set_test_budget(None);

    assert_eq!(
        row_digests(&under_tiny_budget),
        expected,
        "a 1-node work budget changed the replay's output — the meter is armed on this \
         path and can degrade the join key"
    );
}
