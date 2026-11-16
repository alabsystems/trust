// The statement-version oracle on a BACK-EDGE ladder: it must scale in BLOCK count,
// and it must never change an obligation.
//
// HISTORY. This file pinned `generate::path_defs::entry_versions_fixpoint`, the
// whole-CFG reaching-version fixpoint the oracle used to be. Its cost was
// `rounds x blocks x predecessor-edges x live names`, and on the ladder below — where
// information must travel backwards one block per round-robin pass — VC generation
// grew with exponent ~2.8 in BLOCK count (285 ms at 48 blocks, 93.7 s at 384 before
// the per-edge map rebuild was removed; 42.6 s after). The fixpoint also polled the
// ambient verify budget, because a truncated reaching-version map was its failure
// mode, and this file pinned that poll with a wall-clock bound.
//
// The fixpoint is gone: `generate::version_ssa` resolves the same reaching sets on
// demand over the dominator tree and has no truncated state of its own (the retired
// fixpoint survives only as the `cfg(test)` differential it is checked against, byte
// for byte, in `version_ssa_parity_tests`). So the timing pin and the fixpoint's own
// budget pin are retired with it. (The oracle's INPUTS still come from the polled
// block-definition extraction; `version_ssa_parity_tests::
// an_oracle_built_after_a_budget_trip_fails_closed` pins what it does after a trip.)
// What this file pins now is COST AS WORK — deterministic counters, not wall time —
// and the two staleness properties below.
//
// THE DANGEROUS DIRECTION IS NOT SLOWNESS. A reaching-version set that came back
// SHORT — a stale memo entry, an oracle answering for the wrong function — is a short
// KILL set, which lets a stale fact survive and vacuously discharge a real
// obligation. That is a false PROVE. The staleness tests below are the ones that
// matter.
use trust_types::{
    BasicBlock, BinOp, BlockId, LocalDecl, Operand, Place, Projection, Rvalue, SourceSpan,
    Statement, Terminator, Ty, VerifiableBody, VerifiableFunction,
};
use trust_vcgen::generate_vcs;

fn u32_ty() -> Ty {
    Ty::Int { width: 32, signed: false }
}

fn mut_ref_u32() -> Ty {
    Ty::Ref { mutable: true, inner: Box::new(u32_ty()) }
}

/// A `blocks`-block CFG, one overflow obligation per block, whose entry block
/// carries an OPAQUE deref store (`p` is a parameter, so `resolve_referent`
/// cannot fold it) and `borrows` mutable borrows — which is what puts the
/// whole-function havoc list in effect and makes the gen-sets non-trivial.
///
/// Every non-terminal block branches FORWARD to `b+1` and BACK to `b-1`. The
/// back edge is the point: information must travel backwards one block per
/// round-robin pass, so the fixpoint needs real rounds rather than converging
/// immediately in block order.
fn cfg_func(name: &str, blocks: usize, borrows: usize) -> VerifiableFunction {
    let mut locals = vec![
        LocalDecl { index: 0, ty: u32_ty(), name: Some("ret".into()) },
        LocalDecl { index: 1, ty: mut_ref_u32(), name: Some("p".into()) },
        LocalDecl { index: 2, ty: u32_ty(), name: Some("a".into()) },
        LocalDecl { index: 3, ty: u32_ty(), name: Some("b".into()) },
        LocalDecl { index: 4, ty: u32_ty(), name: Some("cond".into()) },
    ];
    let first_tmp = locals.len();
    for i in 0..blocks {
        locals.push(LocalDecl { index: first_tmp + i, ty: u32_ty(), name: Some(format!("t{i}")) });
    }
    let first_borrow = locals.len();
    for i in 0..borrows {
        locals.push(LocalDecl {
            index: first_borrow + 2 * i,
            ty: u32_ty(),
            name: Some(format!("v{i}")),
        });
        locals.push(LocalDecl {
            index: first_borrow + 2 * i + 1,
            ty: mut_ref_u32(),
            name: Some(format!("r{i}")),
        });
    }

    let mut cfg = Vec::with_capacity(blocks);
    for b in 0..blocks {
        let mut stmts = Vec::new();
        if b == 0 {
            stmts.push(Statement::Assign {
                place: Place { local: 1, projections: vec![Projection::Deref] },
                rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
                span: SourceSpan::default(),
            });
            for i in 0..borrows {
                stmts.push(Statement::Assign {
                    place: Place::local(first_borrow + 2 * i + 1),
                    rvalue: Rvalue::Ref {
                        mutable: true,
                        place: Place::local(first_borrow + 2 * i),
                    },
                    span: SourceSpan::default(),
                });
            }
        }
        stmts.push(Statement::Assign {
            place: Place::local(first_tmp + b),
            rvalue: Rvalue::BinaryOp(
                BinOp::Add,
                Operand::Copy(Place::local(2)),
                Operand::Copy(Place::local(3)),
            ),
            span: SourceSpan::default(),
        });
        let terminator = if b + 1 >= blocks {
            Terminator::Return
        } else {
            Terminator::SwitchInt {
                discr: Operand::Copy(Place::local(4)),
                targets: vec![(0, BlockId(b + 1))],
                otherwise: BlockId(b.saturating_sub(1)),
                exhaustive_enum_unreachable: false,
                span: SourceSpan::default(),
            }
        };
        cfg.push(BasicBlock { id: BlockId(b), stmts, terminator });
    }

    VerifiableFunction {
        name: name.to_string(),
        def_path: format!("fixpoint::{name}"),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals,
            blocks: cfg,
            arg_count: 4,
            return_ty: u32_ty(),
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

fn render(vcs: &[trust_types::VerificationCondition]) -> Vec<String> {
    vcs.iter().map(|vc| format!("{:?} | {:?} | {:?}", vc.kind, vc.formula, vc.location)).collect()
}

/// THE COMPLEXITY PIN, in BLOCK count, as WORK. For each doubling of the ladder the
/// oracle's build — the dominator index, the per-block write index, the tracked name
/// universe — must grow at most 2.5x, and it must be built exactly ONCE per
/// generation (every site shares it). These are deterministic counters: they cannot
/// flake on a loaded machine, and a return of any per-(block x name) structure shows
/// up as a 4x rung, not as a slower run.
#[test]
fn the_version_oracle_build_is_linear_in_block_count() {
    let mut previous: Option<(usize, trust_vcgen::AnalysisMemoStats)> = None;
    for blocks in [48usize, 96, 192] {
        let func = cfg_func("wide", blocks, 8);
        trust_vcgen::reset_analysis_memo_stats();
        let vcs = generate_vcs(&func);
        let stats = trust_vcgen::analysis_memo_stats();
        assert!(!vcs.is_empty(), "the body must still produce obligations");
        assert_eq!(
            stats.entry_versions_computed, 1,
            "the oracle is built once per generation: {stats:?}"
        );
        if let Some((small, prev)) = previous {
            for (name, a, b) in [
                ("cfg_work", prev.cfg_work, stats.cfg_work),
                ("block_write_entries", prev.block_write_entries, stats.block_write_entries),
                ("tracked_names", prev.tracked_names, stats.tracked_names),
            ] {
                let ratio = b as f64 / a.max(1) as f64;
                assert!(
                    ratio <= 2.5,
                    "`{name}` grew {ratio:.2}x ({a} -> {b}) from {small} to {blocks} blocks: \
                     the version oracle's build is super-linear again. {prev:?} -> {stats:?}"
                );
            }
        }
        previous = Some((blocks, stats));
    }
}

/// THE STALENESS PIN for the per-function oracle memo.
///
/// `alpha` and `beta` have deliberately different CFGs, different local counts
/// and different havoc lists, so an oracle replayed across them would yield
/// different gen-sets, different OUT tokens, and therefore different kill sets.
/// Run a, then b, then a again: `a`'s obligations must be byte-identical.
///
/// This is the observable form of the invariant the memo's identity discipline
/// maintains — entries bound to a function identity, inert outside a `gen_work`
/// scope, cleared on every outermost scope entry AND exit. Drop any one of the
/// three and this is what fails.
#[test]
fn an_oracle_never_crosses_functions() {
    let a = cfg_func("alpha", 9, 3);
    let b = cfg_func("beta", 14, 7);

    let a_first = render(&generate_vcs(&a));
    let b_only = render(&generate_vcs(&b));
    let a_second = render(&generate_vcs(&a));

    assert_eq!(
        a_first, a_second,
        "generating `beta` in between changed `alpha`'s obligations — a statement-version \
         oracle leaked across functions. A wrong gen-set is a wrong KILL set, which can \
         vacuously discharge a real obligation (a false PROVE)"
    );
    assert_ne!(
        a_first, b_only,
        "the two fixtures must differ, or this test cannot witness cross-function reuse"
    );
}

/// A memo HIT must replay the byte-identical obligation set the computing query
/// produced, not a cheaper approximation of it.
#[test]
fn repeated_generation_is_byte_identical() {
    let func = cfg_func("repeat", 11, 4);
    let first = render(&generate_vcs(&func));
    let second = render(&generate_vcs(&func));
    assert_eq!(first, second, "an oracle memo hit changed this function's obligations");
}
