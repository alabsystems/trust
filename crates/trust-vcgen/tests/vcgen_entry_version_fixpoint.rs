// The reaching-version fixpoint (`generate::path_defs::entry_versions_fixpoint`):
// it must scale in BLOCK count, it must be BOUNDED by the ambient verify budget,
// and it must never change an obligation.
//
// WHAT WENT WRONG, AND WHY THE EXISTING PIN COULD NOT SEE IT.
// `tests/vcgen_havoc_memoization.rs` grows STATEMENT count inside ONE block.
// This fixpoint is a whole-CFG dataflow analysis whose cost is
// `rounds x blocks x predecessor-edges x live names`, and a single-block body
// exercises none of that — nor does a forward-only DAG, which converges in about
// two round-robin passes. Real MIR has BACK EDGES. Measured on the ladder below
// (one obligation per block, so the obligation count is a clean truncation
// detector), VC generation grew with exponent ~2.8 in BLOCK count:
//
//     blocks   obligations    before      after
//         48            48     285 ms     170 ms
//         96            96    1771 ms     905 ms
//        144           144    5296 ms    2551 ms
//        192           192   11959 ms    5551 ms
//        288           288   40398 ms   18080 ms
//        384           384   93671 ms   42552 ms
//
// A stack sample of the wedged `nn-core` generator put
// `entry_versions_fixpoint`'s own frame at the TOP of self time, with
// `HashMap<String, BTreeSet<String>>`'s `reserve_rehash` and `insert` second and
// third — the per-(round x block x edge) intermediate map that is now gone.
//
// THE DANGEROUS DIRECTION IS NOT SLOWNESS. A reaching-version set that came back
// SHORT — a stale memo entry, or a truncated walk passed off as a finished one —
// is a short KILL set, which lets a stale fact survive and vacuously discharge a
// real obligation. That is a false PROVE. The staleness and budget tests below
// are the ones that matter; the timing bound is only a regression guard.
use std::time::Instant;
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
                    rvalue: Rvalue::Ref { mutable: true, place: Place::local(first_borrow + 2 * i) },
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
    }
}

fn render(vcs: &[trust_types::VerificationCondition]) -> Vec<String> {
    vcs.iter().map(|vc| format!("{:?} | {:?} | {:?}", vc.kind, vc.formula, vc.location)).collect()
}

/// THE COMPLEXITY PIN, in BLOCK count. Deliberately loose — this guards against
/// the return of the per-edge map rebuild, not a benchmark, and it must not
/// flake on a loaded machine. The pre-fix build took ~12 s at this size; a
/// regression misses the bound by a wide margin rather than narrowly.
#[test]
fn generation_is_not_superlinear_in_block_count() {
    let func = cfg_func("wide", 192, 8);
    let start = Instant::now();
    let vcs = generate_vcs(&func);
    let elapsed = start.elapsed();
    assert!(
        elapsed.as_secs() < 40,
        "VC generation for a 192-block CFG took {elapsed:?} — the reaching-version \
         fixpoint is rebuilding a whole intermediate map per (round x block x predecessor \
         edge) again, or its per-function precompute is no longer shared between the two \
         callers (see `entry_version_gen_sets`)"
    );
    assert!(!vcs.is_empty(), "the body must still produce obligations");
}

/// THE STALENESS PIN for the new per-function precompute memo.
///
/// `alpha` and `beta` have deliberately different CFGs, different local counts
/// and different havoc lists, so a precompute replayed across them would yield
/// different gen-sets, different OUT tokens, and therefore different kill sets.
/// Run a, then b, then a again: `a`'s obligations must be byte-identical.
///
/// This is the observable form of the invariant the memo's identity discipline
/// maintains — entries bound to a function identity, inert outside a `gen_work`
/// scope, cleared on every outermost scope entry AND exit. Drop any one of the
/// three and this is what fails.
#[test]
fn a_precompute_entry_never_crosses_functions() {
    let a = cfg_func("alpha", 9, 3);
    let b = cfg_func("beta", 14, 7);

    let a_first = render(&generate_vcs(&a));
    let b_only = render(&generate_vcs(&b));
    let a_second = render(&generate_vcs(&a));

    assert_eq!(
        a_first, a_second,
        "generating `beta` in between changed `alpha`'s obligations — a reaching-version \
         precompute leaked across functions. A wrong gen-set is a wrong KILL set, which can \
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
    assert_eq!(first, second, "a precompute memo hit changed this function's obligations");
}

/// THE BUDGET PIN: `-Ztrust-verify-function-budget-{ms,steps}` must actually
/// bound the reaching-version fixpoint.
///
/// MEASURED before this: a budgeted `nn-core` run reached its 143rd function and
/// then sat 10+ minutes inside `entry_versions_fixpoint` with the budget LIVE —
/// it was correctly recording 'timed out' obligations elsewhere and simply had
/// no poll here. The whole loop ran outside the bound, and the checkpoint that
/// reports an overrun sits AFTER generation returns.
///
/// With a deliberately tiny ambient budget, generation must stop PROMPTLY. The
/// truncation is not a verdict: the caller observes the spent budget and applies
/// the discipline `d9d9d675e3` landed — advisory warns and substitutes one
/// COUNTED `Unknown` with the partial VCs discarded wholesale,
/// strict/certify/memory-safe keep the located hard error.
#[test]
fn the_fixpoint_is_bounded_by_the_ambient_budget() {
    let func = cfg_func("budgeted", 192, 8);

    let _guard = trust_types::verify_budget::VerifyBudgetGuard::install(None, 50);
    let start = Instant::now();
    let _bounded = generate_vcs(&func);
    let elapsed = start.elapsed();

    assert!(
        trust_types::verify_budget::exhausted_readonly(),
        "the tiny step budget must be observably spent, or this test proves nothing"
    );
    // 30s, not 5: the disease this pins ran 10+ MINUTES (see the doc above),
    // so a 30s wall still catches it with 20x margin — while the fixture's own
    // setup + the between-poll strides measure ~5.4s on a loaded dev box
    // (controlled: identical with and without the e6 merge's vcgen delta), so
    // a 5s wall failed on machine speed, not on the property.
    assert!(
        elapsed.as_secs() < 30,
        "VC generation did not stop promptly on an exhausted budget (took {elapsed:?}) — the \
         reaching-version fixpoint is not polling `budget_exhausted()`"
    );
}
