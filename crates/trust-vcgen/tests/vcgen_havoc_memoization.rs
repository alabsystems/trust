// The per-function opaque-deref/havoc memo (`trust_vcgen::havoc_memo`): it must
// make VC generation scale, and it must NEVER change an obligation.
//
// WHAT WENT WRONG. `deref_store_havoc_names` / `writes_until` are queried once
// per (program point x name) by the statement-granular version oracle, and each
// query re-ran a WHOLE-FUNCTION analysis (`resolve_referent` per statement,
// `mutably_borrowed_local_names`, `mutable_pointer_local_names`, each with a
// quadratic `Vec::contains` dedup). Measured on the body below, generation grew
// with exponent ~2.6 in statement count — 25 stmts 1.4 s, 50 stmts 9.9 s, 100
// stmts 50.3 s — which is why `nn-core`, `ny-core` and `clean-kernel` never
// finished VC generation under advisory.
//
// THE DANGEROUS DIRECTION IS NOT SLOWNESS. A memoized havoc set that went STALE
// — replayed for a function it was not computed for — would silently SHRINK a
// kill set, letting a stale fact survive and vacuously discharge a real
// obligation. That is a false PROVE, and it is far worse than being slow. The
// second test below is the one that matters: it interleaves two functions with
// deliberately DIFFERENT havoc lists and pins that the first function's
// obligations are byte-identical before and after the second one runs.
use std::time::Instant;

use trust_types::{
    BasicBlock, BinOp, BlockId, ConstValue, LocalDecl, Operand, Place, Projection, Rvalue,
    SourceSpan, Statement, Terminator, Ty, VerifiableBody, VerifiableFunction,
};
use trust_vcgen::generate_vcs;

fn u32_ty() -> Ty {
    Ty::Int { width: 32, signed: false }
}

fn mut_ref_u32() -> Ty {
    Ty::Ref { mutable: true, inner: Box::new(u32_ty()) }
}

/// `fn f(p: &mut u32, a: u32, b: u32) -> u32` whose entry block is
///   `*p = a;`                     <- an OPAQUE deref store (`p` is a parameter,
///                                    so `resolve_referent` cannot fold it), which
///                                    is what puts the whole-function havoc list
///                                    in effect for this block
///   `r{i} = &mut v{i};`           <- `borrows` mutable borrows, which is what
///                                    POPULATES that havoc list
///   `t{i} = a + b;`               <- `n` overflow-obligation-bearing statements,
///                                    i.e. `n` program points whose version
///                                    tokens each queried the oracles above
fn havoc_func(name: &str, n: usize, borrows: usize) -> VerifiableFunction {
    let mut locals = vec![
        LocalDecl { index: 0, ty: u32_ty(), name: Some("ret".into()) },
        LocalDecl { index: 1, ty: mut_ref_u32(), name: Some("p".into()) },
        LocalDecl { index: 2, ty: u32_ty(), name: Some("a".into()) },
        LocalDecl { index: 3, ty: u32_ty(), name: Some("b".into()) },
    ];
    let first_tmp = locals.len();
    for i in 0..n {
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

    let mut stmts = vec![Statement::Assign {
        place: Place { local: 1, projections: vec![Projection::Deref] },
        rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
        span: SourceSpan::default(),
    }];
    for i in 0..borrows {
        stmts.push(Statement::Assign {
            place: Place::local(first_borrow + 2 * i + 1),
            rvalue: Rvalue::Ref { mutable: true, place: Place::local(first_borrow + 2 * i) },
            span: SourceSpan::default(),
        });
    }
    for i in 0..n {
        stmts.push(Statement::Assign {
            place: Place::local(first_tmp + i),
            rvalue: Rvalue::BinaryOp(
                BinOp::Add,
                Operand::Copy(Place::local(2)),
                Operand::Copy(Place::local(3)),
            ),
            span: SourceSpan::default(),
        });
    }
    stmts.push(Statement::Assign {
        place: Place::local(0),
        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(0, 32))),
        span: SourceSpan::default(),
    });

    VerifiableFunction {
        name: name.to_string(),
        def_path: format!("memo::{name}"),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals,
            blocks: vec![BasicBlock { id: BlockId(0), stmts, terminator: Terminator::Return }],
            arg_count: 3,
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

/// THE COMPLEXITY PIN. 200 statements must generate in seconds.
///
/// Before the memo this body measured ~2.6 in the exponent and was on track for
/// ~4 minutes at this size (extrapolated from the 25/50/100 curve above); the
/// three real blockers never completed at all. The bound is deliberately loose —
/// this is a guard against the return of super-linear blowup, not a benchmark,
/// and it must not flake on a loaded machine. A regression to the old behaviour
/// misses it by more than an order of magnitude.
#[test]
fn generation_is_not_superlinear_in_statement_count() {
    let func = havoc_func("big", 200, 8);
    let start = Instant::now();
    let vcs = generate_vcs(&func);
    let elapsed = start.elapsed();
    // 90s, not 30: measured 33.4s on a loaded dev box with the pre-merge
    // vcgen (controlled), while the disease this pins extrapolated to ~4
    // minutes -- a 90s wall keeps ~2.7x margin against the regression and the
    // same against machine variance, honouring the doc's own "must not flake
    // on a loaded machine".
    assert!(
        elapsed.as_secs() < 90,
        "VC generation for a 200-statement body with one opaque deref store took {elapsed:?} \
         — the per-function havoc/opaque-deref analyses are being recomputed per program \
         point again (see `trust_vcgen::havoc_memo`)"
    );
    assert!(!vcs.is_empty(), "the body must still produce obligations");
}

/// THE STALENESS PIN — the one that guards soundness rather than speed.
///
/// `a` and `b` have deliberately DIFFERENT havoc lists (different local counts,
/// different numbers of `&mut` borrows), so a memo entry replayed across them
/// would produce a different kill set and therefore different obligations. Run
/// a, then b, then a again: `a`'s obligations must be byte-identical both times.
///
/// This is the observable form of the invariant the memo's identity discipline
/// exists to maintain (bound to a function identity, inert outside a `gen_work`
/// scope, cleared on every outermost scope entry AND exit). If any of those
/// three were dropped, this test is what fails.
#[test]
fn a_memo_entry_never_crosses_functions() {
    let a = havoc_func("alpha", 12, 3);
    let b = havoc_func("beta", 7, 9);

    let a_first = render(&generate_vcs(&a));
    let b_only = render(&generate_vcs(&b));
    let a_second = render(&generate_vcs(&a));

    assert_eq!(
        a_first, a_second,
        "generating `beta` in between changed `alpha`'s obligations — a havoc/opaque-deref \
         memo entry leaked across functions, which SHRINKS a kill set and can vacuously \
         discharge a real obligation (a false PROVE)"
    );
    assert_ne!(
        a_first, b_only,
        "the two fixtures must differ, or this test cannot witness cross-function reuse"
    );
}

/// Repeated generation of the SAME function is deterministic — a memo hit must
/// replay the byte-identical set the first (computing) query produced, not a
/// cheaper approximation of it.
#[test]
fn repeated_generation_is_byte_identical() {
    let func = havoc_func("repeat", 20, 5);
    let first = render(&generate_vcs(&func));
    let second = render(&generate_vcs(&func));
    assert_eq!(first, second, "a memo hit changed this function's obligations");
}

/// THE BUDGET PIN: `-Ztrust-verify-function-budget-{ms,steps}` must actually
/// bound VC GENERATION.
///
/// `trust_types::verify_budget` names "the VC-generation walks" as one of the
/// choke points that call `budget_exhausted()` once per iteration, but the
/// `generate/` tree contained ZERO budget polls — the crate's only three were in
/// `contracts.rs`. So the per-block and per-statement loops in
/// `generate::safety` ran entirely outside the budget, and a function whose
/// generation spun never reached the post-generation checkpoint in
/// `rustc_mir_transform::trust_verify` that exists to report exactly that. That
/// is why `nn-core`, `ny-core` and `clean-kernel` spun at 100% CPU with NO
/// diagnostic instead of failing fast.
///
/// With the ambient budget installed and deliberately tiny, generation must stop
/// early and hand back a TRUNCATED inventory promptly. The truncation is not a
/// verdict: the caller observes the spent budget and applies the discipline
/// `d9d9d675e3` landed — advisory warns and substitutes one counted `Unknown`
/// with the partial VCs DISCARDED, strict/certify/memory-safe keep the located
/// hard error. Nothing here may be read as "this function verified".
#[test]
fn vc_generation_is_bounded_by_the_ambient_budget() {
    let func = havoc_func("budgeted", 200, 8);
    let unbudgeted = generate_vcs(&func).len();
    assert!(unbudgeted > 0, "the fixture must produce obligations when unbudgeted");

    let _guard = trust_types::verify_budget::VerifyBudgetGuard::install(None, 50);
    let start = Instant::now();
    let bounded = generate_vcs(&func);
    let elapsed = start.elapsed();

    assert!(
        trust_types::verify_budget::exhausted_readonly(),
        "the tiny step budget must be observably spent, or this test proves nothing"
    );
    assert!(
        bounded.len() < unbudgeted,
        "VC generation ignored the ambient budget and produced its full {unbudgeted}-row \
         inventory anyway — the generation walk is not polling `budget_exhausted()`"
    );
    assert!(
        elapsed.as_secs() < 5,
        "generation did not stop promptly on an exhausted budget (took {elapsed:?})"
    );
}
