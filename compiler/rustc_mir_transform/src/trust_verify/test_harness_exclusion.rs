//! Trust (CB4, 2026-09-28): the bodies rustc's libtest harness SYNTHESIZES are
//! EXCLUDED from the proof inventory — counted, disclosed, never proved.
//!
//! ## The failure
//!
//! Under `--test` the builtin `#[test]` expander wraps every test in a runner
//! closure (`|| test::assert_test_result(the_test())`) and the harness pass adds
//! `fn main() { test::test_main_static(&[..]) }`. The strict verification gate
//! treated both as user proof inventory, and neither can be proved: the closure
//! calls the generic libtest callee `assert_test_result::<T>`, whose body is
//! absent from the lowered bundle (`[trust-absent-callee-assumption]`), and
//! `main` is built at `DUMMY_SP`, so every obligation in it has no source span
//! and the typed request builder refuses its whole bundle
//! (`MissingObligationSourceSpan`). MEASURED: `rustc --test -Ztrust-verify=on`
//! on a crate whose only test is `#[test] fn empty() {}` failed with exactly
//! those two errors, and so did `targo trust test` and `targo trust check
//! --tests`. No strict crate with a `#[test]` could build its tests.
//!
//! ## The rule
//!
//! A body is excluded only when BOTH hold:
//!
//! 1. PROVENANCE — `rustc_middle::middle::trust_test_harness` says rustc's
//!    libtest harness synthesized it, keyed on the expansion that produced the
//!    item's own span (never on a name, never on the forgeable
//!    `#[rustc_test_marker]` alone); and, for a runner closure, the builtin
//!    macro it came from is resident in this compiler's own sysroot.
//! 2. SHAPE — its optimized MIR is EXACTLY the harness shape
//!    ([`runner_closure_shape`], [`harness_main_shape`]): no source scope
//!    carries inlined code, only call/return/goto/unwind terminators, and
//!    * a runner closure makes exactly one call to its test function `u` — a
//!      local, non-generic fn the author wrote — and exactly one call to libtest's
//!      `assert_test_result`, and `u` carries no `requires` clause;
//!    * `main` makes exactly one call, to libtest's `test_main_static` or
//!      `test_main_static_abort`, and every `#[rustc_test_marker]` item in the
//!      crate is a descriptor the builtin `#[test]`/`#[bench]` synthesized.
//!
//! When either fails the body is verified exactly as before, and human output
//! says why it was not excluded.
//!
//! ## Why each shape conjunct exists
//!
//! * `requires` on `u`: `#[test]` fns take no arguments and a `requires` clause
//!   can name neither a static nor a call, so any non-trivial `requires` on a
//!   test is unsatisfiable, and the callee's own vacuity guard already refuses
//!   to assume it (an `assumption:requires` row). What the harness closure
//!   still holds is the CALL-SITE precondition row — MEASURED:
//!   `#[test] fn vacuous() requires false {}` reports
//!   `precondition of ...::vacuous#1 FAILED` inside the closure. Excluding the
//!   closure would drop that row, so a `requires`-bearing test keeps its
//!   closure verified. That row is all this conjunct guards.
//! * inlining: under explicit MIR inlining the test body is inlined into the
//!   closure (MEASURED at `-Copt-level=3 -Zmir-opt-level=2 -Zinline-mir=yes`:
//!   the user's `ArithmeticOverflow` row moved into `{closure#0}`, and for a
//!   `requires false` test the call — and with it the precondition row —
//!   disappeared). "The closure contains no user code" holds for the AST, not
//!   for inlined MIR, so any inlined scope refuses exclusion.
//! * exactly one call to `u`: after inlining, "every call goes to `u` or to
//!   libtest" is satisfied by a closure that calls NOTHING — the inlining
//!   check and this count close that together.
//! * `main` and user markers: with `custom_test_frameworks` and no
//!   `#![test_runner]`, a user-written `#[test_case] const T: TestDescAndFn`
//!   whose `testfn` is any function pointer is run by a `main` whose MIR is
//!   byte-for-byte the builtin shape (MEASURED), so `main` would execute
//!   author-chosen code with no row anywhere. `main` is excluded only when
//!   every marked item is a builtin descriptor. A custom `#![test_runner]`
//!   makes `main` call the author's runner, which fails the one-call check.
//!
//! ## What an exclusion is
//!
//! Not a proof and not an assumption. The body keeps its place in the coverage
//! universe (eligible and processed), and under JSON transport output its ONE
//! function envelope carries ONE row in the shape
//! `trust_types::exclusion` pins — kind `excluded:test-harness-synthesized`,
//! outcome `skipped` (which every older consumer counts as not proved), solver
//! `trust-test-harness`. Targo counts that row as `excluded`, outside the
//! obligation total. It is never a verification failure in any policy
//! (`skip_is_full_verification_failure`), the same disposition as
//! `ContractGeneratedClosure` — with one difference recorded in
//! docs/DECISION_QUEUE.md: that closure is statically dead, while these bodies
//! RUN in phase B of `targo trust test`, so the libtest crate `test` is listed
//! as a Conditional trust-base entry in test-mode units, beside core/alloc/std.

use rustc_hir::def::DefKind;
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_middle::middle::trust_test_harness::{
    TestHarnessItem, is_from_builtin_test_expansion, own_expansion_macro_def,
    test_harness_markers_are_all_builtin, test_harness_synthesized_item,
};
use rustc_middle::mir::{Body, Operand, TerminatorKind};
use rustc_middle::ty::{self, TyCtxt};
use rustc_span::sym;
use trust_types::exclusion::{
    TEST_HARNESS_EXCLUSION_TAG, TEST_HARNESS_ROW_DESCRIPTION, TEST_HARNESS_ROW_KIND,
    TEST_HARNESS_ROW_SOLVER, TestHarnessExclusionItem, test_harness_exclusion_reason,
};

use super::{
    Outcome, TransportObligationResult, TrustContractKind, TrustOutputMode, emit_transport_json,
    source_span_from_rustc_span, trust_contracts_if_any,
};

/// Trust (CB4): one excluded body — the payload of
/// `TrustVerifySkipReason::TestHarnessSynthesized`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct TestHarnessExclusion {
    /// `HarnessMain` or `TestRunnerClosure`; a descriptor const is never a
    /// runtime body this pass sees.
    pub(super) item: TestHarnessItem,
    /// For a runner closure, its one user callee — the test function, which is
    /// verified as its own body. `None` for `main`.
    pub(super) test_function: Option<DefId>,
    /// The exact `reason` the exclusion row carries, rendered once at decision
    /// time so a callee path that cannot be carried refuses the exclusion
    /// instead of producing a row the consumer would reject.
    pub(super) row_reason: String,
}

/// One `Call` terminator of a harness body, classified.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum HarnessCall {
    /// A local, non-generic `fn` the author wrote (its span is not from the
    /// builtin test expansion, and it is not itself harness-synthesized),
    /// called with `args` arguments.
    AuthorFn { def: DefId, args: usize },
    /// `test::assert_test_result` in the sysroot `test` crate.
    LibtestAssertTestResult,
    /// `test::test_main_static` / `test::test_main_static_abort` in the sysroot
    /// `test` crate.
    LibtestMain,
    /// Anything else: an indirect call, another crate, a generic or
    /// harness-synthesized local fn, another libtest item.
    Other,
}

/// The facts the shape checks read, extracted from one optimized body.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(super) struct HarnessBodyShape {
    /// Every `Call` terminator, classified.
    pub(super) calls: Vec<HarnessCall>,
    /// The first terminator that is neither a call nor return/goto/unwind
    /// plumbing, by name.
    pub(super) foreign_terminator: Option<&'static str>,
    /// Some source scope carries `inlined: Some(..)`.
    pub(super) has_inlined_scope: bool,
}

/// Why a provenance-matched harness body is still verified.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum HarnessShapeRefusal {
    InlinedScope,
    ForeignTerminator,
    NotExactlyOneTestCall,
    UnexpectedCall,
    TestCallArity,
    TestFunctionRequires,
    NonSysrootExpander,
    AuthorMarkedItems,
    NotExactlyOneLibtestEntry,
    UncarriableTestPath,
}

impl HarnessShapeRefusal {
    pub(super) const fn describe(self) -> &'static str {
        match self {
            Self::InlinedScope => {
                "MIR inlining folded other code into this body, so it no longer contains only \
                 harness code"
            }
            Self::ForeignTerminator => "the body has control flow the harness never generates",
            Self::NotExactlyOneTestCall => {
                "the closure does not make exactly one call to one test function"
            }
            Self::UnexpectedCall => {
                "the body calls something other than its test function and libtest"
            }
            Self::TestCallArity => "the test function is called with an unexpected arity",
            Self::TestFunctionRequires => {
                "the test function carries a `requires` clause, and the harness closure holds its \
                 call-site precondition check"
            }
            Self::NonSysrootExpander => {
                "the `#[test]` expander it came from is not resident in this compiler's sysroot"
            }
            Self::AuthorMarkedItems => {
                "the crate has a `#[test_case]` or hand-written `#[rustc_test_marker]` item, which \
                 this `main` would run"
            }
            Self::NotExactlyOneLibtestEntry => {
                "`main` does not make exactly one call to libtest's `test_main_static` (a custom \
                 `#![test_runner]` calls the author's runner)"
            }
            Self::UncarriableTestPath => {
                "the test function's path cannot be carried in the exclusion row"
            }
        }
    }
}

/// Trust (CB4): the runner-closure shape check. Pure, so every input shape is
/// unit-testable. `Ok(u)` names the test function the closure calls.
pub(super) fn runner_closure_shape(
    shape: &HarnessBodyShape,
    test_function_has_requires: impl FnOnce(DefId) -> bool,
) -> Result<DefId, HarnessShapeRefusal> {
    if shape.has_inlined_scope {
        return Err(HarnessShapeRefusal::InlinedScope);
    }
    if shape.foreign_terminator.is_some() {
        return Err(HarnessShapeRefusal::ForeignTerminator);
    }
    let mut test_call = None;
    let mut author_calls = 0usize;
    let mut assert_calls = 0usize;
    for call in &shape.calls {
        match *call {
            HarnessCall::AuthorFn { def, args } => {
                author_calls += 1;
                test_call = Some((def, args));
            }
            HarnessCall::LibtestAssertTestResult => assert_calls += 1,
            HarnessCall::LibtestMain | HarnessCall::Other => {
                return Err(HarnessShapeRefusal::UnexpectedCall);
            }
        }
    }
    let (Some((test_function, args)), 1) = (test_call, author_calls) else {
        return Err(HarnessShapeRefusal::NotExactlyOneTestCall);
    };
    if assert_calls != 1 {
        return Err(HarnessShapeRefusal::UnexpectedCall);
    }
    // `#[test]` takes no argument; `#[bench]` takes the `&mut Bencher`.
    if args > 1 {
        return Err(HarnessShapeRefusal::TestCallArity);
    }
    if test_function_has_requires(test_function) {
        return Err(HarnessShapeRefusal::TestFunctionRequires);
    }
    Ok(test_function)
}

/// Trust (CB4): the harness-`main` shape check. Pure, like
/// [`runner_closure_shape`].
pub(super) fn harness_main_shape(
    shape: &HarnessBodyShape,
    every_marked_item_is_a_builtin_descriptor: bool,
) -> Result<(), HarnessShapeRefusal> {
    if shape.has_inlined_scope {
        return Err(HarnessShapeRefusal::InlinedScope);
    }
    if shape.foreign_terminator.is_some() {
        return Err(HarnessShapeRefusal::ForeignTerminator);
    }
    if !every_marked_item_is_a_builtin_descriptor {
        return Err(HarnessShapeRefusal::AuthorMarkedItems);
    }
    if shape.calls != [HarnessCall::LibtestMain] {
        return Err(HarnessShapeRefusal::NotExactlyOneLibtestEntry);
    }
    Ok(())
}

/// Trust (CB4): what the verification gate does with one body.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum HarnessDecision {
    /// Not harness code: verified as ever.
    NotHarness,
    /// Harness code in the exact shape: excluded.
    Exclude(TestHarnessExclusion),
    /// Harness provenance, but the shape check refused: verified as ever.
    Refused { item: TestHarnessItem, refusal: HarnessShapeRefusal, test_function: Option<DefId> },
}

/// Trust (CB4): decide one body. Read-only and deterministic, so the several
/// callers of `verification_decision` all see the same answer.
pub(super) fn decide<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> HarnessDecision {
    if body.source.promoted.is_some() || !matches!(body.source.instance, ty::InstanceKind::Item(_))
    {
        return HarnessDecision::NotHarness;
    }
    let Some(local) = body.source.def_id().as_local() else {
        return HarnessDecision::NotHarness;
    };
    let Some(item) = test_harness_synthesized_item(tcx, local) else {
        return HarnessDecision::NotHarness;
    };
    match item {
        // A const is evaluated at compile time; it is not coverage-eligible
        // and never reaches this pass as a runtime body.
        TestHarnessItem::TestDescriptorConst => HarnessDecision::NotHarness,
        TestHarnessItem::TestRunnerClosure => {
            // Defense in depth on top of the resolver's own guarantee: the
            // builtin `#[test]` definition itself lives in this compiler's
            // sysroot `core`.
            if !own_expansion_macro_def(tcx, local)
                .is_some_and(|def| trust_mir_extract::def_is_in_real_sysroot_crate(tcx, def))
            {
                return HarnessDecision::Refused {
                    item,
                    refusal: HarnessShapeRefusal::NonSysrootExpander,
                    test_function: None,
                };
            }
            let shape = body_shape(tcx, body);
            match runner_closure_shape(&shape, |u| test_function_has_requires(tcx, u)) {
                Ok(test_function) => {
                    let path = trust_mir_extract::safe_def_path_str(tcx, test_function);
                    match test_harness_exclusion_reason(
                        TestHarnessExclusionItem::TestRunnerClosure,
                        Some(&path),
                    ) {
                        Some(row_reason) => HarnessDecision::Exclude(TestHarnessExclusion {
                            item,
                            test_function: Some(test_function),
                            row_reason,
                        }),
                        None => HarnessDecision::Refused {
                            item,
                            refusal: HarnessShapeRefusal::UncarriableTestPath,
                            test_function: Some(test_function),
                        },
                    }
                }
                Err(refusal) => HarnessDecision::Refused {
                    item,
                    refusal,
                    test_function: shape.calls.iter().find_map(|call| match *call {
                        HarnessCall::AuthorFn { def, .. } => Some(def),
                        _ => None,
                    }),
                },
            }
        }
        TestHarnessItem::HarnessMain => {
            let shape = body_shape(tcx, body);
            match harness_main_shape(&shape, test_harness_markers_are_all_builtin(tcx)) {
                Ok(()) => HarnessDecision::Exclude(TestHarnessExclusion {
                    item,
                    test_function: None,
                    row_reason: test_harness_exclusion_reason(
                        TestHarnessExclusionItem::HarnessMain,
                        None,
                    )
                    .expect("the harness-main reason takes no callee"),
                }),
                Err(refusal) => HarnessDecision::Refused { item, refusal, test_function: None },
            }
        }
    }
}

fn test_function_has_requires(tcx: TyCtxt<'_>, test_function: DefId) -> bool {
    trust_contracts_if_any(tcx, test_function).is_some_and(|bundle| {
        // `opaque` counts: an unparsed clause could be a precondition, and a
        // clause this check cannot read must not be dropped.
        bundle.summary.requires > 0
            || bundle.summary.opaque > 0
            || bundle
                .contracts
                .iter()
                .any(|contract| matches!(contract.kind, TrustContractKind::Requires))
    })
}

/// Extract the facts [`runner_closure_shape`] / [`harness_main_shape`] read.
fn body_shape<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> HarnessBodyShape {
    let mut shape = HarnessBodyShape {
        has_inlined_scope: body.source_scopes.iter().any(|scope| scope.inlined.is_some()),
        ..HarnessBodyShape::default()
    };
    for block in body.basic_blocks.iter() {
        let kind = &block.terminator().kind;
        match kind {
            TerminatorKind::Call { func, args, .. } => {
                shape.calls.push(classify_call(tcx, func, args.len()));
            }
            TerminatorKind::Return
            | TerminatorKind::Goto { .. }
            | TerminatorKind::UnwindResume
            | TerminatorKind::UnwindTerminate(_)
            | TerminatorKind::Unreachable => {}
            _ => {
                if shape.foreign_terminator.is_none() {
                    shape.foreign_terminator = Some(kind.name());
                }
            }
        }
    }
    shape
}

fn classify_call<'tcx>(tcx: TyCtxt<'tcx>, func: &Operand<'tcx>, args: usize) -> HarnessCall {
    let Some((def, generic_args)) = func.const_fn_def() else {
        return HarnessCall::Other;
    };
    if tcx.crate_name(def.krate) == sym::test
        && trust_mir_extract::def_is_in_sysroot_resident_crate(tcx, def)
    {
        return match tcx.item_name(def).as_str() {
            "assert_test_result" => HarnessCall::LibtestAssertTestResult,
            // Upstream 1.101: the harness pass emits `test::test_main_env_args`
            // (returning `ExitCode`) in place of `test_main_static`; both are
            // libtest's one entry point, keyed here by sysroot-`test`-crate
            // residency above, never by the name alone.
            "test_main_static"
            | "test_main_static_abort"
            | "test_main_env_args"
            | "test_main_env_args_abort" => HarnessCall::LibtestMain,
            _ => HarnessCall::Other,
        };
    }
    let Some(local) = def.as_local() else {
        return HarnessCall::Other;
    };
    if is_author_fn(tcx, local) && generic_args.non_erasable_generics().next().is_none() {
        HarnessCall::AuthorFn { def, args }
    } else {
        HarnessCall::Other
    }
}

/// A local `fn` the author wrote: not harness-synthesized, and its own span is
/// not from the builtin `#[test]` expansion (the expander re-emits the user's
/// fn with the user's context, so this holds for every real test function).
fn is_author_fn(tcx: TyCtxt<'_>, local: LocalDefId) -> bool {
    matches!(tcx.def_kind(local), DefKind::Fn)
        && test_harness_synthesized_item(tcx, local).is_none()
        && !is_from_builtin_test_expansion(tcx, local)
}

/// Per-crate count of excluded bodies, for the one human summary line.
#[derive(Default)]
struct SessionHarnessExclusionCensus {
    runner_closures: usize,
    harness_mains: usize,
}

/// Trust (CB4): write what an excluded body leaves behind — its ONE transport
/// row under JSON output (the body's one function envelope) — and count it for
/// the crate's human summary line. Never an error, never a proof.
pub(super) fn record_exclusion(tcx: TyCtxt<'_>, func_path: &str, exclusion: &TestHarnessExclusion) {
    tcx.sess.with_trust_compiler_state::<SessionHarnessExclusionCensus, _>(
        |census| match exclusion.item {
            TestHarnessItem::HarnessMain => census.harness_mains += 1,
            _ => census.runner_closures += 1,
        },
    );
    if !TrustOutputMode::parse(tcx.sess).emit_json() {
        return;
    }
    let row = TransportObligationResult {
        assumes: Vec::new(),
        gap_class: None,
        monitor: None,
        obligation_id: None,
        claim_digest_sha256: None,
        kind: TEST_HARNESS_ROW_KIND.to_string(),
        original_vc_snapshot: None,
        typed_kind: None,
        description: TEST_HARNESS_ROW_DESCRIPTION.to_string(),
        // The runner closure points at the user's test function — the code the
        // reader wrote; `main` has no location (rustc builds it at DUMMY_SP).
        location: exclusion
            .test_function
            .map(|test_function| source_span_from_rustc_span(tcx, tcx.def_span(test_function))),
        outcome: Outcome::Skipped,
        solver: TEST_HARNESS_ROW_SOLVER.to_string(),
        time_ms: 0,
        counterexample: None,
        counterexample_model: None,
        reason: Some(exclusion.row_reason.clone()),
        design_mandate: false,
        native_trust_ir: None,
        proof_evidence: None,
        grade: None,
    };
    emit_transport_json(tcx, None, func_path, &[row], 0);
}

/// Trust (CB4): under human output, say why a harness body was NOT excluded.
/// Called from the pass's verify arm only, so each body says it at most once.
pub(super) fn note_refusal<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>, func_path: &str) {
    let HarnessDecision::Refused { item, refusal, test_function } = decide(tcx, body) else {
        return;
    };
    if !TrustOutputMode::parse(tcx.sess).emit_human() {
        return;
    }
    let callee = test_function
        .map(|def| format!(" (test function `{}`)", trust_mir_extract::safe_def_path_str(tcx, def)))
        .unwrap_or_default();
    // eprintln, not a diagnostic (house style for verify-pass notes).
    eprintln!(
        "Trust: NOT EXCLUDED [{TEST_HARNESS_EXCLUSION_TAG}] `{func_path}` ({}){callee}: {}; \
         verified as ordinary code",
        item.tag(),
        refusal.describe(),
    );
}

/// Trust (CB4): the crate's ONE human summary line — never one line per body,
/// which would grow with the number of tests. The per-body inventory is the
/// machine rows. Silent when nothing was excluded.
pub(super) fn emit_crate_summary(tcx: TyCtxt<'_>) {
    if !TrustOutputMode::parse(tcx.sess).emit_human() {
        return;
    }
    let (closures, mains) =
        tcx.sess.with_trust_compiler_state::<SessionHarnessExclusionCensus, _>(|census| {
            (census.runner_closures, census.harness_mains)
        });
    if closures + mains == 0 {
        return;
    }
    eprintln!(
        "Trust: EXCLUDED [{TEST_HARNESS_EXCLUSION_TAG}] {} body/bodies rustc's libtest harness \
         synthesized ({closures} test runner closure(s), {mains} harness main(s)): not verified \
         (NOT proved); each test function they call is verified as its own body",
        closures + mains,
    );
}

#[cfg(test)]
mod tests;
