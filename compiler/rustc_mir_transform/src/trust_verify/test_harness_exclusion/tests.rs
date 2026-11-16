use rustc_hir::def_id::{CrateNum, DefIndex};

use super::*;

fn def(index: u32) -> DefId {
    DefId { krate: CrateNum::from_u32(0), index: DefIndex::from_u32(index) }
}

fn shape(calls: &[HarnessCall]) -> HarnessBodyShape {
    HarnessBodyShape { calls: calls.to_vec(), ..HarnessBodyShape::default() }
}

const U: u32 = 7;

fn test_call() -> HarnessCall {
    HarnessCall::AuthorFn { def: def(U), args: 0 }
}

#[test]
fn the_builtin_runner_closure_is_excluded_and_names_its_test() {
    // `_2 = u(); _0 = assert_test_result::<()>(move _2)`, in either order.
    for calls in [
        [test_call(), HarnessCall::LibtestAssertTestResult],
        [HarnessCall::LibtestAssertTestResult, test_call()],
    ] {
        assert_eq!(runner_closure_shape(&shape(&calls), |_| false), Ok(def(U)));
    }
    // `#[bench]`: `u(b)`.
    let bench =
        [HarnessCall::AuthorFn { def: def(U), args: 1 }, HarnessCall::LibtestAssertTestResult];
    assert_eq!(runner_closure_shape(&shape(&bench), |_| false), Ok(def(U)));
}

/// Critique MUST-FIX 3: exact under MIR inlining.
#[test]
fn an_inlined_scope_refuses_exclusion_whatever_the_calls() {
    let mut inlined = shape(&[test_call(), HarnessCall::LibtestAssertTestResult]);
    inlined.has_inlined_scope = true;
    assert_eq!(runner_closure_shape(&inlined, |_| false), Err(HarnessShapeRefusal::InlinedScope));
    // The MEASURED `requires false` case: the call to `u` was inlined away,
    // leaving only `assert_test_result(const ())`. Refused twice over.
    let mut folded = shape(&[HarnessCall::LibtestAssertTestResult]);
    assert_eq!(
        runner_closure_shape(&folded, |_| false),
        Err(HarnessShapeRefusal::NotExactlyOneTestCall)
    );
    folded.has_inlined_scope = true;
    assert_eq!(runner_closure_shape(&folded, |_| false), Err(HarnessShapeRefusal::InlinedScope));
    let mut main = shape(&[HarnessCall::LibtestMain]);
    main.has_inlined_scope = true;
    assert_eq!(harness_main_shape(&main, true), Err(HarnessShapeRefusal::InlinedScope));
}

#[test]
fn a_closure_that_is_not_exactly_the_harness_shape_is_verified() {
    let other = HarnessCall::AuthorFn { def: def(U + 1), args: 0 };
    for (calls, refusal) in [
        (vec![], HarnessShapeRefusal::NotExactlyOneTestCall),
        (vec![test_call()], HarnessShapeRefusal::UnexpectedCall),
        (
            vec![test_call(), other, HarnessCall::LibtestAssertTestResult],
            HarnessShapeRefusal::NotExactlyOneTestCall,
        ),
        (
            vec![test_call(), test_call(), HarnessCall::LibtestAssertTestResult],
            HarnessShapeRefusal::NotExactlyOneTestCall,
        ),
        (
            vec![test_call(), HarnessCall::LibtestAssertTestResult, HarnessCall::Other],
            HarnessShapeRefusal::UnexpectedCall,
        ),
        (
            vec![test_call(), HarnessCall::LibtestMain, HarnessCall::LibtestAssertTestResult],
            HarnessShapeRefusal::UnexpectedCall,
        ),
        (
            vec![
                test_call(),
                HarnessCall::LibtestAssertTestResult,
                HarnessCall::LibtestAssertTestResult,
            ],
            HarnessShapeRefusal::UnexpectedCall,
        ),
        (
            vec![
                HarnessCall::AuthorFn { def: def(U), args: 2 },
                HarnessCall::LibtestAssertTestResult,
            ],
            HarnessShapeRefusal::TestCallArity,
        ),
    ] {
        assert_eq!(runner_closure_shape(&shape(&calls), |_| false), Err(refusal), "{calls:?}");
    }
    let mut branchy = shape(&[test_call(), HarnessCall::LibtestAssertTestResult]);
    branchy.foreign_terminator = Some("SwitchInt");
    assert_eq!(
        runner_closure_shape(&branchy, |_| false),
        Err(HarnessShapeRefusal::ForeignTerminator)
    );
}

/// The one user obligation the closure holds: the call-site `requires` row.
#[test]
fn a_test_function_with_requires_keeps_its_closure_verified() {
    let calls = [test_call(), HarnessCall::LibtestAssertTestResult];
    let mut asked = None;
    assert_eq!(
        runner_closure_shape(&shape(&calls), |u| {
            asked = Some(u);
            true
        }),
        Err(HarnessShapeRefusal::TestFunctionRequires)
    );
    assert_eq!(asked, Some(def(U)), "the requires check asks about the called test fn");
}

#[test]
fn main_is_excluded_only_in_the_builtin_shape_with_builtin_markers() {
    assert_eq!(harness_main_shape(&shape(&[HarnessCall::LibtestMain]), true), Ok(()));
    // SHOULD-FIX: a user `#[test_case]` descriptor is run by a `main` of the
    // builtin shape; that main is verified.
    assert_eq!(
        harness_main_shape(&shape(&[HarnessCall::LibtestMain]), false),
        Err(HarnessShapeRefusal::AuthorMarkedItems)
    );
    // A custom `#![test_runner]`: main calls the author's runner.
    for calls in [
        vec![HarnessCall::AuthorFn { def: def(U), args: 1 }],
        vec![HarnessCall::Other],
        vec![],
        vec![HarnessCall::LibtestMain, HarnessCall::LibtestMain],
        vec![HarnessCall::LibtestMain, HarnessCall::LibtestAssertTestResult],
    ] {
        assert_eq!(
            harness_main_shape(&shape(&calls), true),
            Err(HarnessShapeRefusal::NotExactlyOneLibtestEntry),
            "{calls:?}"
        );
    }
}

#[test]
fn every_refusal_has_a_distinct_description() {
    let all = [
        HarnessShapeRefusal::InlinedScope,
        HarnessShapeRefusal::ForeignTerminator,
        HarnessShapeRefusal::NotExactlyOneTestCall,
        HarnessShapeRefusal::UnexpectedCall,
        HarnessShapeRefusal::TestCallArity,
        HarnessShapeRefusal::TestFunctionRequires,
        HarnessShapeRefusal::NonSysrootExpander,
        HarnessShapeRefusal::AuthorMarkedItems,
        HarnessShapeRefusal::NotExactlyOneLibtestEntry,
        HarnessShapeRefusal::UncarriableTestPath,
    ];
    let mut descriptions = all.iter().map(|refusal| refusal.describe()).collect::<Vec<_>>();
    descriptions.sort_unstable();
    descriptions.dedup();
    assert_eq!(descriptions.len(), all.len());
}
