//! Trust (CB4, 2026-09-28): the compiler↔targo contract for bodies EXCLUDED
//! from the proof inventory because rustc's libtest harness synthesized them.
//!
//! Under `--test`, rustc generates code nobody wrote: one runner closure per
//! `#[test]`/`#[bench]` (`|| test::assert_test_result(the_test())`) and the
//! harness `main` (`test::test_main_static(&[..])`). Strict verification used
//! to treat that code as user proof inventory, and it cannot be proved: the
//! closure calls a generic libtest callee whose body is absent, and `main` is
//! built at `DUMMY_SP`, so every obligation in it lacks a source span. So no
//! strict crate with a `#[test]` could build its tests (CB4).
//!
//! The compiler now EXCLUDES those bodies, but only when it can show where they
//! came from (`rustc_middle::middle::trust_test_harness`, which keys on the
//! expansion that produced the item, never on a name or on the forgeable
//! `#[rustc_test_marker]` attribute) and when a MIR shape check passes. Each
//! excluded body gets exactly one transport row, in the shape this module
//! pins. That row is never proof:
//!
//! * its wire outcome is `skipped`, which every consumer that predates this
//!   module counts as not proved (fail-closed for older readers);
//! * targo counts an exact row as `excluded`, a bucket that is NOT part of the
//!   obligation total, so a run whose only rows are exclusions cannot claim a
//!   proof;
//! * a row of this kind that claims `proved`/`runtime-checked`, differs from the
//!   pinned shape in any field, or comes from a Cargo unit that is not a
//!   test-harness compile (`test`, `check-test`) is a transport defect and is
//!   counted as a genuine unknown.
//!
//! This lives in `trust-types`, the shared dependency of the compiler's verify
//! pass (the producer) and targo (the consumer), so the two ends cannot drift.
//!
//! SOUNDNESS: nothing here may contain the full-verifier classifier text
//! (`native full verifier`, `trust-full-verifier`, `fullverification::`,
//! `trust full verification failed`, `trust-verify-full`); targo's
//! `is_full_verifier_text` would otherwise misread the row as full-verifier
//! evidence. Pinned by a unit test below.

/// The disclosure tag for this exclusion class. It is the census tag in the
/// compiler, the suffix of [`TEST_HARNESS_ROW_KIND`], and the key under which
/// targo reports the count (`excluded: test-harness-synthesized`).
pub const TEST_HARNESS_EXCLUSION_TAG: &str = "test-harness-synthesized";

/// The `kind` of the one transport row an excluded harness body emits.
/// Deliberately NOT `assumption:*`: an excluded body is not a premise the
/// crate's proof rests on (nothing about any user body depends on it), and it
/// must not enter the strict lane's assumption table either.
pub const TEST_HARNESS_ROW_KIND: &str = "excluded:test-harness-synthesized";

/// The `solver` label on the exclusion row. Its own label, so no consumer has
/// to recognize the row by its text.
pub const TEST_HARNESS_ROW_SOLVER: &str = "trust-test-harness";

/// The exact `description` of the exclusion row.
pub const TEST_HARNESS_ROW_DESCRIPTION: &str =
    "rustc libtest harness code, excluded from the proof inventory: not verified (NOT proved)";

/// The Cargo compile modes that build a libtest harness. `targo trust test`
/// produces `test`; `targo trust check --tests` produces `check-test` (both
/// MEASURED on the CB4 probes). Cargo has no separate bench mode: a bench
/// target compiles in `test` mode under the bench profile.
pub const TEST_HARNESS_EXCLUSION_UNIT_MODES: [&str; 2] = ["test", "check-test"];

/// Opening of every exclusion row's `reason`. The item tag follows it.
const TEST_HARNESS_REASON_PREFIX: &str = "excluded [test-harness-synthesized] ";

/// Which synthesized body an exclusion row stands for.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TestHarnessExclusionItem {
    /// The harness entry point `main` (`test::test_main_static[_abort]`).
    HarnessMain,
    /// The runner closure a builtin `#[test]`/`#[bench]` puts in its
    /// `TestDescAndFn` descriptor.
    TestRunnerClosure,
}

impl TestHarnessExclusionItem {
    /// Stable machine tag, carried in the row's `reason`.
    #[must_use]
    pub const fn tag(self) -> &'static str {
        match self {
            Self::HarnessMain => "harness-main",
            Self::TestRunnerClosure => "test-runner-closure",
        }
    }
}

/// A parsed exclusion-row `reason`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TestHarnessExclusionReason {
    /// Which synthesized body the row stands for.
    pub item: TestHarnessExclusionItem,
    /// For a runner closure, the canonical path of the user test function it
    /// calls (which is verified as its own body). `None` for `main`.
    pub test_function: Option<String>,
}

const HARNESS_MAIN_REASON_BODY: &str = "the entry point rustc synthesizes for a --test crate; it \
     runs only the builtin #[test]/#[bench] descriptors, and each test function is verified as \
     its own body";

const RUNNER_CLOSURE_REASON_LEAD: &str = "calls `";
const RUNNER_CLOSURE_REASON_TAIL: &str = "`, which is verified as its own body";

/// The exact `reason` the compiler writes on an exclusion row. `test_function`
/// is the runner closure's one user callee and is ignored for `main`.
///
/// Returns `None` when a runner closure is given no callee, or a callee that
/// could not round-trip through [`parse_test_harness_exclusion_reason`] (empty,
/// or containing a backtick or a line break), so the producer can never write a
/// row the consumer would reject as malformed.
#[must_use]
pub fn test_harness_exclusion_reason(
    item: TestHarnessExclusionItem,
    test_function: Option<&str>,
) -> Option<String> {
    match item {
        TestHarnessExclusionItem::HarnessMain => {
            Some(format!("{TEST_HARNESS_REASON_PREFIX}{}: {HARNESS_MAIN_REASON_BODY}", item.tag()))
        }
        TestHarnessExclusionItem::TestRunnerClosure => {
            let callee = test_function.filter(|callee| is_well_formed_callee(callee))?;
            Some(format!(
                "{TEST_HARNESS_REASON_PREFIX}{}: {RUNNER_CLOSURE_REASON_LEAD}{callee}{RUNNER_CLOSURE_REASON_TAIL}",
                item.tag()
            ))
        }
    }
}

fn is_well_formed_callee(callee: &str) -> bool {
    !callee.trim().is_empty()
        && callee.trim() == callee
        && !callee.contains('`')
        && !callee.contains('\n')
        && !callee.contains('\r')
}

/// Parse an exclusion-row `reason`. Exact: anything other than the text
/// [`test_harness_exclusion_reason`] produces returns `None`.
#[must_use]
pub fn parse_test_harness_exclusion_reason(reason: &str) -> Option<TestHarnessExclusionReason> {
    let rest = reason.strip_prefix(TEST_HARNESS_REASON_PREFIX)?;
    let main_tag = TestHarnessExclusionItem::HarnessMain.tag();
    let closure_tag = TestHarnessExclusionItem::TestRunnerClosure.tag();
    if let Some(body) = rest.strip_prefix(main_tag).and_then(|rest| rest.strip_prefix(": ")) {
        return (body == HARNESS_MAIN_REASON_BODY).then_some(TestHarnessExclusionReason {
            item: TestHarnessExclusionItem::HarnessMain,
            test_function: None,
        });
    }
    let body = rest.strip_prefix(closure_tag)?.strip_prefix(": ")?;
    let callee =
        body.strip_prefix(RUNNER_CLOSURE_REASON_LEAD)?.strip_suffix(RUNNER_CLOSURE_REASON_TAIL)?;
    is_well_formed_callee(callee).then(|| TestHarnessExclusionReason {
        item: TestHarnessExclusionItem::TestRunnerClosure,
        test_function: Some(callee.to_string()),
    })
}

/// Whether a row's `kind` CLAIMS to be a test-harness exclusion. Every row that
/// does is either an exact exclusion ([`is_exact_test_harness_exclusion_row`]
/// plus the consumer's outcome and unit-mode checks) or a transport defect —
/// never an ordinary obligation.
#[must_use]
pub fn is_test_harness_exclusion_row_kind(kind: &str) -> bool {
    kind == TEST_HARNESS_ROW_KIND
}

/// Whether a row has the compiler's exact exclusion shape: kind, solver,
/// description and a parseable reason. The OUTCOME (must be `skipped`, never
/// proved or runtime-checked), the absence of a counterexample and the unit
/// mode ([`test_harness_exclusion_admits_unit_mode`]) are the consumer's
/// checks, because only the consumer has them.
#[must_use]
pub fn is_exact_test_harness_exclusion_row(
    kind: &str,
    solver: &str,
    description: &str,
    reason: Option<&str>,
) -> bool {
    is_test_harness_exclusion_row_kind(kind)
        && solver == TEST_HARNESS_ROW_SOLVER
        && description == TEST_HARNESS_ROW_DESCRIPTION
        && reason.and_then(parse_test_harness_exclusion_reason).is_some()
}

/// Whether a Cargo proof unit compiled in `mode` builds a libtest harness, and
/// may therefore carry exclusion rows. Every other mode — `build`, `check`,
/// `doctest`, a build script — makes an exclusion row a transport defect.
#[must_use]
pub fn test_harness_exclusion_admits_unit_mode(mode: &str) -> bool {
    TEST_HARNESS_EXCLUSION_UNIT_MODES.contains(&mode)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reasons_round_trip_for_both_items() {
        let main = test_harness_exclusion_reason(TestHarnessExclusionItem::HarnessMain, None)
            .expect("main reason");
        assert_eq!(
            parse_test_harness_exclusion_reason(&main),
            Some(TestHarnessExclusionReason {
                item: TestHarnessExclusionItem::HarnessMain,
                test_function: None,
            })
        );
        // `main` ignores a callee: it runs descriptors, it calls no one test.
        assert_eq!(
            test_harness_exclusion_reason(TestHarnessExclusionItem::HarnessMain, Some("x")),
            Some(main)
        );

        let closure = test_harness_exclusion_reason(
            TestHarnessExclusionItem::TestRunnerClosure,
            Some("unit::tests::empty"),
        )
        .expect("closure reason");
        assert_eq!(
            parse_test_harness_exclusion_reason(&closure),
            Some(TestHarnessExclusionReason {
                item: TestHarnessExclusionItem::TestRunnerClosure,
                test_function: Some("unit::tests::empty".to_string()),
            })
        );
    }

    #[test]
    fn a_runner_closure_reason_requires_a_well_formed_callee() {
        for bad in [None, Some(""), Some("  "), Some("a`b"), Some("a\nb"), Some(" padded")] {
            assert_eq!(
                test_harness_exclusion_reason(TestHarnessExclusionItem::TestRunnerClosure, bad),
                None,
                "{bad:?}"
            );
        }
    }

    #[test]
    fn the_reason_parser_is_exact() {
        let closure = test_harness_exclusion_reason(
            TestHarnessExclusionItem::TestRunnerClosure,
            Some("c::t"),
        )
        .expect("closure reason");
        let main = test_harness_exclusion_reason(TestHarnessExclusionItem::HarnessMain, None)
            .expect("main reason");
        for bad in [
            String::new(),
            format!("{closure} "),
            format!(" {closure}"),
            closure.replace("test-runner-closure", "harness-main"),
            main.replace("harness-main", "test-runner-closure"),
            format!("{main}."),
            closure.replace("c::t", ""),
            closure.replace("c::t", "a`b"),
            "excluded [test-harness-synthesized] other: x".to_string(),
        ] {
            assert_eq!(parse_test_harness_exclusion_reason(&bad), None, "{bad:?}");
        }
    }

    #[test]
    fn the_exact_row_shape_checks_every_pinned_field() {
        let reason = test_harness_exclusion_reason(
            TestHarnessExclusionItem::TestRunnerClosure,
            Some("c::t"),
        );
        let reason = reason.as_deref();
        assert!(is_exact_test_harness_exclusion_row(
            TEST_HARNESS_ROW_KIND,
            TEST_HARNESS_ROW_SOLVER,
            TEST_HARNESS_ROW_DESCRIPTION,
            reason,
        ));
        // Each field is load-bearing: a row that gets any one wrong is not an
        // exclusion (the consumer counts it as a defect).
        assert!(!is_exact_test_harness_exclusion_row(
            "assumption:test-harness-synthesized",
            TEST_HARNESS_ROW_SOLVER,
            TEST_HARNESS_ROW_DESCRIPTION,
            reason,
        ));
        assert!(!is_exact_test_harness_exclusion_row(
            TEST_HARNESS_ROW_KIND,
            "trust-policy",
            TEST_HARNESS_ROW_DESCRIPTION,
            reason,
        ));
        assert!(!is_exact_test_harness_exclusion_row(
            TEST_HARNESS_ROW_KIND,
            TEST_HARNESS_ROW_SOLVER,
            "rustc libtest harness code",
            reason,
        ));
        assert!(!is_exact_test_harness_exclusion_row(
            TEST_HARNESS_ROW_KIND,
            TEST_HARNESS_ROW_SOLVER,
            TEST_HARNESS_ROW_DESCRIPTION,
            None,
        ));
        assert!(!is_exact_test_harness_exclusion_row(
            TEST_HARNESS_ROW_KIND,
            TEST_HARNESS_ROW_SOLVER,
            TEST_HARNESS_ROW_DESCRIPTION,
            Some("excluded"),
        ));
    }

    #[test]
    fn only_test_harness_compile_modes_admit_an_exclusion() {
        assert!(test_harness_exclusion_admits_unit_mode("test"));
        assert!(test_harness_exclusion_admits_unit_mode("check-test"));
        for mode in [
            "build",
            "check",
            "doctest",
            "doc",
            "docscrape",
            "run-custom-build",
            "bench",
            "",
            "Test",
        ] {
            assert!(!test_harness_exclusion_admits_unit_mode(mode), "{mode}");
        }
    }

    #[test]
    fn the_row_is_not_an_assumption_nor_full_verifier_text() {
        assert!(!TEST_HARNESS_ROW_KIND.starts_with("assumption:"));
        assert!(!TEST_HARNESS_ROW_KIND.starts_with("transport:"));
        assert_eq!(
            TEST_HARNESS_ROW_KIND.strip_prefix("excluded:"),
            Some(TEST_HARNESS_EXCLUSION_TAG)
        );
        let main = test_harness_exclusion_reason(TestHarnessExclusionItem::HarnessMain, None)
            .expect("main reason");
        let closure = test_harness_exclusion_reason(
            TestHarnessExclusionItem::TestRunnerClosure,
            Some("c::t"),
        )
        .expect("closure reason");
        for text in [
            TEST_HARNESS_ROW_KIND,
            TEST_HARNESS_ROW_SOLVER,
            TEST_HARNESS_ROW_DESCRIPTION,
            main.as_str(),
            closure.as_str(),
        ] {
            let lower = text.to_ascii_lowercase();
            for marker in [
                "native full verifier",
                "trust-full-verifier",
                "fullverification::",
                "trust full verification failed",
                "trust-verify-full",
                "full verifier",
                "full-verifier",
            ] {
                assert!(!lower.contains(marker), "{text:?} contains {marker:?}");
            }
        }
    }
}
