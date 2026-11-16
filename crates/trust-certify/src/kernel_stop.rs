// trust-certify: the clean kernel's re-check, with the stop that ended it named.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

//! The one entry for the clean kernel's re-check of a certificate (plan P4a,
//! slice 2): every lane's `term : goal` check of the proof it mints, of the
//! payload it round-trips, and a frontend goal's discharge. One judgment that
//! re-checks no certificate takes it as well, on critic B1's list: the
//! citation route's rung selector (`clean_island::theorem_states_goal`). It
//! can never mint a discharge, but a spent count turns its `true` into a
//! `false`, which changes WHICH failing rung, and so which failing verdict, is
//! reported.
//!
//! Every other kernel call stays outside this entry (`docs/DECISION_QUEUE.md`,
//! KERNEL-STOP-1 point 8):
//!
//! * the calls that re-check no certificate: a goal-typing gate, an island
//!   unfolding, a model evaluation, the census's own bounded classification;
//! * `cert_meter::grade`, the citation route's and the island audits' real
//!   authority, whose checker is built inside clean's `audit_certification`,
//!   so this entry cannot read its count; the compiler reaches it directly,
//!   with no run around it;
//! * the scalar-model registrations, which their callers reach directly with
//!   no certify run reading a stop there. Their `Err` text may name a mismatch
//!   a spent count caused (the third bullet below), so a count-ended decline
//!   there can still read as a rejection; carrying that stop is the caller's
//!   slice, as it is for `cert_meter::grade`.
//!
//! Every re-check builds a fresh [`TypeChecker`], and every [`TypeChecker`]
//! carries the kernel's own deterministic heartbeat count
//! ([`clean_kernel::tc::DEFAULT_HEARTBEAT_LIMIT`], 2,000,000): `whnf`,
//! `is_def_eq` and `infer_type` each draw on it, and once it is spent
//! `check_type` answers `HeartbeatExceeded` and `is_def_eq` bails `false`.
//! Before this entry each re-check site folded that answer into a plain
//! decline (`.is_ok()`), so a certificate the count cut short read exactly
//! like an uncertifiable formula: no stop, and the decline memoized as pure.
//!
//! A site now hands its checker to [`check_type`] or [`is_def_eq`], and a
//! decline the count ended records [`StopCause::Effort`] as the run's stop
//! (the crate root's `RUN_STOP`, through `note_certify_stop`), beside the
//! run's other stops. `CertifyOutcome` reads it today; the entry that reports
//! a run's stop with its evidence (L4's C06a) carries it to the row.
//!
//! In production one routed site runs inside a certify run that reads its
//! stop: the crate root's `kernel_checks_false_for` (the Int and Real lanes).
//! The compiler reaches `clean_island`'s two sites directly, with no run
//! around them, and the other routed sites have no compiler or targo-trust
//! caller. A stop recorded with no open scope is read by nothing:
//! `with_stop_scope` restores that outer record around each run, so it never
//! reaches a run it did not stop. A caller with no run to read the stop asks
//! [`check_type_naming_stop`] for it and names it in its own verdict, as
//! `clean_island::kernel_prove_ensures_by_defeq_in` does in its detail.
//!
//! * The count is the kernel's own. Nothing here adds, sizes or reads a clock.
//! * Only a DECLINE is a stop. A check the kernel accepted finished; an
//!   accepted term is a proof whatever the counter reads afterwards.
//! * A decline with the count spent is a stop even when the kernel's error is
//!   not `HeartbeatExceeded`: a spent count makes `whnf` return unreduced
//!   terms, and the error that follows may name the mismatch it caused. The
//!   count is deterministic, so naming such a decline `effort` costs only the
//!   memo entry (fail-closed).
//! * The kernel's AMBIENT declaration budget (`clean_kernel::tc::decl_budget`)
//!   also makes the checker read spent. No trust-certify path arms it, and its
//!   own documentation says it is not exactly reproducible, so a decline it
//!   ended is recorded as [`StopCause::Unclassified`], never as `effort`.
//! * PURITY is unchanged: a stopped run is recomputed, never stored, until L4b
//!   rules otherwise (`CertifyOutcome` in the crate root).

use clean_kernel::{Expr, TypeChecker, TypeError};
use trust_types::determinism::StopCause;

/// `checker.check_type(term, goal)`, recording the stop of a decline the
/// kernel's count ended (module docs).
pub(crate) fn check_type(
    checker: TypeChecker<'_>,
    term: &Expr,
    goal: &Expr,
) -> Result<(), TypeError> {
    check_type_naming_stop(checker, term, goal).0
}

/// [`check_type`], also answering the stop it recorded (`None` for an
/// accepted check and for a decline the kernel reached with its count to
/// spare), for a caller outside any certify run that names the stop in its
/// own verdict.
pub(crate) fn check_type_naming_stop(
    checker: TypeChecker<'_>,
    term: &Expr,
    goal: &Expr,
) -> (Result<(), TypeError>, Option<StopCause>) {
    #[cfg(test)]
    let checker = census::arm(checker);
    let verdict = checker.check_type(term, goal);
    #[cfg(test)]
    census::record(&checker);
    let stop = match &verdict {
        Ok(()) => None,
        Err(error) => note_decline(&checker, Some(error)),
    };
    (verdict, stop)
}

/// `checker.is_def_eq(left, right)`, recording the stop of a `false` the
/// kernel's count ended (module docs).
pub(crate) fn is_def_eq(checker: TypeChecker<'_>, left: &Expr, right: &Expr) -> bool {
    #[cfg(test)]
    let checker = census::arm(checker);
    let equal = checker.is_def_eq(left, right);
    #[cfg(test)]
    census::record(&checker);
    if !equal {
        note_decline(&checker, None);
    }
    equal
}

/// Record the stop of one declined re-check, if a count ended it, and answer
/// it.
fn note_decline(checker: &TypeChecker<'_>, error: Option<&TypeError>) -> Option<StopCause> {
    let ambient_spent = clean_kernel::tc::declaration_budget_exhausted()
        || matches!(error, Some(TypeError::DeclarationBudgetExhausted { .. }));
    let heartbeat_spent =
        matches!(error, Some(TypeError::HeartbeatExceeded { .. })) || checker.heartbeat_spent();
    let stop = decline_stop(ambient_spent, heartbeat_spent);
    if let Some(cause) = stop {
        crate::note_certify_stop(cause);
    }
    stop
}

/// The stop a declined re-check reports: `unclassified` when the ambient
/// declaration budget ran out, `effort` when the checker's heartbeat count
/// did, and none for a decline the kernel reached with its count to spare.
const fn decline_stop(ambient_spent: bool, heartbeat_spent: bool) -> Option<StopCause> {
    if ambient_spent {
        Some(StopCause::Unclassified)
    } else if heartbeat_spent {
        Some(StopCause::Effort)
    } else {
        None
    }
}

/// Test-only census of the heartbeats the kernel re-checks of one run spend,
/// so a test can hold a certificate's count fixed across runs and threads.
/// That the count is a function of the certificate is what L4b needs before
/// PURITY could memoize an `effort` stop. It rides the crate's thread hops
/// with the stop (`on_stack_carrying_stop`).
#[cfg(test)]
pub(crate) mod census {
    use std::cell::Cell;
    use std::sync::atomic::{AtomicU64, Ordering};

    use clean_kernel::TypeChecker;

    thread_local! {
        /// `Some(total)` while a [`measure`] is armed on this thread.
        static SPENT: Cell<Option<u64>> = const { Cell::new(None) };
    }

    /// Run `work` with the census armed, and return its answer with the
    /// heartbeats every re-check in it spent, on any thread it hopped to.
    pub(crate) fn measure<T>(work: impl FnOnce() -> T) -> (T, u64) {
        let outer = SPENT.replace(Some(0));
        let answer = work();
        let spent = SPENT.replace(outer).unwrap_or(0);
        add(spent);
        (answer, spent)
    }

    /// Turn the checker's profiler on while a census is armed.
    pub(super) fn arm(mut checker: TypeChecker<'_>) -> TypeChecker<'_> {
        if SPENT.get().is_some() {
            checker.enable_heartbeat_profiler();
        }
        checker
    }

    /// Add what the checker spent to the armed census.
    pub(super) fn record(checker: &TypeChecker<'_>) {
        if let Some(profile) = checker.heartbeat_profile() {
            add(profile.total());
        }
    }

    fn add(spent: u64) {
        SPENT.with(|cell| {
            if let Some(total) = cell.get() {
                cell.set(Some(total + spent));
            }
        });
    }

    /// The census across one thread hop: armed on the worker iff it is armed
    /// on the caller, and what the worker spent added back on the caller.
    pub(crate) struct Hop {
        armed: bool,
        spent: AtomicU64,
    }

    impl Hop {
        /// On the caller, before the hop.
        pub(crate) fn leave() -> Self {
            Self { armed: SPENT.get().is_some(), spent: AtomicU64::new(0) }
        }

        /// On the worker, before its work.
        pub(crate) fn arrive(&self) {
            if self.armed {
                SPENT.set(Some(0));
            }
        }

        /// On the worker, after its work.
        pub(crate) fn depart(&self) {
            if self.armed {
                self.spent.store(SPENT.take().unwrap_or(0), Ordering::Relaxed);
            }
        }

        /// On the caller, after the join.
        pub(crate) fn home(&self) {
            if self.armed {
                add(self.spent.load(Ordering::Relaxed));
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use clean_kernel::{Environment, LocalContext};
    use trust_ir::ProofEvidence;
    use trust_types::determinism::StopCause;
    use trust_types::{Formula, Sort};

    use super::{census, check_type, decline_stop, is_def_eq};
    use crate::{
        ObligationIdentity, ReducedContext, TypeChecker, certify_lanes, certify_violation,
        deserialize_context, deserialize_term, false_expr, int_ty, on_certify_stack,
        with_stop_scope,
    };

    fn var(name: &str) -> Formula {
        Formula::Var(name.to_string(), Sort::Int)
    }

    fn lt(a: Formula, b: Formula) -> Formula {
        Formula::Lt(Box::new(a), Box::new(b))
    }

    /// `x < 0 ∧ 0 < x`, which the Int lane certifies through ay and clean-auto.
    fn contradiction() -> Formula {
        Formula::And(vec![lt(var("x"), Formula::Int(0)), lt(Formula::Int(0), var("x"))])
    }

    /// The term and context bytes of the Int lane's certificate of
    /// [`contradiction`], minted in a stop scope of their own: the ay run that
    /// mints them is outside every scope a test below measures, so its stop can
    /// never be read as the stop of the re-check under test.
    fn certificate_bytes() -> (Vec<u8>, Vec<u8>) {
        let (evidence, stop) = with_stop_scope(|| certify_violation(&contradiction()));
        let Some(ProofEvidence::CleanCic { term, context, .. }) = evidence else {
            panic!(
                "x < 0 ∧ 0 < x must certify (the run's stop: {stop:?}; a stop means a clock \
                 or the host's load ended the run, not that the re-check is wrong)"
            );
        };
        (term, context)
    }

    /// The inputs of the Int lane's re-check `term : False` for
    /// [`certificate_bytes`]: its environment, local context and term. It only
    /// decodes; no lane, solver or routed re-check runs here.
    fn certificate(
        (term, context): &(Vec<u8>, Vec<u8>),
    ) -> (Environment, LocalContext, clean_kernel::Expr) {
        let term = deserialize_term(term).expect("term");
        let reduced: ReducedContext = deserialize_context(context).expect("context");
        let env = crate::build_env(&BTreeSet::from(["x".to_string()])).expect("env");
        (env, reduced.into_context(), term)
    }

    /// Re-check [`certificate`] on the certification stack (the kernel
    /// recurses to the depth of the term), inside a fresh stop scope, with a
    /// checker `limit` heartbeats deep (`None`: the kernel's own count) and
    /// against `goal` (`None`: `False`). Answers whether the kernel accepted,
    /// whether it answered `HeartbeatExceeded`, and the run's stop.
    fn recheck(
        limit: Option<u32>,
        goal: Option<fn() -> clean_kernel::Expr>,
    ) -> (bool, bool, Option<StopCause>) {
        let bytes = certificate_bytes();
        let (answer, stop) = with_stop_scope(|| {
            on_certify_stack(|| {
                let (env, ctx, term) = certificate(&bytes);
                let mut checker = TypeChecker::with_context(&env, ctx);
                if let Some(limit) = limit {
                    checker.set_heartbeat_limit(limit);
                }
                let goal = goal.map_or_else(false_expr, |goal| goal());
                let verdict = check_type(checker, &term, &goal);
                Some((
                    verdict.is_ok(),
                    matches!(verdict, Err(clean_kernel::TypeError::HeartbeatExceeded { .. })),
                ))
            })
        });
        let (accepted, exceeded) = answer.expect("the certification stack ran");
        (accepted, exceeded, stop)
    }

    #[test]
    fn the_stop_of_a_decline_is_the_count_that_ended_it() {
        assert_eq!(decline_stop(false, false), None);
        assert_eq!(decline_stop(false, true), Some(StopCause::Effort));
        assert_eq!(decline_stop(true, false), Some(StopCause::Unclassified));
        assert_eq!(decline_stop(true, true), Some(StopCause::Unclassified));
    }

    /// With the count to spare the kernel accepts the certificate and no stop
    /// is recorded; with a count of one heartbeat the same check declines and
    /// the run's stop is `effort`, where before it was an unexplained decline.
    #[test]
    fn a_re_check_the_heartbeat_count_ended_is_an_effort_stop() {
        let (accepted, _, stop) = recheck(None, None);
        assert!(accepted, "the certificate re-checks with the kernel's own count");
        assert_eq!(stop, None, "an accepted re-check is not a stop");

        let (accepted, exceeded, stop) = recheck(Some(1), None);
        assert!(!accepted && exceeded, "one heartbeat cannot re-check the certificate");
        assert_eq!(stop, Some(StopCause::Effort));
    }

    /// A real rejection, reached with the count to spare, stays a plain
    /// decline: no stop, so the run may be memoized as before.
    #[test]
    fn a_rejection_with_the_count_to_spare_is_not_a_stop() {
        let (accepted, exceeded, stop) = recheck(None, Some(int_ty));
        assert!(!accepted && !exceeded, "a proof of False is not an Int");
        assert_eq!(stop, None);
    }

    /// `is_def_eq` bails `false` once the count is spent; that `false` is an
    /// `effort` stop, and a `false` with the count to spare is not.
    #[test]
    fn a_def_eq_the_heartbeat_count_ended_is_an_effort_stop() {
        let bytes = certificate_bytes();
        let def_eq = |limit: Option<u32>| {
            with_stop_scope(|| {
                on_certify_stack(|| {
                    let (env, ctx, _) = certificate(&bytes);
                    let mut checker = TypeChecker::with_context(&env, ctx);
                    if let Some(limit) = limit {
                        checker.set_heartbeat_limit(limit);
                    }
                    Some(is_def_eq(checker, &false_expr(), &int_ty()))
                })
            })
        };
        assert_eq!(def_eq(Some(1)), (Some(false), Some(StopCause::Effort)));
        assert_eq!(def_eq(None), (Some(false), None));
    }

    /// The kernel's ambient declaration budget is not the heartbeat count and
    /// is not exactly reproducible: a decline it ended reads `unclassified`.
    #[test]
    fn a_re_check_the_declaration_budget_ended_is_unclassified() {
        let bytes = certificate_bytes();
        let (accepted, stop) = with_stop_scope(|| {
            on_certify_stack(|| {
                let (env, ctx, term) = certificate(&bytes);
                clean_kernel::tc::set_declaration_budget(1);
                let accepted =
                    check_type(TypeChecker::with_context(&env, ctx), &term, &false_expr()).is_ok();
                clean_kernel::tc::clear_declaration_budget();
                Some(accepted)
            })
        });
        assert_eq!(accepted, Some(false));
        assert_eq!(stop, Some(StopCause::Unclassified));
    }

    /// P4a slice 2's measurement: the heartbeats the kernel re-checks spend on
    /// a certificate are a function of the certificate. Over a few certifying
    /// fixtures (the Int lane's ay reconstruction, a linear sum, a closed
    /// constant, and the linear-REAL lane, which runs on a thread of its own),
    /// ten runs in a row and eight threads at once give each the same
    /// certificate bytes and the same heartbeats. Each run goes below the memo,
    /// so every run re-checks; a lane that hands a synthesized sub-obligation
    /// back to the memoized entry (the unsigned-BV order lane does) would
    /// re-check only on its first run, so none is a fixture here.
    #[test]
    fn heartbeats_per_certificate_are_identical_across_runs_and_threads() {
        let real_x = || Box::new(Formula::Var("x".to_string(), Sort::Real));
        let sum = || Formula::Add(Box::new(var("a")), Box::new(var("b")));
        let two = || Formula::Int(2);
        let fixtures = vec![
            contradiction(),
            Formula::And(vec![lt(sum(), Formula::Int(0)), lt(Formula::Int(0), sum())]),
            Formula::And(vec![
                Formula::Le(Box::new(Formula::Int(i128::from(i64::MIN))), Box::new(two())),
                Formula::Le(Box::new(two()), Box::new(Formula::Int(i128::from(i64::MAX)))),
                Formula::Or(vec![
                    lt(two(), Formula::Int(0)),
                    Formula::Ge(Box::new(two()), Box::new(Formula::Int(32))),
                ]),
            ]),
            Formula::And(vec![
                Formula::Le(real_x(), Box::new(Formula::rat_from_int(1))),
                Formula::Ge(real_x(), Box::new(Formula::rat_from_int(2))),
            ]),
        ];
        let measure_all = || -> Vec<(Vec<u8>, u64)> {
            fixtures
                .iter()
                .map(|violation| {
                    let identity = ObligationIdentity::from_violation(violation).expect("identity");
                    let ((evidence, stop), spent) = census::measure(|| {
                        with_stop_scope(|| on_certify_stack(|| certify_lanes(violation, &identity)))
                    });
                    let Some(ProofEvidence::CleanCic { term, context, .. }) = evidence else {
                        panic!(
                            "fixture must certify: {violation:?} (the run's stop: {stop:?}; a \
                             stop means a clock or the host's load ended the run, which is no \
                             finding about the heartbeat count's determinism)"
                        );
                    };
                    assert!(spent > 0, "the census saw no re-check of {violation:?}");
                    ([term, context].concat(), spent)
                })
                .collect()
        };
        let first = measure_all();
        for run in 1..10 {
            assert_eq!(measure_all(), first, "run {run} differs from run 0");
        }
        let parallel: Vec<Vec<(Vec<u8>, u64)>> = std::thread::scope(|scope| {
            let workers: Vec<_> = (0..8).map(|_| scope.spawn(&measure_all)).collect();
            workers.into_iter().map(|worker| worker.join().expect("worker")).collect()
        });
        for (thread, measured) in parallel.iter().enumerate() {
            assert_eq!(measured, &first, "thread {thread} of 8 differs from the serial run");
        }
        let heartbeats: Vec<u64> = first.iter().map(|(_, spent)| *spent).collect();
        eprintln!("KERNEL-HEARTBEATS per certificate: {heartbeats:?}");
    }
}
