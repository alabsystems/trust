// Tests for crate::determinism.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use super::*;

fn every_cause() -> Vec<StopCause> {
    // An exhaustive match, so a new variant fails to compile here until it is
    // added to `ALL` and classified.
    let witness = |cause: StopCause| match cause {
        StopCause::Solved
        | StopCause::Steps
        | StopCause::Effort
        | StopCause::TermMemory
        | StopCause::Frames
        | StopCause::SolverIncomplete
        | StopCause::Unsupported
        | StopCause::NotDispatched
        | StopCause::WallBackstop
        | StopCause::RssBackstop
        | StopCause::SolverFault
        | StopCause::Unclassified
        | StopCause::AdmissionRefused => cause,
    };
    StopCause::ALL.into_iter().map(witness).collect()
}

#[test]
fn every_cause_round_trips_its_canonical_spelling_and_all_is_sorted() {
    let causes = every_cause();
    assert_eq!(causes.len(), 13);
    for cause in &causes {
        assert_eq!(StopCause::parse(cause.as_str()), Some(*cause));
        let json = serde_json::to_string(cause).unwrap();
        assert_eq!(json, format!("\"{}\"", cause.as_str()));
        assert_eq!(serde_json::from_str::<StopCause>(&json).unwrap(), *cause);
    }
    let names: Vec<&str> = causes.iter().map(|cause| cause.as_str()).collect();
    let mut sorted = names.clone();
    sorted.sort_unstable();
    sorted.dedup();
    assert_eq!(names, sorted, "ALL must be the complete set in canonical-name order");
    assert_eq!(StopCause::parse("timeout"), None, "only canonical spellings parse");
    assert_eq!(StopCause::parse("Solved"), None);
}

#[test]
fn only_counts_are_deterministic() {
    use Reproducibility::*;
    let expected = [
        (StopCause::Solved, Deterministic),
        (StopCause::Steps, Deterministic),
        (StopCause::Effort, Deterministic),
        (StopCause::TermMemory, Deterministic),
        (StopCause::Frames, Deterministic),
        (StopCause::SolverIncomplete, Deterministic),
        (StopCause::Unsupported, Deterministic),
        (StopCause::NotDispatched, Deterministic),
        (StopCause::WallBackstop, NotReproducible),
        (StopCause::RssBackstop, NotReproducible),
        (StopCause::SolverFault, NotReproducible),
        (StopCause::Unclassified, NotReproducible),
        (StopCause::AdmissionRefused, CouldNotRun),
    ];
    assert_eq!(expected.len(), every_cause().len());
    for (cause, class) in expected {
        assert_eq!(cause.reproducibility(), class, "{cause}");
    }
}

#[test]
fn a_stamped_reason_reads_back_its_cause() {
    let reason = StopCause::Effort.stamp("in-process ay returned unknown: resourceout");
    assert_eq!(reason, "in-process ay returned unknown: resourceout [stop:effort]");
    assert_eq!(StopCause::from_reason(&reason), Some(StopCause::Effort));
    // The detail keeps its prefix, which existing consumers match on.
    assert!(reason.starts_with("in-process ay returned unknown"));
    assert_eq!(StopCause::Steps.stamp(""), "[stop:steps]");
}

#[test]
fn restamping_replaces_the_trailing_token_instead_of_stacking_two() {
    let first = StopCause::Effort.stamp("solver returned unknown");
    let second = StopCause::SolverIncomplete.stamp(&first);
    assert_eq!(second, "solver returned unknown [stop:solver-incomplete]");
    assert_eq!(StopCause::from_reason(&second), Some(StopCause::SolverIncomplete));
}

/// Plan §2/§3.1, the combination rule: a wrapper that states a DETERMINISTIC
/// cause can never launder a clock, an unexplained stop or a refused admission
/// underneath it into a reproducible row.
#[test]
fn a_wrapper_cannot_launder_a_non_reproducible_cause() {
    for inner in [
        StopCause::Unclassified,
        StopCause::WallBackstop,
        StopCause::RssBackstop,
        StopCause::SolverFault,
        StopCause::AdmissionRefused,
    ] {
        for outer in every_cause()
            .into_iter()
            .filter(|cause| cause.reproducibility() == Reproducibility::Deterministic)
        {
            let restamped = outer.stamp(&inner.stamp("solver returned unknown"));
            assert_eq!(
                StopCause::from_reason(&restamped),
                Some(inner),
                "restamping {inner} as {outer} must keep {inner}: {restamped}"
            );
            let quoted = outer.stamp(&format!("retry after ({})", inner.stamp("first attempt")));
            assert_eq!(
                StopCause::from_reason(&quoted),
                Some(inner),
                "a quoted {inner} under a {outer} wrapper must keep {inner}: {quoted}"
            );
        }
    }
    // A refused admission is worse than any clock.
    let clock_then_refusal =
        StopCause::WallBackstop.stamp(&StopCause::AdmissionRefused.stamp("trustd unreachable"));
    assert_eq!(StopCause::from_reason(&clock_then_refusal), Some(StopCause::AdmissionRefused));
}

#[test]
fn combining_keeps_the_least_reproducible_cause_and_otherwise_the_outer_one() {
    for inner in every_cause() {
        for outer in every_cause() {
            let combined = StopCause::combine(inner, outer);
            let (ri, ro) = (inner.reproducibility().rank(), outer.reproducibility().rank());
            assert_eq!(combined.reproducibility().rank(), ri.max(ro), "{inner} + {outer}");
            if ri == ro {
                let expected = if outer == StopCause::Unclassified { inner } else { outer };
                assert_eq!(combined, expected, "{inner} + {outer}");
            }
        }
    }
    // Within the non-reproducible class, a stated clock is not replaced by
    // "nobody said why", and a stated cause does replace an unexplained one.
    assert_eq!(
        StopCause::combine(StopCause::WallBackstop, StopCause::Unclassified),
        StopCause::WallBackstop
    );
    assert_eq!(
        StopCause::combine(StopCause::Unclassified, StopCause::WallBackstop),
        StopCause::WallBackstop
    );
}

#[test]
fn a_wrapper_that_states_its_own_cause_last_keeps_it() {
    let inner = StopCause::Effort.stamp("resourceout");
    let wrapped = StopCause::WallBackstop.stamp(&format!("relaxation retry after ({inner})"));
    assert_eq!(StopCause::from_reason(&wrapped), Some(StopCause::WallBackstop));
    // Two deterministic statements: the outer one decides.
    let decided = StopCause::Unsupported.stamp(&format!("declined after ({inner})"));
    assert_eq!(StopCause::from_reason(&decided), Some(StopCause::Unsupported));
    // A wrapper that states nothing inherits the inner statement.
    let quoted = format!("fallback because: {inner}");
    assert_eq!(StopCause::from_reason(&quoted), Some(StopCause::Effort));
}

#[test]
fn text_that_merely_looks_like_a_token_is_not_a_cause() {
    assert_eq!(StopCause::from_reason("solver returned unknown"), None);
    assert_eq!(StopCause::from_reason("[stop:timeout] legacy"), None);
    assert_eq!(StopCause::from_reason("[stop:effort"), None, "an unterminated token");
    assert_eq!(
        StopCause::from_reason("[stop:steps] budget then [stop:bogus]"),
        Some(StopCause::Steps),
        "an unknown token is skipped, an earlier valid one is still read"
    );
    assert_eq!(
        StopCause::from_reason("[stop:effort] then [stop:steps] then [stop:effort"),
        Some(StopCause::Steps),
        "between deterministic causes the last complete valid token wins"
    );
    assert_eq!(
        StopCause::from_reason("[stop:wall-backstop] then [stop:solved]"),
        Some(StopCause::WallBackstop),
        "a clock anywhere in the reason outranks a later deterministic token"
    );
}

#[test]
fn a_backend_result_names_its_stop() {
    let proved = VerificationResult::Proved {
        solver: "ay".into(),
        time_ms: 1,
        strength: crate::ProofStrength::smt_unsat(),
        proof_certificate: None,
        solver_warnings: None,
        native_proof_envelope: None,
    };
    assert_eq!(StopCause::of_result(&proved), StopCause::Solved);
    let failed =
        VerificationResult::Failed { solver: "ay".into(), time_ms: 1, counterexample: None };
    assert_eq!(StopCause::of_result(&failed), StopCause::Solved);
    let timeout = VerificationResult::Timeout { solver: "ay".into(), timeout_ms: 5000 };
    assert_eq!(StopCause::of_result(&timeout), StopCause::WallBackstop);
    let silent = VerificationResult::Unknown {
        solver: "ay".into(),
        time_ms: 1,
        reason: "solver returned unknown".to_string(),
    };
    assert_eq!(StopCause::of_result(&silent), StopCause::Unclassified);
    let stated = StopCause::TermMemory.unknown_result("ay", 3, "term store ceiling");
    assert_eq!(StopCause::of_result(&stated), StopCause::TermMemory);
    assert_eq!(stated.solver_name(), "ay");
    assert_eq!(stated.time_ms(), 3);
}

#[test]
fn a_row_without_a_stated_cause_falls_back_to_what_its_outcome_says() {
    assert_eq!(StopCause::of_outcome(Outcome::Proved, None), StopCause::Solved);
    assert_eq!(StopCause::of_outcome(Outcome::Failed, None), StopCause::Solved);
    assert_eq!(StopCause::of_outcome(Outcome::Rejected, None), StopCause::Solved);
    assert_eq!(
        StopCause::of_outcome(Outcome::Timeout, Some("solver timed out")),
        StopCause::WallBackstop
    );
    assert_eq!(StopCause::of_outcome(Outcome::Canceled, None), StopCause::WallBackstop);
    assert_eq!(StopCause::of_outcome(Outcome::Skipped, None), StopCause::NotDispatched);
    assert_eq!(StopCause::of_outcome(Outcome::Unsupported, None), StopCause::Unsupported);
    assert_eq!(StopCause::of_outcome(Outcome::Unknown, Some("no idea")), StopCause::Unclassified);
    assert_eq!(StopCause::of_outcome(Outcome::RuntimeChecked, None), StopCause::Unclassified);
    // A stated cause wins over the outcome, e.g. a runtime-checked row whose
    // static attempt ran out of effort.
    let stated = StopCause::Effort.stamp("resourceout");
    assert_eq!(StopCause::of_outcome(Outcome::RuntimeChecked, Some(&stated)), StopCause::Effort);
    // ... except over an outcome that is itself a clock.
    assert_eq!(StopCause::of_outcome(Outcome::Timeout, Some(&stated)), StopCause::WallBackstop);
    assert_eq!(StopCause::of_outcome(Outcome::Canceled, Some(&stated)), StopCause::WallBackstop);
    let refused = StopCause::AdmissionRefused.stamp("trustd unreachable");
    assert_eq!(
        StopCause::of_outcome(Outcome::Timeout, Some(&refused)),
        StopCause::AdmissionRefused
    );
}

#[test]
fn the_unit_outcome_is_the_worst_stop() {
    assert_eq!(UnitOutcome::from_causes([]), UnitOutcome::Measured);
    assert_eq!(
        UnitOutcome::from_causes([StopCause::Solved, StopCause::Effort, StopCause::Steps]),
        UnitOutcome::Measured
    );
    assert_eq!(
        UnitOutcome::from_causes([StopCause::Solved, StopCause::WallBackstop, StopCause::Effort]),
        UnitOutcome::NotReproducible
    );
    assert_eq!(
        UnitOutcome::from_causes([StopCause::Unclassified]),
        UnitOutcome::NotReproducible,
        "an unexplained stop is never counted as deterministic"
    );
    assert_eq!(
        UnitOutcome::from_causes([
            StopCause::WallBackstop,
            StopCause::AdmissionRefused,
            StopCause::Solved
        ]),
        UnitOutcome::CouldNotRun
    );
    assert_eq!(
        serde_json::to_string(&UnitOutcome::NotReproducible).unwrap(),
        "\"not-reproducible\""
    );
}

#[test]
fn the_tally_counts_and_renders_in_canonical_order() {
    let tally: StopCauseTally =
        [StopCause::Solved, StopCause::WallBackstop, StopCause::Solved, StopCause::Effort]
            .into_iter()
            .collect();
    assert_eq!(tally.count(StopCause::Solved), 2);
    assert_eq!(tally.count(StopCause::Steps), 0);
    assert_eq!(tally.render(), "effort=1 solved=2 wall-backstop=1");
    assert_eq!(tally.outcome(), UnitOutcome::NotReproducible);
    assert_eq!(
        serde_json::to_string(&tally).unwrap(),
        r#"{"effort":1,"solved":2,"wall-backstop":1}"#
    );
    assert_eq!(StopCauseTally::default().render(), "none");
}

fn entry(key: &str, status: Outcome, stop: StopCause) -> VerdictEntry {
    VerdictEntry::new(key, status, stop).unwrap()
}

#[test]
fn the_vector_digest_is_independent_of_production_order() {
    let a = entry("obligation:m::f:overflow:0", Outcome::Proved, StopCause::Solved);
    let b = entry("obligation:m::f:overflow:1", Outcome::Unknown, StopCause::Effort);
    let c = entry("obligation:m::g:bounds:0", Outcome::Failed, StopCause::Solved);
    let forward = VerdictVector::new(vec![a.clone(), b.clone(), c.clone()]);
    let backward = VerdictVector::new(vec![c, b, a]);
    assert_eq!(forward, backward);
    assert_eq!(forward.digest(), backward.digest());
    assert_eq!(forward.first_difference(&backward), None);
    assert_eq!(forward.digest().len(), 64);
}

#[test]
fn any_change_of_status_or_stop_changes_the_digest_and_is_located() {
    let base = VerdictVector::new(vec![
        entry("obligation:m::f:overflow:0", Outcome::Proved, StopCause::Solved),
        entry("obligation:m::f:overflow:1", Outcome::Unknown, StopCause::Effort),
    ]);
    let status_moved = VerdictVector::new(vec![
        entry("obligation:m::f:overflow:0", Outcome::Proved, StopCause::Solved),
        entry("obligation:m::f:overflow:1", Outcome::Proved, StopCause::Solved),
    ]);
    let stop_moved = VerdictVector::new(vec![
        entry("obligation:m::f:overflow:0", Outcome::Proved, StopCause::Solved),
        entry("obligation:m::f:overflow:1", Outcome::Unknown, StopCause::WallBackstop),
    ]);
    assert_ne!(base.digest(), status_moved.digest());
    assert_ne!(base.digest(), stop_moved.digest());
    assert_ne!(status_moved.digest(), stop_moved.digest());
    let (left, right) = base.first_difference(&stop_moved).unwrap();
    assert_eq!(left.unwrap().stop, StopCause::Effort);
    assert_eq!(right.unwrap().stop, StopCause::WallBackstop);
    assert_eq!(base.tally().render(), "effort=1 solved=1");
}

#[test]
fn duplicate_keys_and_field_boundaries_are_part_of_the_identity() {
    let once =
        VerdictVector::new(vec![entry("obligation:m::f:x:0", Outcome::Proved, StopCause::Solved)]);
    let twice = VerdictVector::new(vec![
        entry("obligation:m::f:x:0", Outcome::Proved, StopCause::Solved),
        entry("obligation:m::f:x:0", Outcome::Proved, StopCause::Solved),
    ]);
    assert_ne!(once.digest(), twice.digest(), "a duplicated row is not the same production");
    // Length prefixes keep ("ab", "c") and ("a", "bc")-style splits apart.
    let split_one = VerdictVector::new(vec![VerdictEntry {
        obligation: "obligation:ab".into(),
        status: "c".into(),
        stop: StopCause::Solved,
    }]);
    let split_two = VerdictVector::new(vec![VerdictEntry {
        obligation: "obligation:a".into(),
        status: "bc".into(),
        stop: StopCause::Solved,
    }]);
    assert_ne!(split_one.digest(), split_two.digest());
    assert_ne!(VerdictVector::default().digest(), once.digest());
}

#[test]
fn a_key_carrying_volatile_identity_is_refused() {
    for volatile in [
        "",
        "   ",
        "rustc-crate:0123abcd:obligation:m::f:x:0",
        "path+file://<home>/checkout#crate@0.1.0",
        "registry+https://github.com/rust-lang/crates.io-index#serde@1.0.0",
        "<home>/checkout/src/lib.rs:12",
        "obligation:file:/tmp/x",
    ] {
        let error = VerdictEntry::new(volatile, Outcome::Proved, StopCause::Solved).unwrap_err();
        assert_eq!(error.key, volatile);
        assert!(!error.to_string().is_empty());
    }
    assert!(
        VerdictEntry::new("obligation:crate::m::f:overflow:3", Outcome::Proved, StopCause::Solved)
            .is_ok()
    );
}

/// T9: the vector keys on the stable `<def_path>#<local id>` key, and its
/// digest domain says so (v2), so a v1 digest — keyed on the ordinal
/// `obligation_id` — can never compare equal to a v2 one.
#[test]
fn the_vector_keys_on_the_stable_key_under_domain_v2() {
    assert_eq!(VERDICT_VECTOR_DOMAIN, b"trust-verdict-vector/v2\0");
    let id = crate::obligation_identity::local_id("divzero", "src:0123456789abcdef", 0);
    let key = crate::obligation_identity::obligation_key("c::m::{closure#0}", &id);
    let entry = VerdictEntry::new(key.clone(), Outcome::Proved, StopCause::Solved)
        .expect("a stable key carries no volatile identity");
    assert_eq!(entry.obligation, key);
}

fn int_var(name: &str) -> Formula {
    Formula::Var(name.to_string(), crate::Sort::Int)
}

/// Plan §3.2a: the size is the query's DAG — a repeated subterm counts once,
/// variables and constants count, a consistent renaming changes nothing, and
/// tree duplication is not counted.
#[test]
fn query_size_counts_each_distinct_term_once() {
    let x_plus_y = || Formula::Add(Box::new(int_var("x")), Box::new(int_var("y")));
    assert_eq!(query_size(&[&x_plus_y()]), 3, "x, y and x+y");
    let twice = Formula::And(vec![x_plus_y(), x_plus_y()]);
    assert_eq!(query_size(&[&twice]), query_size(&[&x_plus_y()]) + 1, "the And node only");
    // Across assertions: the same term in two assertions counts once.
    assert_eq!(query_size(&[&x_plus_y(), &x_plus_y()]), 3);
    assert_eq!(query_size(&[]), 0);

    let renamed = Formula::Add(Box::new(int_var("a")), Box::new(int_var("b")));
    assert_eq!(query_size(&[&renamed]), query_size(&[&x_plus_y()]), "renaming is free");
    // ... but merging two variables into one is not a renaming.
    let merged = Formula::Add(Box::new(int_var("a")), Box::new(int_var("a")));
    assert_eq!(query_size(&[&merged]), 2);
    // Constants count, and a distinct constant is a distinct term.
    let lt = |k: i128| Formula::Lt(Box::new(int_var("x")), Box::new(Formula::Int(k)));
    assert_eq!(query_size(&[&lt(0)]), 3);
    assert_eq!(query_size(&[&lt(0), &lt(1)]), 5);
}

/// A balanced tree of 2^20 leaves that are all the same subterm is a DAG of
/// 21 distinct terms: its size is the DAG's, never the tree's.
#[test]
fn query_size_is_the_dag_size_not_the_tree_size() {
    let mut tree = int_var("x");
    for _ in 0..20 {
        tree = Formula::And(vec![tree.clone(), tree]);
    }
    assert_eq!(query_size(&[&tree]), 21);
}

/// `effort(q) = min(C, max(1, k · size(q)))`, saturating, and `k` is a count
/// in `1..=C`.
#[test]
fn the_effort_count_scales_with_size_and_is_clamped() {
    let c = EffortScale::CEILING;
    assert_eq!(c, 100_000, "P2's flat per-query count, the calibration reference");
    let k = |conflicts_per_node| EffortScale { conflicts_per_node };
    assert_eq!(k(3).for_size(10), QueryEffort { size: 10, conflicts: 30 });
    assert_eq!(k(3).for_size(0).conflicts, 1, "never `:rlimit 0`, which ay reads as unbounded");
    assert_eq!(k(3).for_size(50_000).conflicts, c, "clamped at C");
    assert_eq!(k(c).for_size(u64::MAX).conflicts, c, "saturating, then clamped");
    let f = Formula::Add(Box::new(int_var("x")), Box::new(int_var("y")));
    assert_eq!(k(7).for_query(&[&f]), QueryEffort { size: 3, conflicts: 21 });
    assert_eq!(k(7).for_query(&[&f]).smt2_command(), "(set-option :rlimit 21)");
    assert_eq!(k(7).for_query(&[&f]).smt2_option(), (":rlimit", "21".to_string()));

    assert_eq!(EffortScale::parse(" 12 "), Ok(k(12)));
    assert_eq!(EffortScale::parse(&c.to_string()), Ok(k(c)));
    for refused in ["0", "100001", "18446744073709551615", "-1", "lots", "1,2"] {
        assert!(EffortScale::parse(refused).is_err(), "{refused}");
    }
    assert!(EffortScale::parse(&EffortScale::BUILTIN.conflicts_per_node.to_string()).is_ok());
    assert_eq!(EffortScale::default(), EffortScale::BUILTIN);
}

/// A component retry splits ONE query's effort by component size: every part
/// at least one conflict, the parts proportional, and their sum at most the
/// whole whenever the whole affords a conflict per part.
#[test]
fn the_component_split_is_proportional_to_size() {
    let whole = QueryEffort { size: 100, conflicts: 1_000 };
    let parts = whole.split_by_size(&[10, 30, 60]);
    assert_eq!(parts.iter().map(|p| p.conflicts).collect::<Vec<_>>(), [100, 300, 600]);
    assert_eq!(parts.iter().map(|p| p.size).collect::<Vec<_>>(), [10, 30, 60]);
    let uneven = whole.split_by_size(&[1, 1, 1]);
    assert_eq!(uneven.iter().map(|p| p.conflicts).collect::<Vec<_>>(), [333, 333, 333]);
    assert!(uneven.iter().map(|p| p.conflicts).sum::<u64>() <= whole.conflicts);
    let starved = QueryEffort { size: 5, conflicts: 2 }.split_by_size(&[1, 1, 1, 1]);
    assert!(starved.iter().all(|p| p.conflicts == 1), "{starved:?}");
    assert_eq!(QueryEffort { size: 0, conflicts: 9 }.split_by_size(&[0, 0])[0].conflicts, 1);
}

/// The built-in backstop reproduces exactly the clocks targo always passed
/// (no clock moves before T2), and per mille 1 is the 5 ms / 120 ms negative
/// control.
#[test]
fn the_backstop_reproduces_the_reference_clocks() {
    let builtin = Backstop::BUILTIN;
    assert_eq!((builtin.vc_clock_ms(), builtin.function_clock_ms()), (5_000, 120_000));
    let control = Backstop { per_mille: 1 };
    assert_eq!((control.vc_clock_ms(), control.function_clock_ms()), (5, 120));
    let doubled = Backstop { per_mille: 2000 };
    assert_eq!((doubled.vc_clock_ms(), doubled.function_clock_ms()), (10_000, 240_000));
    assert_eq!(Backstop::parse("1000"), Ok(builtin));
    assert!(Backstop::parse("0").unwrap_err().contains("at least 1"));
    assert!(Backstop::parse("-5").is_err());
    assert_eq!(Backstop::default(), builtin);
}

/// Schema 4: the id is `hash(schema, effort, backstop)` and nothing else — the
/// name, the worker-thread count and the derived clocks are recorded beside it.
#[test]
fn the_profile_id_is_the_effort_scale_and_the_backstop() {
    let base = BudgetProfile::builtin();
    let id = base.id();
    assert_eq!(id.len(), 64);
    assert_eq!(base.schema, BUDGET_PROFILE_SCHEMA);
    assert_eq!(BUDGET_PROFILE_SCHEMA, 4);
    assert_eq!(base.name, "builtin");
    assert_eq!(
        base.canonical_fields().into_iter().map(|(key, _)| key).collect::<Vec<_>>(),
        ["backstop", "effort", "schema"]
    );

    let mut renamed = base.clone();
    renamed.name = "renamed".into();
    assert_eq!(renamed.id(), id, "renaming a profile does not change what it bounds");
    let mut serial = base.clone();
    serial.worker_threads = 1;
    assert_eq!(serial.id(), id, "a worker-thread count is not a bound");

    let effort = BudgetProfile::new(EffortScale { conflicts_per_node: 1 }, Backstop::BUILTIN, 0);
    let backstop = BudgetProfile::new(EffortScale::BUILTIN, Backstop { per_mille: 1 }, 0);
    assert_eq!(effort.name, "configured");
    assert_ne!(effort.id(), id);
    assert_ne!(backstop.id(), id);
    assert_ne!(effort.id(), backstop.id());
    assert_eq!(
        BudgetProfile::new(EffortScale::BUILTIN, Backstop::BUILTIN, 7).id(),
        id,
        "restating the built-in bounds is the built-in profile"
    );
}

#[test]
fn the_header_names_the_id_the_bounds_and_the_recorded_values() {
    let mut profile = BudgetProfile::builtin();
    profile.worker_threads = 3;
    assert_eq!(
        profile.header_line(),
        format!(
            "Budget profile: {} (builtin) backstop=1000 effort={} schema=4; not in the id: \
             vc_clock_ms=5000 function_clock_ms=120000 worker_threads=3 frontend_threads=1 \
             (pinned)",
            short_id(&profile.id()),
            EffortScale::BUILTIN.conflicts_per_node,
        )
    );
    assert_eq!(short_id("abc"), "abc");
    assert_eq!(short_id("0123456789abcdef"), "0123456789ab");
}

/// A schema-4 record round-trips; a record of any other schema — an
/// intermediate one, never shipped — is refused by its schema, with no decode
/// path, whatever fields it carries.
#[test]
fn only_a_schema_4_profile_decodes() {
    let profile = BudgetProfile::new(EffortScale { conflicts_per_node: 9 }, Backstop::BUILTIN, 2);
    let json = serde_json::to_string(&profile).expect("serializes");
    assert_eq!(
        json,
        r#"{"schema":4,"name":"configured","effort":9,"backstop":1000,"worker_threads":2}"#
    );
    assert_eq!(serde_json::from_str::<BudgetProfile>(&json).expect("decodes"), profile);

    // The shape every earlier schema had: lane fields and the per-field
    // bounds beside them.
    let schema_3 = r#"{"schema":3,"name":"builtin","level":"2","policy":"strict",
        "function_budget_steps":64000000,"vc_timeout_ms":5000,"function_budget_ms":120000,
        "worker_threads":0}"#;
    let error = serde_json::from_str::<BudgetProfile>(schema_3).unwrap_err().to_string();
    assert!(error.contains("schema 3 is not readable"), "refused by its schema: {error}");
    let relabeled =
        r#"{"schema":3,"name":"builtin","effort":9,"backstop":1000,"worker_threads":0}"#;
    let error = serde_json::from_str::<BudgetProfile>(relabeled).unwrap_err().to_string();
    assert!(error.contains("schema 3 is not readable"), "{error}");
    let out_of_domain =
        r#"{"schema":4,"name":"builtin","effort":0,"backstop":1000,"worker_threads":0}"#;
    assert!(serde_json::from_str::<BudgetProfile>(out_of_domain).is_err());

    // A schema-4 record is held to exactly the schema-4 fields.
    let extra = r#"{"schema":4,"name":"builtin","effort":9,"backstop":1000,"worker_threads":0,
        "vc_timeout_ms":5000}"#;
    let error = serde_json::from_str::<BudgetProfile>(extra).unwrap_err().to_string();
    assert!(error.contains("unknown field `vc_timeout_ms`"), "{error}");
    let repeated =
        r#"{"schema":4,"name":"a","effort":9,"effort":10,"backstop":1000,"worker_threads":0}"#;
    let error = serde_json::from_str::<BudgetProfile>(repeated).unwrap_err().to_string();
    assert!(error.contains("duplicate field `effort`"), "{error}");
    let missing = r#"{"schema":4,"name":"a","effort":9,"worker_threads":0}"#;
    let error = serde_json::from_str::<BudgetProfile>(missing).unwrap_err().to_string();
    assert!(error.contains("missing field `backstop`"), "{error}");
}

/// The backstop ledger (plan §2: a unit is not reproducible when at least one
/// backstop fired, in a row or not). Lane names are unique to this test: the
/// ledger is process-wide and other tests run concurrently.
#[test]
fn the_backstop_ledger_records_non_reproducible_stops_and_the_solver_count() {
    let lane = "determinism_tests::ledger";
    for deterministic in every_cause().into_iter().filter(|cause| {
        cause.reproducibility() == Reproducibility::Deterministic && *cause != StopCause::Effort
    }) {
        note_stop(lane, deterministic);
    }
    assert!(
        noted_stops().iter().all(|stop| stop.lane != lane),
        "a deterministic stop other than the solver count is not recorded: {:?}",
        noted_stops()
    );
    note_stop(lane, StopCause::WallBackstop);
    note_stop(lane, StopCause::WallBackstop);
    note_stop(lane, StopCause::Unclassified);
    note_result(lane, &StopCause::SolverFault.unknown_result("ay", 0, "crashed"));
    note_result(
        lane,
        &VerificationResult::Failed { solver: "ay".into(), time_ms: 0, counterexample: None },
    );
    // The solver count is counted wherever the stopped work went.
    note_stop(lane, StopCause::Effort);
    note_result(lane, &StopCause::Effort.unknown_result("ay", 0, "ay unknown (resourceout)"));
    let mine: Vec<NotedStop> = noted_stops().into_iter().filter(|stop| stop.lane == lane).collect();
    assert_eq!(
        mine,
        vec![
            NotedStop { lane: lane.into(), cause: StopCause::Effort, item: None, count: 2 },
            NotedStop { lane: lane.into(), cause: StopCause::SolverFault, item: None, count: 1 },
            NotedStop { lane: lane.into(), cause: StopCause::Unclassified, item: None, count: 1 },
            NotedStop { lane: lane.into(), cause: StopCause::WallBackstop, item: None, count: 2 },
        ]
    );
    assert_eq!(mine[3].to_string(), format!("{lane} wall-backstop=2"));
    assert_eq!(
        UnitOutcome::from_causes(mine.iter().map(|stop| stop.cause)),
        UnitOutcome::NotReproducible
    );
    assert_eq!(
        UnitOutcome::from_causes(mine[..1].iter().map(|stop| stop.cause)),
        UnitOutcome::Measured,
        "a count stop never makes a unit not reproducible"
    );
    let json = serde_json::to_string(&mine[3]).unwrap();
    assert_eq!(json, format!(r#"{{"lane":"{lane}","cause":"wall-backstop","count":2}}"#));
}

/// Critique of the lane-efficiency plan (2026-09-30), P1 ledger items: every
/// named stop has one cause, round-trips its spelling, and rides in a reason
/// beside the stop token without changing how the cause is read.
#[test]
fn every_named_stop_has_one_cause_and_round_trips() {
    let expected = [
        (StopItem::CertificationEffort, StopCause::Effort),
        (StopItem::GenericTheoryLemma, StopCause::SolverIncomplete),
        (StopItem::InvalidSatModel, StopCause::SolverFault),
        (StopItem::ModelValidationViolated, StopCause::SolverIncomplete),
        (StopItem::ProofCheckEnvelope, StopCause::Effort),
        (StopItem::StrictCheckCancelled, StopCause::WallBackstop),
        (StopItem::UnverifiedTrustRule, StopCause::SolverIncomplete),
    ];
    assert_eq!(expected.len(), StopItem::ALL.len());
    let names: Vec<&str> = StopItem::ALL.iter().map(|item| item.as_str()).collect();
    let mut sorted = names.clone();
    sorted.sort_unstable();
    assert_eq!(names, sorted, "ALL is in canonical-name order");
    for (item, cause) in expected {
        assert_eq!(item.cause(), cause, "{item}");
        assert_eq!(StopItem::parse(item.as_str()), Some(item));
        let json = serde_json::to_string(&item).unwrap();
        assert_eq!(json, format!("\"{}\"", item.as_str()));
        let reason = cause.stamp_item(item, "computed UNSAT rejected");
        assert_eq!(
            reason,
            format!("computed UNSAT rejected [stop-item:{item}] [stop:{cause}]"),
            "the stop token stays last, where every consumer reads it"
        );
        assert_eq!(StopItem::from_reason(&reason), Some(item));
        assert_eq!(StopCause::from_reason(&reason), Some(cause));
    }
    assert_eq!(StopItem::from_reason("no item [stop:effort]"), None);
    assert_eq!(StopItem::from_reason("[stop-item:not-an-item]"), None);
}

#[test]
fn naming_a_stop_never_makes_a_row_more_reproducible() {
    // A clock inside the detail stays the row's cause whatever the item says.
    let clocked = StopCause::WallBackstop.stamp("strict check deadline");
    let named = StopCause::SolverIncomplete.stamp_item(StopItem::ModelValidationViolated, &clocked);
    assert_eq!(StopCause::from_reason(&named), Some(StopCause::WallBackstop), "{named}");
    assert_eq!(StopItem::from_reason(&named), Some(StopItem::ModelValidationViolated));
    // A wrapper that restamps keeps the item and the less reproducible cause.
    let rewrapped = StopCause::Unsupported.stamp(&named);
    assert_eq!(StopCause::from_reason(&rewrapped), Some(StopCause::WallBackstop));
    assert_eq!(StopItem::from_reason(&rewrapped), Some(StopItem::ModelValidationViolated));
}

/// Named stops are counted in the ledger whatever their class; the unit outcome
/// still takes only each entry's cause.
#[test]
fn the_ledger_counts_named_stops_by_name() {
    let lane = "determinism_tests::named";
    note_result(
        lane,
        &StopCause::SolverIncomplete.unknown_result_item(
            StopItem::ModelValidationViolated,
            "ay",
            0,
            "model validation violated: Assertion: x",
        ),
    );
    note_result(
        lane,
        &StopCause::WallBackstop.unknown_result_item(
            StopItem::StrictCheckCancelled,
            "ay",
            0,
            "proof validation cancelled by the caller",
        ),
    );
    note_result(
        lane,
        &StopCause::WallBackstop.unknown_result_item(
            StopItem::StrictCheckCancelled,
            "ay",
            0,
            "proof validation cancelled by the caller",
        ),
    );
    let mine: Vec<NotedStop> = noted_stops().into_iter().filter(|stop| stop.lane == lane).collect();
    assert_eq!(
        mine,
        vec![
            NotedStop {
                lane: lane.into(),
                cause: StopCause::SolverIncomplete,
                item: Some(StopItem::ModelValidationViolated),
                count: 1,
            },
            NotedStop {
                lane: lane.into(),
                cause: StopCause::WallBackstop,
                item: Some(StopItem::StrictCheckCancelled),
                count: 2,
            },
        ]
    );
    assert_eq!(mine[1].to_string(), format!("{lane} wall-backstop[strict-check-cancelled]=2"));
    assert_eq!(
        UnitOutcome::from_causes(mine.iter().take(1).map(|stop| stop.cause)),
        UnitOutcome::Measured,
        "a deterministic named stop is counted, never graded"
    );
    let json = serde_json::to_string(&mine[1]).unwrap();
    assert_eq!(
        json,
        format!(
            r#"{{"lane":"{lane}","cause":"wall-backstop","item":"strict-check-cancelled","count":2}}"#
        )
    );
    let tally: StopItemTally =
        [StopItem::UnverifiedTrustRule, StopItem::UnverifiedTrustRule, StopItem::InvalidSatModel]
            .into_iter()
            .collect();
    assert_eq!(tally.render(), "invalid-sat-model=1 unverified-trust-rule=2");
    assert_eq!(tally.count(StopItem::UnverifiedTrustRule), 2);
    assert_eq!(StopItemTally::default().render(), "none");
}

/// Review 2026-09-30: an ay solve the bridge drops because it stopped on a
/// COUNT leaves the native row; that row states the count too, by the
/// combination rule, so the less reproducible cause still wins.
#[test]
fn a_lane_count_stop_folds_into_the_surviving_row_by_the_combination_rule() {
    let lane = "the ay producer";
    let effort = StopCause::Effort.unknown_result("ay", 3, "ay unknown (resourceout)");
    let unsupported =
        StopCause::Unsupported.stamp("native full verifier evidence status: Unsupported");

    // A deterministic native stop: the row states the count that also ended it.
    let folded = fold_lane_count_stop(&unsupported, lane, &effort).expect("a count stop folds");
    assert_eq!(StopCause::from_reason(&folded), Some(StopCause::Effort), "{folded}");
    assert!(folded.starts_with("native full verifier evidence status: Unsupported; "), "{folded}");
    assert!(folded.contains("the ay producer stopped on its effort count"), "{folded}");
    assert_eq!(folded.matches("[stop:").count(), 1, "one trailing token: {folded}");

    // A native clock stop stays a clock stop.
    let clock = StopCause::WallBackstop.stamp("native full verifier evidence status: Canceled");
    let folded = fold_lane_count_stop(&clock, lane, &effort).expect("a count stop folds");
    assert_eq!(StopCause::from_reason(&folded), Some(StopCause::WallBackstop), "{folded}");

    // A native row that states nothing stays unexplained, and now names the count.
    let silent = "native full verifier evidence status: Unknown";
    let folded = fold_lane_count_stop(silent, lane, &effort).expect("a count stop folds");
    assert_eq!(StopCause::from_reason(&folded), Some(StopCause::Unclassified), "{folded}");
    assert!(folded.contains("effort count"), "{folded}");

    // Only a count stop folds: a verdict, a clock and an unexplained stop do not.
    let failed =
        VerificationResult::Failed { solver: "ay".into(), time_ms: 0, counterexample: None };
    let timed_out = StopCause::WallBackstop.unknown_result("ay", 5_000, "timeout");
    let unexplained =
        VerificationResult::Unknown { solver: "ay".into(), time_ms: 0, reason: "unknown".into() };
    for other in [failed, timed_out, unexplained] {
        assert_eq!(fold_lane_count_stop(&unsupported, lane, &other), None, "{other:?}");
    }
}

/// Proof-loss class 6 (2026-10-02): on trust main `d36c551fac` every in-process
/// ay solve past ~60% of aterm-grid ended on ay's process-memory ceiling, and
/// the bridge dropped that stop, so the surviving native row read the bundle's
/// typed-input refusal (`[stop:unclassified]`) as the reason 21 seal-proved rows
/// were unproved. A resource backstop now folds into the surviving row, and the
/// row states it.
#[test]
fn a_lane_resource_backstop_folds_into_the_surviving_row() {
    let lane = "the ay producer";
    let refusal = StopCause::Unclassified.stamp(
        "native full verifier evidence status: Unsupported; compiler full verification \
         requires typed TrustIr native evidence: constructor member has no complete exact \
         root invocation path",
    );
    let memout = StopCause::RssBackstop.unknown_result(
        "ay-in-process",
        0,
        "ay unknown (memory_limit): process footprint over the embedded ceiling",
    );
    let guard = StopCause::RssBackstop.unknown_result(
        "memory-guard",
        0,
        "memory limit exceeded: 5400MB used, 3072MB limit (peak: 5400MB) — skipping solver dispatch",
    );
    let fault = StopCause::SolverFault.unknown_result("ay-in-process", 0, "solver panicked");

    // The measured shape: the row now names the memory ceiling, once, last.
    let folded = fold_lane_stop(&refusal, lane, &memout).expect("an RSS backstop folds");
    assert_eq!(StopCause::from_reason(&folded), Some(StopCause::RssBackstop), "{folded}");
    assert!(folded.starts_with("native full verifier evidence status: Unsupported; "), "{folded}");
    assert!(folded.contains("constructor member has no complete exact root invocation path"));
    assert!(folded.contains("the ay producer stopped on rss-backstop before it decided"));
    assert!(folded.contains("memory_limit"), "{folded}");
    assert!(folded.ends_with("[stop:rss-backstop]"), "{folded}");
    assert_eq!(folded.matches("[stop:").count(), 1, "one trailing token: {folded}");
    let folded = fold_lane_stop(&refusal, lane, &guard).expect("the router guard folds");
    assert_eq!(StopCause::from_reason(&folded), Some(StopCause::RssBackstop), "{folded}");
    let folded = fold_lane_stop(&refusal, lane, &fault).expect("a solver fault folds");
    assert_eq!(StopCause::from_reason(&folded), Some(StopCause::SolverFault), "{folded}");

    // A deterministic native stop becomes the backstop: it is less reproducible.
    let unsupported =
        StopCause::Unsupported.stamp("native full verifier evidence status: Unsupported");
    let folded = fold_lane_stop(&unsupported, lane, &memout).expect("an RSS backstop folds");
    assert_eq!(StopCause::from_reason(&folded), Some(StopCause::RssBackstop), "{folded}");
    // A row that states nothing at all names the backstop too.
    let folded = fold_lane_stop("native full verifier evidence status: Unknown", lane, &memout)
        .expect("an RSS backstop folds");
    assert_eq!(StopCause::from_reason(&folded), Some(StopCause::RssBackstop), "{folded}");
    // A unit that could not run stays could-not-run: never made MORE reproducible.
    let refused = StopCause::AdmissionRefused.stamp("trustd refused admission");
    let folded = fold_lane_stop(&refused, lane, &memout).expect("an RSS backstop folds");
    assert_eq!(StopCause::from_reason(&folded), Some(StopCause::AdmissionRefused), "{folded}");

    // `fold_lane_stop` still folds the count exactly as `fold_lane_count_stop`.
    let effort = StopCause::Effort.unknown_result("ay", 3, "ay unknown (resourceout)");
    assert_eq!(
        fold_lane_stop(&unsupported, lane, &effort),
        fold_lane_count_stop(&unsupported, lane, &effort)
    );
    // ... and `fold_lane_count_stop` itself still folds no backstop.
    assert_eq!(fold_lane_count_stop(&unsupported, lane, &memout), None);

    // Negative controls: a verdict, a clock (published as a clock stop by its
    // own lane), an unexplained stop and a deterministic lane stop never fold.
    let proved = VerificationResult::Proved {
        solver: "ay".into(),
        time_ms: 0,
        strength: crate::ProofStrength::smt_unsat(),
        proof_certificate: None,
        solver_warnings: None,
        native_proof_envelope: None,
    };
    let failed =
        VerificationResult::Failed { solver: "ay".into(), time_ms: 0, counterexample: None };
    let timed_out = StopCause::WallBackstop.unknown_result("ay", 5_000, "timeout");
    let unexplained =
        VerificationResult::Unknown { solver: "ay".into(), time_ms: 0, reason: "unknown".into() };
    let incomplete = StopCause::SolverIncomplete.unknown_result("ay", 0, "incomplete theory");
    let term_memory = StopCause::TermMemory.unknown_result("ay", 0, "term-store memory ceiling");
    for other in [proved, failed, timed_out, unexplained, incomplete, term_memory] {
        assert_eq!(fold_lane_stop(&refusal, lane, &other), None, "{other:?}");
    }
}

#[test]
fn only_rss_and_solver_fault_are_resource_backstops() {
    for cause in StopCause::ALL {
        assert_eq!(
            cause.is_resource_backstop(),
            matches!(cause, StopCause::RssBackstop | StopCause::SolverFault),
            "{cause}"
        );
        if cause.is_resource_backstop() {
            assert_eq!(cause.reproducibility(), Reproducibility::NotReproducible, "{cause}");
            assert!(!cause.is_solver_count(), "{cause}");
        }
    }
}
