use super::*;

fn tally() -> PublishedRowTally {
    PublishedRowTally {
        cause: None,
        proved: 1,
        failed: 1,
        unknown: 3,
        timed_out: 1,
        runtime_checked: 1,
        assumed_requires: 1,
        assumed_discharge: 1,
        skipped: 2,
        clock_stopped: 1,
    }
}

fn facts() -> HumanFacts {
    HumanFacts {
        rows: vec![
            HumanRow::Proved,
            HumanRow::Assumed("[a] original requires assumption".into()),
            HumanRow::Unknown { reason: "[b] UNKNOWN (ay): original open row".into(), proposable: true },
            HumanRow::Unknown { reason: "[b] UNKNOWN (ay): original open row".into(), proposable: true },
            HumanRow::Failed { reason: "[c] FAILED (ay): original fail-closed reason".into(), unproved: true },
            HumanRow::Timeout("[d] TIMEOUT (ay)".into()),
            HumanRow::RuntimeChecked { reason: "[e] original runtime monitor".into(), proposable: true },
            HumanRow::Other("[f] unsupported verification result variant".into()),
        ],
        conditional_on_coroutine_premise: false,
        // Arbitrary already-captured text verifies copy/order behavior;
        // this does not construct the authority that could substantiate it.
        disclosures: vec![
            "of which 1 kernel-certified by the clean CIC kernel (zero-trust re-check; runtime-check elision requires exact MIR Assert identity)".into(),
            "original named premise; not a new candidate certificate".into(),
        ],
    }
}

#[test]
fn original_render_keeps_published_denominator_disclosures_and_batched_reasons() {
    let report = facts().render(tally(), &[]).unwrap();
    assert_eq!(report.summary,
        "Trust verification: 1 proved, 1 failed, 3 unknown, 1 timed out, 1 runtime-checked, 1 assumed (requires), 1 assumed (instance discharge), 2 skipped out of 11 obligation(s)");
    assert_eq!(report.notes, vec![
        "counted over the rows this function publishes (its JSON transport rows): the policy layer added rows after the per-obligation results below, or reclassified some of them (a memory-safe assumption, a runtime-checked std member, a contract-panic or termination row), so their categories can differ from this line's",
        "of the per-obligation results below, 1 FAILED row(s) are unproved with NO counterexample: nothing refuted them; they fail closed because the unsafe operation could not be proved and may not pass unproved (an unmodelled call, a body that did not lower to native trust-ir, or a solver that returned unknown)",
        "of which 1 kernel-certified by the clean CIC kernel (zero-trust re-check; runtime-check elision requires exact MIR Assert identity)",
        "original named premise; not a new candidate certificate",
        "[a] original requires assumption",
        "2× [b] UNKNOWN (ay): original open row",
        "[c] FAILED (ay): original fail-closed reason",
        "[d] TIMEOUT (ay)",
        "[e] original runtime monitor",
        "… and 1 more distinct reason(s) suppressed (log batching)",
    ]);
}

#[test]
fn proposal_changes_only_exact_row_reason_and_never_certified_or_unrelated_debt() {
    let facts = facts();
    let original = facts.render(tally(), &[]).unwrap();
    let mut alternative = tally();
    alternative.proved = 2;
    alternative.unknown = 2;
    assert_eq!(alternative.total(), tally().total());
    let candidate = facts.render(alternative, &[2]).unwrap();
    assert_eq!(candidate.summary,
        "Trust verification: 2 proved, 1 failed, 2 unknown, 1 timed out, 1 runtime-checked, 1 assumed (requires), 1 assumed (instance discharge), 2 skipped out of 11 obligation(s)");
    assert_eq!(candidate.notes.len(), 10);
    assert_eq!(candidate.notes[5], "[b] UNKNOWN (ay): original open row");
    for index in [0, 1, 2, 3, 4, 6, 7, 8, 9] {
        assert_eq!(candidate.notes[index], original.notes[index], "unrelated disclosure/reason {index}");
    }
    let again = facts.render(tally(), &[]).unwrap();
    assert_eq!(again.summary, original.summary);
    assert_eq!(again.notes, original.notes, "rendering never mutates original facts");

    // An original Unknown rendered as runtime-checked can be proposed;
    // its Timeout-derived counterpart below is deliberately ineligible.
    let mut runtime_alternative = tally();
    runtime_alternative.proved = 2;
    runtime_alternative.runtime_checked = 0;
    assert_eq!(runtime_alternative.total(), tally().total());
    let candidate = facts.render(runtime_alternative, &[6]).unwrap();
    assert!(!candidate.notes.iter().any(|s| s.contains("[e] original runtime monitor")));
    assert!(candidate.notes.iter().any(|s| s.contains("of which 1 kernel-certified")));
    assert!(!candidate.notes.iter().any(|s| s.contains("of which 2 kernel-certified")));
}

#[test]
fn invalid_or_protected_proposals_refuse_instead_of_skipping_rows() {
    let mut facts = facts();
    facts.rows.push(HumanRow::Unknown {
        reason: "held refutation or original assumption/premise".into(), proposable: false,
    });
    facts.rows.push(HumanRow::RuntimeChecked {
        reason: "original timeout fallback".into(), proposable: false,
    });
    let mut rows = tally();
    rows.unknown += 1;
    rows.runtime_checked += 1;
    for valid in [vec![], vec![2], vec![3], vec![6], vec![6, 2]] {
        assert!(facts.render(rows, &valid).is_some(), "nonvacuous permitted DATA baseline");
    }
    for invalid in [
        vec![2, 2], vec![usize::MAX], vec![2, usize::MAX],
        vec![0], vec![1], vec![4], vec![5], vec![7], vec![8], vec![9],
    ] {
        assert!(facts.render(rows, &invalid).is_none(), "invalid proposal {invalid:?}");
    }
}

#[test]
fn frozen_human_data_roundtrip_does_not_synthesize_a_favorable_label() {
    let original = facts();
    let bytes = serde_json::to_vec(&original).unwrap();
    let owned: HumanFacts = serde_json::from_slice(&bytes).unwrap();
    let original_report = original.render(tally(), &[]).unwrap();
    let decoded_report = owned.render(tally(), &[]).unwrap();
    assert_eq!(decoded_report.summary, original_report.summary);
    assert_eq!(decoded_report.notes, original_report.notes);
    assert!(owned.render(tally(), &[1]).is_none(), "an assumption stays ineligible after decode");
    let mut unknown_variant = serde_json::to_value(&original).unwrap();
    unknown_variant["rows"][0] = serde_json::json!({"Certified": "not a DATA row constructor"});
    assert!(serde_json::from_value::<HumanFacts>(unknown_variant).is_err());
    let mut extra = serde_json::to_value(&original).unwrap();
    extra["selected_success"] = serde_json::json!(true);
    assert!(serde_json::from_value::<HumanFacts>(extra).is_err());
}

#[test]
fn conditional_and_collapse_disclosures_keep_the_original_scope_and_full_count() {
    let mut facts = facts();
    facts.conditional_on_coroutine_premise = true;
    facts.disclosures = vec![
        "1 obligation(s) were discharged CONDITIONALLY, under the coroutine resume-state entry assumption injected at function entry — not as unconditional proof; see the accompanying coroutine executor-protocol row".into(),
        "original named invariant premise".into(),
    ];
    let mut rows = tally();
    rows.cause = Some(PublishedRowsCause::NativeLoweringCollapse);
    let original = facts.render(rows, &[]).unwrap();
    assert_eq!(original.summary,
        "Trust verification: 1 conditionally discharged (NOT proved), 1 failed, 3 unknown, 1 timed out, 1 runtime-checked, 1 assumed (requires), 1 assumed (instance discharge), 2 skipped out of 11 obligation(s)");
    assert_eq!(original.notes[0],
        "counted over the rows this function publishes: native typed-TrustIr lowering did not complete, and its unproved rows were collapsed into one `assumption:native-lowering` row (skipped, NOT proved); the notes below are the per-obligation results from before that collapse");
    assert!(original.notes[2].contains("discharged CONDITIONALLY"));
    assert_eq!(original.notes[3], "original named invariant premise");
    rows.proved += 1;
    rows.unknown -= 1;
    let candidate = facts.render(rows, &[2]).unwrap();
    assert!(candidate.summary.contains("2 conditionally discharged (NOT proved)"));
    assert!(candidate.summary.ends_with("out of 11 obligation(s)"));
    assert_eq!(&candidate.notes[..4], &original.notes[..4]);
    assert!(!candidate.notes.iter().any(|s| s.contains("kernel-certified")));
    let empty = HumanFacts { rows: Vec::new(), conditional_on_coroutine_premise: false, disclosures: Vec::new() };
    assert!(empty.render(rows, &[]).is_none(), "original empty-results behavior");
}
