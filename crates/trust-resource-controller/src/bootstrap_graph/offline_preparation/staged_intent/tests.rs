// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! DATA-only controls; no native reservation, program, source or owner exists.
use super::*;

fn selected() -> (StagedIntent, ProgramSelection) {
    let request = super::super::tests::request();
    (
        StagedIntent {
            key: request.key.clone(),
            selection: StagedSelection {
                source_root: request.source_root,
                output_root: request.output_root,
                environment: request.environment,
                budget_ns: request.budget_ns,
            },
        },
        ProgramSelection {
            key: request.key,
            configured_targo: request.configured_targo,
            configured_compiler: request.configured_compiler,
        },
    )
}

#[test]
fn staged_frames_are_distinct_bounded_and_reject_truncation_or_trailing_bytes() {
    let (intent, selection) = selected();
    let query = StagedIntentQuery { key: intent.key.graph.clone() };
    let reply = StagedIntentReply {
        query: query.clone(),
        intent,
        remaining_root_ns: MAX_BUDGET_NS,
    };
    let programs = ProgramSelectionReply {
        selection: selection.clone(),
        namespace: b"/private-seed".to_vec(),
        remaining_root_ns: MAX_BUDGET_NS,
    };
    let reservation = ProgramSelectionQuery { key: selection.key.clone() };
    let reserved = ReservedPrograms {
        query: reservation.clone(),
        namespace: programs.namespace.clone(),
        remaining_root_ns: MAX_BUDGET_NS,
    };
    let frames = [
        (128, reply.intent.selection.encode().unwrap()),
        (129, query.encode().unwrap()),
        (130, reply.encode().unwrap()),
        (131, selection.encode().unwrap()),
        (132, programs.encode().unwrap()),
        (133, reservation.encode().unwrap()),
        (134, reserved.encode().unwrap()),
    ];
    let decodes = |kind, bytes: &[u8]| match kind {
        0 => StagedSelection::decode(bytes).is_ok(),
        1 => StagedIntentQuery::decode(bytes).is_ok(),
        2 => StagedIntentReply::decode(bytes, &query).is_ok(),
        3 => ProgramSelection::decode(bytes).is_ok(),
        4 => ProgramSelectionReply::decode(bytes, &selection).is_ok(),
        5 => ProgramSelectionQuery::decode(bytes).is_ok(),
        6 => ReservedPrograms::decode(bytes, &reservation).is_ok(),
        _ => unreachable!(),
    };
    let old_query = IntentQuery { key: query.key.clone() };
    for (index, (tag, frame)) in frames.iter().enumerate() {
        assert_eq!(u64::from_be_bytes(frame[8..16].try_into().unwrap()), *tag);
        for other in 0..frames.len() {
            assert_eq!(decodes(other, frame), index == other);
        }
        for end in 0..frame.len() {
            assert!(!decodes(index, &frame[..end]));
        }
        let mut trailing = frame.clone();
        trailing.push(0);
        assert!(!decodes(index, &trailing));
        assert!(IntentSelection::decode(frame).is_err());
        assert!(IntentQuery::decode(frame).is_err());
        assert!(IntentReply::decode(frame, &old_query).is_err());
        assert!(Request::decode(frame).is_err());
        assert!(crate::bootstrap_graph::query::Request::decode(frame).is_err());
        assert!(crate::bootstrap_graph::object::Request::decode(frame).is_err());
    }
    assert!(StagedIntentReply::decode(&reply.encode().unwrap(), &query).unwrap() == reply);
    assert!(ProgramSelectionReply::decode(&programs.encode().unwrap(), &selection).unwrap() == programs);
    assert!(ReservedPrograms::decode(&reserved.encode().unwrap(), &reservation).unwrap() == reserved);
}

#[test]
fn staged_selectors_preserve_raw_policy_and_reject_ambiguous_or_unbounded_data() {
    let (intent, _) = selected();
    let encoded = intent.selection.encode().unwrap();
    let decoded = StagedSelection::decode(&encoded).unwrap();
    assert!(decoded == intent.selection);
    assert!(decoded.environment.contains(&(b"TARGO_BUILD_WARNINGS".to_vec(), vec![])));
    assert!(decoded.environment.contains(&(b"CALLER_OS_BYTES".to_vec(), vec![255, 254])));
    for budget in [0, MAX_BUDGET_NS + 1, u64::MAX] {
        let mut bad = intent.clone();
        bad.selection.budget_ns = budget;
        assert!(bad.validate().is_err());
    }
    for path in [b"".as_slice(), b"relative", b"/source/../other", b"/source//other", b"/source\0"] {
        for source in [false, true] {
            let mut bad = intent.clone();
            if source {
                bad.selection.source_root = path.to_vec();
            } else {
                bad.selection.output_root = path.to_vec();
            }
            assert!(bad.validate().is_err());
        }
    }
    let mut bad = intent.clone();
    bad.selection.output_root = bad.selection.source_root.clone();
    assert!(bad.validate().is_err());
    let mut bad = intent.clone();
    bad.selection.environment.push(bad.selection.environment[0].clone());
    assert!(bad.validate().is_err());
    let mut bad = intent.clone();
    bad.selection.environment.retain(|(name, _)| name != b"CARGO_NET_OFFLINE");
    assert!(bad.validate().is_err());
    let mut bad = intent.clone();
    bad.selection.environment[0].1 = vec![b'x'; MAX_FIELD + 1];
    assert!(bad.validate().is_err());
    for sequence in [0, 2, u64::MAX] {
        let mut bad = intent.clone();
        bad.key.sequence = sequence;
        assert!(bad.validate().is_err());
        assert!(ProgramSelectionQuery { key: bad.key }.encode().is_err());
    }
}

#[test]
fn staged_policy_and_final_programs_restrict_the_same_original_request_separately() {
    let (intent, selected) = selected();
    let original = super::super::tests::request();
    intent.matches_request(&original).unwrap();
    selected.matches_request(&original).unwrap();
    let mut reduced = original.clone();
    reduced.budget_ns -= 1;
    intent.matches_request(&reduced).unwrap();
    let mut changed = original.clone();
    changed.configured_targo = b"/private-seed/bin/targo".to_vec();
    // Partial intent cannot stand in for the required final selector check.
    intent.matches_request(&changed).unwrap();
    assert!(selected.matches_request(&changed).is_err());
    let mut changed = original.clone();
    changed.configured_compiler.push(b'x');
    assert!(selected.matches_request(&changed).is_err());
    let mut changed = original.clone();
    changed.environment.retain(|(name, _)| name != b"TARGO_BUILD_WARNINGS");
    assert!(intent.matches_request(&changed).is_err());
    let mut changed = original.clone();
    changed.source_root.push(b'x');
    assert!(intent.matches_request(&changed).is_err());
    let mut changed = original;
    changed.key.operation[0] ^= 1;
    assert!(intent.matches_request(&changed).is_err());
    assert!(selected.matches_request(&changed).is_err());
}

#[test]
fn staged_reply_refuses_foreign_graph_and_remaining_time_beyond_original_budget() {
    let (intent, _) = selected();
    let query = StagedIntentQuery { key: intent.key.graph.clone() };
    let reply = StagedIntentReply {
        query: query.clone(),
        intent,
        remaining_root_ns: MAX_BUDGET_NS,
    };
    let bytes = reply.encode().unwrap();
    let mut foreign = query;
    foreign.key.graph[0] ^= 1;
    assert!(StagedIntentReply::decode(&bytes, &foreign).is_err());
    for remaining in [0, MAX_BUDGET_NS + 1, u64::MAX] {
        let mut bad = reply.clone();
        bad.remaining_root_ns = remaining;
        assert!(bad.encode().is_err());
    }
    let mut bad = reply;
    bad.intent.selection.budget_ns = 1;
    bad.remaining_root_ns = 2;
    assert!(bad.encode().is_err());
}

#[test]
fn program_replies_preserve_exact_request_namespace_and_same_attempt() {
    let (intent, selection) = selected();
    let query = ProgramSelectionQuery { key: intent.key };
    let reserved = ReservedPrograms {
        query: query.clone(),
        namespace: b"/private-seed".to_vec(),
        remaining_root_ns: MAX_BUDGET_NS,
    };
    let reply = ProgramSelectionReply {
        selection: selection.clone(),
        namespace: reserved.namespace.clone(),
        remaining_root_ns: MAX_BUDGET_NS,
    };
    let bytes = reply.encode().unwrap();
    let mut foreign = selection.clone();
    foreign.key.operation[0] ^= 1;
    assert!(ProgramSelectionReply::decode(&bytes, &foreign).is_err());
    let mut changed = selection.clone();
    changed.configured_targo = b"/private-seed/bin/targo".to_vec();
    assert!(ProgramSelectionReply::decode(&bytes, &changed).is_err());
    let bytes = reserved.encode().unwrap();
    let mut foreign = query;
    foreign.key.graph.graph[0] ^= 1;
    assert!(ReservedPrograms::decode(&bytes, &foreign).is_err());
    for namespace in [b"relative".as_slice(), b"/private-seed/..", b"/private-seed//nested", b"/different"] {
        let mut bad = reply.clone();
        bad.namespace = namespace.to_vec();
        assert!(bad.encode().is_err());
    }
    for program in [b"/private-seed/bin".as_slice(), b"/private-seed/bin/nested/targo", b"/private-seed/bin/../targo", b"/private-seed/binx/targo"] {
        let mut bad = reply.clone();
        bad.selection.configured_targo = program.to_vec();
        assert!(bad.encode().is_err());
    }
    for remaining in [0, MAX_BUDGET_NS + 1, u64::MAX] {
        let mut bad = reply.clone();
        bad.remaining_root_ns = remaining;
        assert!(bad.encode().is_err());
        let mut bad = reserved.clone();
        bad.remaining_root_ns = remaining;
        assert!(bad.encode().is_err());
    }
    let mut bad = reserved;
    bad.namespace = b"/seed\0".to_vec();
    assert!(bad.encode().is_err());
}

#[test]
fn staged_intent_and_program_channels_keep_distinct_purposes() {
    let (intent, selection) = selected();
    let query = StagedIntentQuery { key: intent.key.graph.clone() };
    let reservation = ProgramSelectionQuery { key: intent.key };
    let staged = query.hello().unwrap();
    let programs = reservation.hello().unwrap();
    assert!(staged.windows(STAGED_INTENT_PURPOSE.len()).any(|part| part == STAGED_INTENT_PURPOSE.as_bytes()));
    assert!(programs.windows(PROGRAM_PURPOSE.len()).any(|part| part == PROGRAM_PURPOSE.as_bytes()));
    assert!(selection.hello().unwrap() == programs);
    assert!(staged != programs);
    assert!(!staged.windows(INTENT_PURPOSE.len()).any(|part| part == INTENT_PURPOSE.as_bytes()));
}
