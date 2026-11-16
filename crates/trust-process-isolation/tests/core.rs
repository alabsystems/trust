use std::time::{Duration, Instant};

use trust_process_isolation::*;

fn limits() -> Limits {
    Limits {
        frame_bytes: 65536,
        wire_bytes: 1_000_000,
        allocation_bytes: 2_000_000,
        values: 10000,
        work: 100000,
        calls: 100,
        live_handles: 64,
        depth: 16,
    }
}
fn budget() -> Budget {
    Budget::new(limits(), Instant::now() + Duration::from_secs(30)).unwrap()
}
fn binding() -> Binding {
    Binding {
        version: PROTOCOL_VERSION,
        invocation: 17,
        compiler: [1; 32],
        worker: [2; 32],
        artifact: [3; 32],
        metadata: [4; 32],
        unit: [5; 32],
        input_closure: [6; 32],
        host_abi: [7; 32],
    }
}
fn h(kind: HandleKind) -> Handle {
    Handle { invocation: 17, kind, slot: 0, generation: 1 }
}
fn envelope(message: Message) -> Envelope {
    Envelope { binding: binding(), message }
}
fn sample(ty: Type) -> Value {
    match ty {
        Type::Unit => Value::Unit,
        Type::Bool => Value::Bool(true),
        Type::U64 => Value::U64(19),
        Type::Text => Value::Text("λ_x".into()),
        Type::OptionalText => Value::OptionalText(Some("x".into())),
        Type::Stream => Value::Stream(h(HandleKind::Stream)),
        Type::Span => Value::Span(h(HandleKind::Span)),
        Type::OptionalStream => Value::OptionalStream(Some(h(HandleKind::Stream))),
        Type::OptionalSpan => Value::OptionalSpan(Some(h(HandleKind::Span))),
        Type::Tree => Value::Tree(Box::new(Tree::Group {
            delimiter: 0,
            stream: Some(h(HandleKind::Stream)),
            spans: [h(HandleKind::Span); 3],
        })),
        Type::Trees => Value::Trees(vec![
            Tree::Ident { symbol: "x".into(), is_raw: false, span: h(HandleKind::Span) },
            Tree::Punct { ch: b'=', joint: true, span: h(HandleKind::Span) },
        ]),
        Type::Streams => Value::Streams(vec![h(HandleKind::Stream)]),
        Type::Bound => Value::Bound(Bound::Excluded(5)),
        Type::Range => Value::Range { start: 2, end: 9 },
        Type::Literal => Value::Literal(Box::new(Literal {
            kind: 2,
            raw_hashes: 0,
            symbol: "42".into(),
            suffix: Some("u8".into()),
            span: h(HandleKind::Span),
        })),
        Type::Diagnostic => Value::Diagnostic(Box::new(Diagnostic {
            level: 0,
            message: "error".into(),
            spans: vec![h(HandleKind::Span)],
            children: vec![Diagnostic {
                level: 2,
                message: "note".into(),
                spans: vec![],
                children: vec![],
            }],
        })),
        Type::LiteralOrText => Value::Result { ok: true, value: Box::new(sample(Type::Literal)) },
        Type::StreamOrUnit | Type::StreamOrText => {
            Value::Result { ok: true, value: Box::new(sample(Type::Stream)) }
        }
        Type::TextOrUnit => Value::Result { ok: true, value: Box::new(sample(Type::Text)) },
    }
}

#[test]
fn every_method_roundtrips_and_has_matching_response() {
    assert_eq!(Method::ALL.len(), 32);
    for method in Method::ALL {
        let call = Call {
            id: 1,
            method: *method,
            arguments: method.arguments().iter().map(|t| sample(*t)).collect(),
        };
        let message = envelope(Message::Call(call));
        let bytes = encode(&message, &budget()).unwrap();
        assert_eq!(decode(&bytes, &budget()).unwrap(), message);
        let reply = envelope(Message::Reply { id: 1, value: sample(method.response()) });
        assert_eq!(decode(&encode(&reply, &budget()).unwrap(), &budget()).unwrap(), reply);
        assert_eq!(Method::from_tag(method.tag()).unwrap(), *method);
    }
}

#[test]
fn only_the_pending_admitted_call_can_reach_an_adapter() {
    let call = Call {
        id: 1,
        method: Method::SpanDebug,
        arguments: vec![Value::Span(h(HandleKind::Span))],
    };
    for mismatch in 0..3 {
        let mut session = Session::new(binding(), budget()).unwrap();
        session.receive(envelope(Message::Ready)).unwrap();
        if mismatch != 0 {
            session.receive(envelope(Message::Call(call.clone()))).unwrap();
        }
        let mut proposed = call.clone();
        if mismatch == 1 {
            proposed.id = 2;
        }
        if mismatch == 2 {
            proposed.method = Method::SpanFile;
        }
        assert!(session.validate_pending_call(&proposed).is_err());
        assert_eq!(session.phase(), Phase::Terminal);
        assert!(session.budget().check().is_err());
    }
    let mut session = Session::new(binding(), budget()).unwrap();
    session.receive(envelope(Message::Ready)).unwrap();
    session.receive(envelope(Message::Call(call.clone()))).unwrap();
    let before = session.budget().usage().unwrap().calls;
    session.validate_pending_call(&call).unwrap();
    assert_eq!(session.phase(), Phase::AwaitReply);
    assert_eq!(session.budget().usage().unwrap().calls, before);
    session.reply(call.id, Value::Text("span".into())).unwrap();
}

#[test]
fn pending_call_binds_argument_text_handles_vectors_and_nested_values() {
    let span = h(HandleKind::Span);
    let stream = h(HandleKind::Stream);
    let second = Handle { slot: 1, ..stream };
    let make = |method, arguments| Call { id: 1, method, arguments };
    let originals = [
        make(Method::TrackPath, vec![Value::Text("original".into())]),
        make(Method::TsDrop, vec![Value::Stream(stream)]),
        make(
            Method::TsConcatStreams,
            vec![Value::OptionalStream(None), Value::Streams(vec![stream, second])],
        ),
        make(
            Method::TsFromTokenTree,
            vec![Value::Tree(Box::new(Tree::Group {
                delimiter: 0,
                stream: Some(stream),
                spans: [span; 3],
            }))],
        ),
        make(
            Method::TsFromTokenTree,
            vec![Value::Tree(Box::new(Tree::Literal(Literal {
                kind: 2,
                raw_hashes: 0,
                symbol: "12".into(),
                suffix: None,
                span,
            })))],
        ),
        make(
            Method::EmitDiagnostic,
            vec![Value::Diagnostic(Box::new(Diagnostic {
                level: 0,
                message: "root".into(),
                spans: vec![span],
                children: vec![Diagnostic {
                    level: 2,
                    message: "child".into(),
                    spans: vec![],
                    children: vec![],
                }],
            }))],
        ),
        make(
            Method::SpanSubspan,
            vec![
                Value::Span(span),
                Value::Bound(Bound::Included(1)),
                Value::Bound(Bound::Excluded(3)),
            ],
        ),
    ];
    for (which, original) in originals.into_iter().enumerate() {
        let mut changed = original.clone();
        match (&mut changed.arguments[..], which) {
            ([Value::Text(text)], 0) => *text = "changed".into(),
            ([Value::Stream(handle)], 1) => *handle = second,
            ([_, Value::Streams(handles)], 2) => handles.swap(0, 1),
            ([Value::Tree(tree)], 3) => {
                let Tree::Group { spans, .. } = &mut **tree else { panic!() };
                spans[2].generation += 1;
            }
            ([Value::Tree(tree)], 4) => {
                let Tree::Literal(literal) = &mut **tree else { panic!() };
                literal.suffix = Some("u32".into());
            }
            ([Value::Diagnostic(diagnostic)], 5) => {
                diagnostic.children[0].message = "changed child".into()
            }
            ([_, bound, _], 6) => *bound = Value::Bound(Bound::Excluded(1)),
            _ => panic!("fixture shape"),
        }
        assert_eq!((changed.id, changed.method), (original.id, original.method));
        let mut session = Session::new(binding(), budget()).unwrap();
        session.receive(envelope(Message::Ready)).unwrap();
        session.receive(envelope(Message::Call(original))).unwrap();
        assert_eq!(session.validate_pending_call(&changed), Err(Error::Identity));
        assert_eq!(session.phase(), Phase::Terminal);
        assert_eq!(session.budget().check(), Err(Error::Identity));
        assert_eq!(session.reply(1, sample(changed.method.response())), Err(Error::Identity));
    }
}

#[test]
fn pending_snapshot_is_budgeted_without_consuming_handles_or_new_call_grants() {
    let b = budget();
    let mut table = HandleTable::new(17, b.clone()).unwrap();
    let first = table.insert(HandleKind::Stream, 1).unwrap();
    let second = table.insert(HandleKind::Stream, 2).unwrap();
    let mut session = Session::new(binding(), b.clone()).unwrap();
    session.receive(envelope(Message::Ready)).unwrap();
    let call = Call { id: 1, method: Method::TsDrop, arguments: vec![Value::Stream(first)] };
    let before = b.usage().unwrap();
    session.receive(envelope(Message::Call(call.clone()))).unwrap();
    let admitted = b.usage().unwrap();
    assert!(admitted.allocation_bytes > before.allocation_bytes);
    assert!(admitted.work > before.work);
    assert_eq!(admitted.calls, before.calls + 1);
    assert_eq!(admitted.wire_bytes, before.wire_bytes);
    session.validate_pending_call(&call).unwrap();
    let validated = b.usage().unwrap();
    assert!(validated.allocation_bytes > admitted.allocation_bytes);
    assert!(validated.work > admitted.work);
    assert_eq!(validated.calls, admitted.calls);
    assert_eq!(validated.wire_bytes, admitted.wire_bytes);
    let changed = Call { arguments: vec![Value::Stream(second)], ..call };
    assert_eq!(session.validate_pending_call(&changed), Err(Error::Identity));
    assert_eq!(table.live(), 2, "the guard must not consume either stream");
    table.clear();

    let tight = Budget::new(
        Limits { allocation_bytes: (2 * std::mem::size_of::<usize>()) as u64, ..limits() },
        Instant::now() + Duration::from_secs(30),
    )
    .unwrap();
    let mut session = Session::new(binding(), tight.clone()).unwrap();
    session.receive(envelope(Message::Ready)).unwrap();
    let call = Call {
        id: 1,
        method: Method::TrackPath,
        arguments: vec![Value::Text("needs a retained snapshot".into())],
    };
    assert_eq!(
        session.receive(envelope(Message::Call(call))),
        Err(Error::Budget("allocation bytes"))
    );
    assert_eq!(session.phase(), Phase::Terminal);
    assert_eq!(tight.check(), Err(Error::Budget("allocation bytes")));
}

#[test]
fn session_owner_survives_moves_but_not_reconstruction_on_the_same_budget() {
    let b = budget();
    let original = Session::new(binding(), b.clone()).unwrap();
    let owner = original.owner();
    let mut moved = (original,).0;
    assert!(owner.matches(&moved));
    let mut replacement = Session::new(binding(), b.clone()).unwrap();
    assert!(!owner.matches(&replacement));
    assert!(moved.budget().shares_owner(replacement.budget()));
    replacement.receive(envelope(Message::Ready)).unwrap();
    replacement.receive(envelope(Message::Finish { output: None })).unwrap();
    assert_eq!(b.check(), Ok(()));
    assert_eq!(moved.receive(envelope(Message::Ready)), Ok(Admission::Ready));
    assert!(owner.matches(&moved));
}

#[test]
fn all_messages_and_empty_optional_values_roundtrip() {
    let messages = [
        Message::Begin {
            declaration: 5,
            kind: 1,
            inputs: vec![h(HandleKind::Stream); 2],
            globals: [h(HandleKind::Span); 3],
        },
        Message::Ready,
        Message::Finish { output: None },
        Message::Finish { output: Some(h(HandleKind::Stream)) },
        Message::Failure { reason: "bounded panic".into() },
        Message::Cancel,
    ];
    for message in messages {
        let e = envelope(message);
        assert_eq!(decode(&encode(&e, &budget()).unwrap(), &budget()).unwrap(), e);
    }
    for value in [
        Value::OptionalText(None),
        Value::OptionalSpan(None),
        Value::OptionalStream(None),
        Value::Bound(Bound::Unbounded),
        Value::Bound(Bound::Included(u64::MAX)),
        Value::Trees(vec![]),
        Value::Streams(vec![]),
        Value::Result { ok: false, value: Box::new(Value::Unit) },
    ] {
        let e = envelope(Message::Reply { id: 1, value });
        assert_eq!(decode(&encode(&e, &budget()).unwrap(), &budget()).unwrap(), e);
    }
}

#[test]
fn frame_accepts_fragmentation_but_not_following_frames() {
    let bytes = encode(&envelope(Message::Ready), &budget()).unwrap();
    let mut decoder = FrameDecoder::new(budget());
    for (i, byte) in bytes.iter().enumerate() {
        let result = decoder.push(&[*byte]).unwrap();
        if i + 1 == bytes.len() {
            assert_eq!(result, Some(envelope(Message::Ready)));
        } else {
            assert!(result.is_none());
        }
    }
    assert_eq!(decoder.needed(), 0);
    assert_eq!(decoder.push(&[]), Err(Error::Phase));
    let mut two = bytes.clone();
    two.extend_from_slice(&bytes);
    assert!(decode(&two, &budget()).is_err());
}

#[test]
fn all_truncated_prefixes_refuse_without_panicking() {
    let e = envelope(Message::Call(Call {
        id: 1,
        method: Method::TsConcatTrees,
        arguments: vec![sample(Type::OptionalStream), sample(Type::Trees)],
    }));
    let bytes = encode(&e, &budget()).unwrap();
    for n in 0..bytes.len() {
        let b = budget();
        let error = decode(&bytes[..n], &b).unwrap_err();
        assert_eq!(b.clone().check(), Err(error), "prefix {n}");
    }
}

#[test]
fn a_failed_result_reservation_latches_without_taking_any_handle() {
    let probe = budget();
    let table = HandleTable::<u64>::new(17, probe.clone()).unwrap();
    let reserved = probe.usage().unwrap().allocation_bytes;
    drop(table);
    let b = Budget::new(
        Limits { allocation_bytes: reserved + 7, ..limits() },
        Instant::now() + Duration::from_secs(30),
    )
    .unwrap();
    let mut table = HandleTable::new(17, b.clone()).unwrap();
    let h = table.insert(HandleKind::Stream, 1u64).unwrap();
    assert_eq!(
        table.consume(&[HandleUse { handle: h, mode: UseMode::Consume }]),
        Err(Error::Budget("allocation bytes"))
    );
    assert_eq!(table.live(), 1);
    assert_eq!(b.clone().charge(Charge::default()), Err(Error::Budget("allocation bytes")));
    table.clear();
    assert_eq!(table.live(), 0);
    assert_eq!(b.check(), Err(Error::Budget("allocation bytes")));
}

#[test]
fn hostile_tags_and_bool_and_utf8_and_counts_refuse() {
    let ready = encode(&envelope(Message::Ready), &budget()).unwrap();
    // Four-byte framing + 4 magic + 4 version + 8 invocation + 7 digests.
    let message_offset = 244;
    let mut bytes = ready.clone();
    bytes[message_offset] = 255;
    assert!(decode(&bytes, &budget()).is_err());
    let mut bytes = ready;
    bytes[4] = 0;
    assert!(decode(&bytes, &budget()).is_err());
    let mut bytes =
        encode(&envelope(Message::Reply { id: 1, value: Value::Bool(true) }), &budget()).unwrap();
    *bytes.last_mut().unwrap() = 2;
    assert!(decode(&bytes, &budget()).is_err());
    let mut bytes = encode(&envelope(Message::Failure { reason: "x".into() }), &budget()).unwrap();
    *bytes.last_mut().unwrap() = 255;
    assert!(decode(&bytes, &budget()).is_err());
    let mut bytes = encode(&envelope(Message::Failure { reason: "x".into() }), &budget()).unwrap();
    bytes[message_offset + 1..message_offset + 5].copy_from_slice(&u32::MAX.to_le_bytes());
    assert!(decode(&bytes, &budget()).is_err());
    assert!(Method::from_tag(0).is_err());
    assert!(Method::from_tag(33).is_err());
}

#[test]
fn oversized_frame_rejected_before_allocation() {
    let b = budget();
    let before = b.usage().unwrap();
    let mut decoder = FrameDecoder::new(b.clone());
    assert_eq!(decoder.push(&65537u32.to_le_bytes()), Err(Error::Budget("frame bytes")));
    assert_eq!(b.usage().unwrap().allocation_bytes, before.allocation_bytes);
    assert_eq!(decoder.push(&[]), Err(Error::Budget("frame bytes")));
}

#[test]
fn allocation_budget_checked_before_frame_reservation() {
    let mut limits = limits();
    limits.allocation_bytes = 3;
    let b = Budget::new(limits, Instant::now() + Duration::from_secs(30)).unwrap();
    assert_eq!(
        FrameDecoder::new(b.clone()).push(&4u32.to_le_bytes()),
        Err(Error::Budget("allocation bytes"))
    );
    assert_eq!(b.usage().unwrap().allocation_bytes, 0);
}

#[test]
fn depth_limit_applies_to_results_and_diagnostics() {
    let mut value = Value::Unit;
    for _ in 0..18 {
        value = Value::Result { ok: true, value: Box::new(value) };
    }
    assert_eq!(
        encode(&envelope(Message::Reply { id: 1, value }), &budget()),
        Err(Error::Budget("depth"))
    );
    let mut d = Diagnostic { level: 2, message: String::new(), spans: vec![], children: vec![] };
    for _ in 0..18 {
        d = Diagnostic { level: 2, message: String::new(), spans: vec![], children: vec![d] };
    }
    let bytes = encode(
        &envelope(Message::Reply { id: 1, value: Value::Diagnostic(Box::new(d)) }),
        &Budget::new(Limits { depth: 32, ..limits() }, Instant::now() + Duration::from_secs(30))
            .unwrap(),
    )
    .unwrap();
    assert_eq!(decode(&bytes, &budget()), Err(Error::Budget("depth")));
}

#[test]
fn identity_is_exact_and_a_mismatch_permanently_closes_session() {
    for which in 0..9 {
        let mut changed = binding();
        match which {
            0 => changed.version += 1,
            1 => changed.invocation += 1,
            2 => changed.compiler[0] ^= 1,
            3 => changed.worker[0] ^= 1,
            4 => changed.artifact[0] ^= 1,
            5 => changed.metadata[0] ^= 1,
            6 => changed.unit[0] ^= 1,
            7 => changed.input_closure[0] ^= 1,
            _ => changed.host_abi[0] ^= 1,
        };
        let mut s = Session::new(binding(), budget()).unwrap();
        assert_eq!(
            s.receive(Envelope { binding: changed, message: Message::Ready }),
            Err(Error::Identity)
        );
        assert_eq!(s.phase(), Phase::Terminal);
        assert!(s.receive(envelope(Message::Ready)).is_err());
    }
}

#[test]
fn phase_and_sequence_and_response_schema_fail_closed() {
    let call = Call { id: 1, method: Method::TsIsEmpty, arguments: vec![sample(Type::Stream)] };
    let mut s = Session::new(binding(), budget()).unwrap();
    assert!(s.receive(envelope(Message::Call(call.clone()))).is_err());
    let mut s = Session::new(binding(), budget()).unwrap();
    s.receive(envelope(Message::Ready)).unwrap();
    s.receive(envelope(Message::Call(call.clone()))).unwrap();
    assert!(s.receive(envelope(Message::Finish { output: None })).is_err());
    let mut s = Session::new(binding(), budget()).unwrap();
    s.receive(envelope(Message::Ready)).unwrap();
    s.receive(envelope(Message::Call(call.clone()))).unwrap();
    assert_eq!(s.reply(2, Value::Bool(false)), Err(Error::Sequence));
    assert_eq!(s.phase(), Phase::Terminal);
    let mut s = Session::new(binding(), budget()).unwrap();
    s.receive(envelope(Message::Ready)).unwrap();
    s.receive(envelope(Message::Call(call))).unwrap();
    assert_eq!(s.reply(1, Value::Unit), Err(Error::Schema));
}

#[test]
fn protocol_refusal_aborts_existing_and_new_nested_sessions() {
    for fault in 0..6 {
        let b = budget();
        let mut owner = Session::new(binding(), b.clone()).unwrap();
        let mut nested_binding = binding();
        nested_binding.invocation += 1;
        let mut nested = Session::new(nested_binding.clone(), b.clone()).unwrap();
        let call = Call { id: 1, method: Method::TsIsEmpty, arguments: vec![sample(Type::Stream)] };
        let error = match fault {
            0 => {
                let mut bad = binding();
                bad.worker[0] ^= 1;
                owner.receive(Envelope { binding: bad, message: Message::Ready }).unwrap_err()
            }
            1 => owner.receive(envelope(Message::Finish { output: None })).unwrap_err(),
            2 | 3 => {
                owner.receive(envelope(Message::Ready)).unwrap();
                let bad = if fault == 2 {
                    Call { id: 2, ..call }
                } else {
                    Call { arguments: vec![Value::Bool(true)], ..call }
                };
                owner.receive(envelope(Message::Call(bad))).unwrap_err()
            }
            _ => {
                owner.receive(envelope(Message::Ready)).unwrap();
                owner.receive(envelope(Message::Call(call))).unwrap();
                if fault == 4 {
                    owner.reply(2, Value::Bool(false)).unwrap_err()
                } else {
                    owner.reply(1, Value::Unit).unwrap_err()
                }
            }
        };
        assert_eq!(
            error,
            [
                Error::Identity,
                Error::Phase,
                Error::Sequence,
                Error::Schema,
                Error::Sequence,
                Error::Schema
            ][fault]
        );
        assert_eq!(b.check(), Err(error.clone()));
        assert_eq!(Session::new(nested_binding.clone(), b.clone()).unwrap_err(), error);
        assert_eq!(
            nested.receive(Envelope { binding: nested_binding, message: Message::Ready }),
            Err(error)
        );
        assert_eq!(nested.phase(), Phase::Terminal);
    }
    let b = budget();
    let mut bad = binding();
    bad.version += 1;
    assert_eq!(Session::new(bad, b.clone()).unwrap_err(), Error::Identity);
    assert_eq!(b.check(), Err(Error::Identity));
}

#[test]
fn normal_nested_completion_keeps_the_parent_grant_active() {
    let b = budget();
    let mut parent = Session::new(binding(), b.clone()).unwrap();
    let mut child_binding = binding();
    child_binding.invocation += 1;
    let mut child = Session::new(child_binding.clone(), b.clone()).unwrap();
    child.receive(Envelope { binding: child_binding.clone(), message: Message::Ready }).unwrap();
    assert_eq!(
        child.receive(Envelope {
            binding: child_binding,
            message: Message::Finish { output: None }
        }),
        Ok(Admission::Finished(None))
    );
    assert_eq!(b.check(), Ok(()));
    assert_eq!(parent.receive(envelope(Message::Ready)), Ok(Admission::Ready));
}

#[test]
fn a_valid_roundtrip_advances_exactly_once_and_cancellation_is_terminal() {
    let mut s = Session::new(binding(), budget()).unwrap();
    assert_eq!(s.receive(envelope(Message::Ready)).unwrap(), Admission::Ready);
    let c = Call { id: 1, method: Method::TsIsEmpty, arguments: vec![sample(Type::Stream)] };
    assert_eq!(s.receive(envelope(Message::Call(c.clone()))).unwrap(), Admission::Call(c));
    assert_eq!(
        s.reply(1, Value::Bool(false)).unwrap().message,
        Message::Reply { id: 1, value: Value::Bool(false) }
    );
    let c = Call { id: 1, method: Method::TsIsEmpty, arguments: vec![sample(Type::Stream)] };
    assert_eq!(s.receive(envelope(Message::Call(c))), Err(Error::Sequence));
    let mut s = Session::new(binding(), budget()).unwrap();
    assert_eq!(s.cancel().message, Message::Cancel);
    assert!(s.receive(envelope(Message::Ready)).is_err());
}

#[test]
fn handle_identity_and_generation_and_kind_are_checked() {
    let mut table = HandleTable::new(17, budget()).unwrap();
    let a = table.insert(HandleKind::Stream, 42).unwrap();
    assert_eq!(*table.get(a).unwrap(), 42);
    for bad in [
        Handle { invocation: 18, ..a },
        Handle { generation: 0, ..a },
        Handle { generation: 2, ..a },
        Handle { kind: HandleKind::Span, ..a },
        Handle { slot: 999, ..a },
    ] {
        assert!(table.get(bad).is_err());
    }
    assert_eq!(
        table.consume(&[HandleUse { handle: a, mode: UseMode::Consume }]).unwrap(),
        vec![42]
    );
    assert!(table.get(a).is_err());
    let b = table.insert(HandleKind::Stream, 43).unwrap();
    assert_eq!(a.slot, b.slot);
    assert_eq!(b.generation, a.generation + 1);
    assert!(table.get(a).is_err());
    table.clear();
    assert!(table.get(b).is_err());
    assert_eq!(table.insert(HandleKind::Stream, 44), Err(Error::Phase));
}

/// The search for a reusable slot starts at a mark instead of slot 0. It must
/// still pick the lowest reusable slot, whatever order slots were freed in.
#[test]
fn a_new_handle_takes_the_lowest_reusable_slot() {
    let mut t = HandleTable::new(17, budget()).unwrap();
    let consume = |handle| HandleUse { handle, mode: UseMode::Consume };
    let handles: Vec<Handle> =
        (0..6).map(|value| t.insert(HandleKind::Stream, value).unwrap()).collect();
    assert_eq!(handles.iter().map(|h| h.slot).collect::<Vec<_>>(), [0, 1, 2, 3, 4, 5]);
    // Free a high slot, then lower ones: the mark has to move down each time.
    t.consume(&[consume(handles[4])]).unwrap();
    t.consume(&[consume(handles[1]), consume(handles[3])]).unwrap();
    let slots: Vec<(u32, u32)> = (10..15)
        .map(|value| {
            let handle = t.insert(HandleKind::Stream, value).unwrap();
            assert_eq!(*t.get(handle).unwrap(), value);
            (handle.slot, handle.generation)
        })
        .collect();
    // The three freed slots lowest first, each at its next generation, and
    // only then new slots.
    assert_eq!(slots, [(1, 2), (3, 2), (4, 2), (6, 1), (7, 1)]);
    assert_eq!(t.live(), 8);
    // A stale handle to a reused slot names nothing.
    assert!(t.get(handles[1]).is_err());
    assert_eq!(*t.get(handles[0]).unwrap(), 0);
}

#[test]
fn duplicate_or_late_invalid_consumption_is_atomic() {
    let mut t = HandleTable::new(17, budget()).unwrap();
    let a = t.insert(HandleKind::Stream, 1).unwrap();
    let b = t.insert(HandleKind::Stream, 2).unwrap();
    let consume = |handle| HandleUse { handle, mode: UseMode::Consume };
    assert!(t.consume(&[consume(a), consume(a)]).is_err());
    assert_eq!(t.live(), 2);
    assert_eq!(*t.get(a).unwrap(), 1);
    assert!(t.consume(&[consume(a), consume(Handle { generation: 99, ..b })]).is_err());
    assert_eq!(t.live(), 2);
    assert_eq!(*t.get(a).unwrap(), 1);
    assert!(t.consume(&[HandleUse { handle: a, mode: UseMode::Borrow }, consume(a)]).is_err());
    assert_eq!(t.live(), 2);
    assert!(t.consume(&[HandleUse { handle: a, mode: UseMode::Borrow }; 2]).unwrap().is_empty());
    assert_eq!(t.consume(&[consume(a), consume(b)]).unwrap(), vec![1, 2]);
    assert_eq!(t.live(), 0);
}

#[test]
fn span_consumption_and_duplicate_nested_group_rejected() {
    let b = budget();
    let mut t = HandleTable::new(17, b.clone()).unwrap();
    let stream = t.insert(HandleKind::Stream, 1).unwrap();
    let span = t.insert(HandleKind::Span, 2).unwrap();
    assert!(t.consume(&[HandleUse { handle: span, mode: UseMode::Consume }]).is_err());
    let c = Call {
        id: 1,
        method: Method::TsConcatTrees,
        arguments: vec![
            Value::OptionalStream(Some(stream)),
            Value::Trees(vec![Tree::Group {
                delimiter: 1,
                stream: Some(stream),
                spans: [span; 3],
            }]),
        ],
    };
    let uses = c.handle_uses(&b).unwrap();
    assert!(t.consume(&uses).is_err());
    assert_eq!(*t.get(stream).unwrap(), 1);
}

#[test]
fn shared_budget_limits_nested_tables_and_releases_credits() {
    let b = Budget::new(
        Limits { live_handles: 1, ..limits() },
        Instant::now() + Duration::from_secs(30),
    )
    .unwrap();
    let mut outer = HandleTable::new(17, b.clone()).unwrap();
    let mut inner = HandleTable::new(18, b.clone()).unwrap();
    let a = outer.insert(HandleKind::Stream, 1).unwrap();
    assert_eq!(inner.insert(HandleKind::Stream, 2), Err(Error::Budget("live handles")));
    assert!(outer.consume(&[HandleUse { handle: a, mode: UseMode::Consume }]).is_err());
    outer.clear();
    inner.clear(); // cleanup releases credits despite sticky failure
    assert_eq!(b.check(), Err(Error::Budget("live handles")));
    let b = Budget::new(
        Limits { live_handles: 1, ..limits() },
        Instant::now() + Duration::from_secs(30),
    )
    .unwrap();
    let mut outer = HandleTable::new(17, b.clone()).unwrap();
    let mut inner = HandleTable::new(18, b).unwrap();
    outer.insert(HandleKind::Stream, 1).unwrap();
    drop(outer);
    inner.insert(HandleKind::Span, 3).unwrap();
}

#[test]
fn shared_cumulative_counters_are_atomic_and_cannot_reset() {
    let b = Budget::new(Limits { work: 3, ..limits() }, Instant::now() + Duration::from_secs(30))
        .unwrap();
    let nested = b.clone();
    b.charge(Charge { work: 2, ..Charge::default() }).unwrap();
    assert_eq!(
        nested.charge(Charge { work: 2, allocation_bytes: 1, ..Charge::default() }),
        Err(Error::Budget("work"))
    );
    assert_eq!(b.usage().unwrap(), Charge { work: 2, ..Charge::default() });
    assert_eq!(nested.charge(Charge { work: 1, ..Charge::default() }), Err(Error::Budget("work")));
    assert_eq!(b.charge(Charge::default()), Err(Error::Budget("work")));
    assert_eq!(b.deadline(), nested.deadline());
}

#[test]
fn exact_and_one_short_encoded_capacity_copy_and_wire_budgets() {
    let e = envelope(Message::Failure { reason: "a".repeat(513) });
    let b = budget();
    let bytes = encode(&e, &b).unwrap();
    let used = b.usage().unwrap();
    assert!(
        used.allocation_bytes >= u64::try_from(bytes.capacity() + bytes.capacity() / 2).unwrap()
    );
    assert!(used.work >= u64::try_from(bytes.len() + bytes.capacity() / 2).unwrap());
    let exact = Limits {
        frame_bytes: u32::try_from(bytes.len() - 4).unwrap(),
        allocation_bytes: used.allocation_bytes,
        work: used.work,
        wire_bytes: used.wire_bytes,
        ..limits()
    };
    // A reduced frame cap changes the growth schedule, so exact allocation/work
    // bounds use the original frame cap; the payload size bound is independent.
    let exact = Limits { frame_bytes: limits().frame_bytes, ..exact };
    assert_eq!(
        encode(&e, &Budget::new(exact, Instant::now() + Duration::from_secs(30)).unwrap()).unwrap(),
        bytes
    );
    for short in [
        Limits { allocation_bytes: used.allocation_bytes - 1, ..exact },
        Limits { work: used.work - 1, ..exact },
        Limits { wire_bytes: used.wire_bytes - 1, ..exact },
    ] {
        let b = Budget::new(short, Instant::now() + Duration::from_secs(30)).unwrap();
        let error = encode(&e, &b).unwrap_err();
        assert_eq!(b.clone().charge(Charge::default()), Err(error));
    }
    let exact_frame = Limits { frame_bytes: u32::try_from(bytes.len() - 4).unwrap(), ..limits() };
    assert!(
        encode(&e, &Budget::new(exact_frame, Instant::now() + Duration::from_secs(30)).unwrap())
            .is_ok()
    );
    let short = Limits { frame_bytes: exact_frame.frame_bytes - 1, ..limits() };
    assert_eq!(
        encode(&e, &Budget::new(short, Instant::now() + Duration::from_secs(30)).unwrap()),
        Err(Error::Budget("frame bytes"))
    );
}

#[test]
fn decoder_copy_and_utf8_work_and_allocation_are_priced() {
    let e = envelope(Message::Failure { reason: "z".repeat(513) });
    let bytes = encode(&e, &budget()).unwrap();
    let b = budget();
    decode(&bytes, &b).unwrap();
    let used = b.usage().unwrap();
    assert!(used.work >= u64::try_from(bytes.len() + 2 * 513).unwrap());
    for short in [
        Limits { work: used.work - 1, ..limits() },
        Limits { allocation_bytes: used.allocation_bytes - 1, ..limits() },
    ] {
        let b = Budget::new(short, Instant::now() + Duration::from_secs(30)).unwrap();
        let error = decode(&bytes, &b).unwrap_err();
        assert_eq!(b.clone().check(), Err(error));
    }
}

#[test]
fn handle_capacity_is_prepriced_and_failed_capacity_never_resets() {
    let b = budget();
    let mut t = HandleTable::new(17, b.clone()).unwrap();
    let reserved = b.usage().unwrap().allocation_bytes;
    assert!(reserved > 0);
    for n in 0..64 {
        t.insert(HandleKind::Stream, n).unwrap();
    }
    assert_eq!(b.usage().unwrap().allocation_bytes, reserved);
    let short = Budget::new(
        Limits { allocation_bytes: reserved - 1, ..limits() },
        Instant::now() + Duration::from_secs(30),
    )
    .unwrap();
    assert_eq!(
        HandleTable::<i32>::new(17, short.clone()).unwrap_err(),
        Error::Budget("allocation bytes")
    );
    assert_eq!(short.check(), Err(Error::Budget("allocation bytes")));
}

#[test]
fn ownership_collection_prices_replacement_capacity_and_copy_work() {
    let call = Call {
        id: 1,
        method: Method::TsConcatStreams,
        arguments: vec![
            Value::OptionalStream(None),
            Value::Streams(vec![h(HandleKind::Stream); 33]),
        ],
    };
    let b = budget();
    let uses = call.handle_uses(&b).unwrap();
    let used = b.usage().unwrap();
    assert_eq!(uses.len(), 33);
    assert!(
        used.allocation_bytes
            >= u64::try_from(uses.capacity() * std::mem::size_of::<HandleUse>()).unwrap()
    );
    assert!(used.work > 33);
    let exact = Limits { allocation_bytes: used.allocation_bytes, work: used.work, ..limits() };
    assert_eq!(
        call.handle_uses(&Budget::new(exact, Instant::now() + Duration::from_secs(30)).unwrap())
            .unwrap(),
        uses
    );
    for short in [
        Limits { allocation_bytes: used.allocation_bytes - 1, ..exact },
        Limits { work: used.work - 1, ..exact },
    ] {
        let b = Budget::new(short, Instant::now() + Duration::from_secs(30)).unwrap();
        let error = call.handle_uses(&b).unwrap_err();
        assert_eq!(b.clone().check(), Err(error));
    }
}

#[test]
fn depth_overflow_and_cancel_refusals_are_sticky() {
    let b = budget();
    assert_eq!(b.depth(17), Err(Error::Budget("depth")));
    assert_eq!(b.clone().check(), Err(Error::Budget("depth")));
    let b = Budget::new(
        Limits { work: u64::MAX, ..limits() },
        Instant::now() + Duration::from_secs(30),
    )
    .unwrap();
    b.charge(Charge { work: u64::MAX, ..Charge::default() }).unwrap();
    assert_eq!(b.charge(Charge { work: 1, ..Charge::default() }), Err(Error::Overflow));
    assert_eq!(b.clone().check(), Err(Error::Overflow));
    let b = budget();
    b.cancel();
    assert_eq!(b.clone().check(), Err(Error::Phase));
}

#[test]
fn zero_missing_or_expired_authority_inputs_refuse() {
    assert!(
        Budget::new(Limits { depth: 0, ..limits() }, Instant::now() + Duration::from_secs(30))
            .is_err()
    );
    assert!(
        Budget::new(Limits { depth: 129, ..limits() }, Instant::now() + Duration::from_secs(30))
            .is_err()
    );
    assert_eq!(
        Budget::new(limits(), Instant::now() - Duration::from_secs(1)).unwrap_err(),
        Error::Deadline
    );
    let mut b = binding();
    b.compiler = [0; 32];
    assert_eq!(Session::new(b, budget()).unwrap_err(), Error::Identity);
    assert!(HandleTable::<u8>::new(0, budget()).is_err());
}

#[test]
fn wrong_argument_count_type_and_handle_kind_refuse() {
    assert_eq!(
        Call { id: 1, method: Method::TsDrop, arguments: vec![Value::Span(h(HandleKind::Span))] }
            .validate(),
        Err(Error::Schema)
    );
    assert_eq!(
        Call { id: 1, method: Method::TsDrop, arguments: vec![Value::Stream(h(HandleKind::Span))] }
            .validate(),
        Err(Error::Schema)
    );
    assert_eq!(
        Call { id: 1, method: Method::TsDrop, arguments: vec![] }.validate(),
        Err(Error::Schema)
    );
    let c = Call {
        id: 1,
        method: Method::TsFromTokenTree,
        arguments: vec![Value::Tree(Box::new(Tree::Group {
            delimiter: 1,
            stream: None,
            spans: [h(HandleKind::Stream); 3],
        }))],
    };
    assert!(c.handle_uses(&budget()).is_err());
}

#[test]
fn worker_cannot_forge_error_guarantee_or_literal_tags() {
    for kind in [10, 255] {
        let v = Value::Literal(Box::new(Literal {
            kind,
            raw_hashes: 0,
            symbol: String::new(),
            suffix: None,
            span: h(HandleKind::Span),
        }));
        assert!(encode(&envelope(Message::Reply { id: 1, value: v }), &budget()).is_err());
    }
    let mut l = match sample(Type::Literal) {
        Value::Literal(l) => l,
        _ => unreachable!(),
    };
    l.raw_hashes = 1;
    assert!(
        encode(&envelope(Message::Reply { id: 1, value: Value::Literal(l) }), &budget()).is_err()
    );
}

#[test]
fn call_budget_is_shared_across_independent_invocations() {
    let b = Budget::new(Limits { calls: 1, ..limits() }, Instant::now() + Duration::from_secs(30))
        .unwrap();
    let mut a = Session::new(binding(), b.clone()).unwrap();
    let mut second = binding();
    second.invocation = 18;
    let mut c = Session::new(second.clone(), b).unwrap();
    a.receive(envelope(Message::Ready)).unwrap();
    c.receive(Envelope { binding: second.clone(), message: Message::Ready }).unwrap();
    let call = Call { id: 1, method: Method::TrackPath, arguments: vec![Value::Text("x".into())] };
    a.receive(envelope(Message::Call(call.clone()))).unwrap();
    assert_eq!(
        c.receive(Envelope { binding: second, message: Message::Call(call) }),
        Err(Error::Budget("calls"))
    );
}

#[test]
fn live_lookup_preserves_kind_generation_and_charges_the_original_budget() {
    let b = budget();
    let mut table = HandleTable::new(17, b.clone()).unwrap();
    let first = table.insert(HandleKind::Stream, 7u8).unwrap();
    let before = b.usage().unwrap();
    assert_eq!(table.find(HandleKind::Stream, |v| *v == 7).unwrap(), Some(first));
    assert!(b.usage().unwrap().work > before.work);
    assert_eq!(table.find(HandleKind::Span, |v| *v == 7).unwrap(), None);
    table.consume(&[HandleUse { handle: first, mode: UseMode::Consume }]).unwrap();
    assert_eq!(table.find(HandleKind::Stream, |v| *v == 7).unwrap(), None);
    let next = table.insert(HandleKind::Span, 7).unwrap();
    assert_ne!(first.generation, next.generation);
    assert_eq!(table.find(HandleKind::Span, |v| *v == 7).unwrap(), Some(next));
    assert!(table.get(first).is_err());
    table.clear();
    assert_eq!(table.find(HandleKind::Span, |_| true), Err(Error::Phase));

    let b = Budget::new(Limits { work: 1, ..limits() }, Instant::now() + Duration::from_secs(30))
        .unwrap();
    let mut table = HandleTable::new(17, b.clone()).unwrap();
    table.insert(HandleKind::Span, 7).unwrap();
    assert_eq!(table.find(HandleKind::Span, |_| true), Err(Error::Budget("work")));
    assert_eq!(b.check(), Err(Error::Budget("work")));
}
