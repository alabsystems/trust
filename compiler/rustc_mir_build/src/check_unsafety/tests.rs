use rustc_span::def_id::{CRATE_DEF_ID, DefIndex};
use rustc_span::{BytePos, Span, SyntaxContext};

use super::*;

fn retained(body_owner: LocalDefId) -> TrustUnsafeSourceEventRoster {
    TrustUnsafeSourceEventRoster::with_retention(body_owner, true)
}

fn events(roster: &TrustUnsafeSourceEventRoster) -> &[TrustUnsafeSourceEvent] {
    roster.events.as_deref().expect("diagnostic retention enabled")
}

#[test]
fn unsafe_source_occurrences_are_unique_per_body_even_at_one_location() {
    let nested_owner = LocalDefId { local_def_index: DefIndex::from_u32(1) };
    let mut parent = retained(CRATE_DEF_ID);
    let mut nested = retained(nested_owner);
    let kind = UnsafeOpKind::UseOfMutableStatic;
    let span = Span::new(BytePos(5), BytePos(9), SyntaxContext::root(), Some(CRATE_DEF_ID));

    parent.record(&kind, span, HirId::INVALID, &SafetyContext::Safe);
    parent.record(&kind, span, HirId::INVALID, &SafetyContext::Safe);
    nested.record(&kind, span, HirId::INVALID, &SafetyContext::Safe);
    let first = &events(&parent)[0];
    let second = &events(&parent)[1];
    let inner = &events(&nested)[0];

    assert_eq!(first.id, TrustUnsafeSourceEventId { body_owner: CRATE_DEF_ID, occurrence: 0 });
    assert_eq!(second.id, TrustUnsafeSourceEventId { body_owner: CRATE_DEF_ID, occurrence: 1 });
    assert_eq!(inner.id, TrustUnsafeSourceEventId { body_owner: nested_owner, occurrence: 0 });
    assert_ne!(first.id, second.id);
    assert_ne!(first.id, inner.id);
    assert_eq!(&first.kind, &kind);
    assert_eq!(first.source_kind, TrustUnsafeSourceKind::UseOfMutableStatic);
    assert_eq!(first.span.data(), span.data());
    assert_eq!(first.span.data().parent, Some(CRATE_DEF_ID));
    assert_eq!(first.hir_context, HirId::INVALID);
    assert_eq!(first.scope, TrustUnsafeSourceScope::Safe);
    assert_eq!(first.origin, TrustUnsafeSourceOrigin::NonBuiltin);
    assert_eq!(parent.complete().event_count, 2);
    assert_eq!(nested.complete().event_count, 1);
}

#[test]
fn unsafe_source_origin_follows_the_exact_safety_context() {
    let cases = [
        (SafetyContext::Safe, TrustUnsafeSourceScope::Safe, TrustUnsafeSourceOrigin::NonBuiltin),
        (
            SafetyContext::UnsafeFn,
            TrustUnsafeSourceScope::UnsafeFn,
            TrustUnsafeSourceOrigin::NonBuiltin,
        ),
        (
            SafetyContext::UnsafeBlock {
                span: rustc_span::DUMMY_SP,
                hir_id: HirId::INVALID,
                used: false,
                nested_used_blocks: Vec::new(),
            },
            TrustUnsafeSourceScope::ExplicitUnsafeBlock,
            TrustUnsafeSourceOrigin::NonBuiltin,
        ),
        (
            SafetyContext::BuiltinUnsafeBlock,
            TrustUnsafeSourceScope::BuiltinUnsafeBlock,
            TrustUnsafeSourceOrigin::CompilerBuiltin,
        ),
    ];

    for (context, expected_scope, expected_origin) in cases {
        let scope = TrustUnsafeSourceScope::from_safety_context(&context);
        assert_eq!(scope, expected_scope);
        assert_eq!(scope.origin(), expected_origin);

        let kind = UnsafeOpKind::UseOfMutableStatic;
        let mut roster = retained(CRATE_DEF_ID);
        let event = roster
            .record(&kind, rustc_span::DUMMY_SP, HirId::INVALID, &context)
            .expect("diagnostic event retained");
        assert_eq!(event.scope, expected_scope);
        assert_eq!(event.origin, expected_origin);
    }
}

#[test]
fn trace_span_debug_escapes_newline_in_filename() {
    struct NewlineFilename;

    impl std::fmt::Debug for NewlineFilename {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            f.write_str("dir/odd\nname.rs:1:2")
        }
    }

    let span = trace_safe_debug(&NewlineFilename);
    assert_eq!(span, "dir/odd\\nname.rs:1:2");
    assert_eq!(span.lines().count(), 1);
}

#[test]
fn builtin_call_and_nested_body_events_keep_separate_counts() {
    let closure_owner = LocalDefId { local_def_index: DefIndex::from_u32(1) };
    let inline_const_owner = LocalDefId { local_def_index: DefIndex::from_u32(2) };
    let mut parent = retained(CRATE_DEF_ID);
    let mut closure = retained(closure_owner);
    let mut inline_const = retained(inline_const_owner);
    let generated_call = UnsafeOpKind::CallToUnsafeFunction(Some(CRATE_DEF_ID.to_def_id()));
    let user_deref = UnsafeOpKind::DerefOfRawPointer;
    let explicit_unsafe = SafetyContext::UnsafeBlock {
        span: rustc_span::DUMMY_SP,
        hir_id: HirId::INVALID,
        used: false,
        nested_used_blocks: Vec::new(),
    };

    parent.record(
        &generated_call,
        rustc_span::DUMMY_SP,
        HirId::INVALID,
        &SafetyContext::BuiltinUnsafeBlock,
    );
    parent.record(&user_deref, rustc_span::DUMMY_SP, HirId::INVALID, &explicit_unsafe);
    closure.record(&user_deref, rustc_span::DUMMY_SP, HirId::INVALID, &explicit_unsafe);
    inline_const.record(&user_deref, rustc_span::DUMMY_SP, HirId::INVALID, &explicit_unsafe);
    let generated = &events(&parent)[0];
    let user = &events(&parent)[1];
    let closure_event = &events(&closure)[0];
    let inline_const_event = &events(&inline_const)[0];

    assert_eq!(generated.origin, TrustUnsafeSourceOrigin::CompilerBuiltin);
    assert_eq!(generated.scope, TrustUnsafeSourceScope::BuiltinUnsafeBlock);
    assert_eq!(generated.source_kind, TrustUnsafeSourceKind::CallToUnsafeFunction);
    assert_eq!(user.origin, TrustUnsafeSourceOrigin::NonBuiltin);
    assert_eq!(user.scope, TrustUnsafeSourceScope::ExplicitUnsafeBlock);
    assert_eq!(user.source_kind, TrustUnsafeSourceKind::DerefOfRawPointer);
    assert_eq!(
        closure_event.id,
        TrustUnsafeSourceEventId { body_owner: closure_owner, occurrence: 0 }
    );
    assert_eq!(
        inline_const_event.id,
        TrustUnsafeSourceEventId { body_owner: inline_const_owner, occurrence: 0 }
    );
    let parent_complete = parent.complete();
    let closure_complete = closure.complete();
    let inline_const_complete = inline_const.complete();
    assert_eq!((parent_complete.body_owner, parent_complete.event_count), (CRATE_DEF_ID, 2));
    assert_eq!((closure_complete.body_owner, closure_complete.event_count), (closure_owner, 1));
    assert_eq!(
        (inline_const_complete.body_owner, inline_const_complete.event_count),
        (inline_const_owner, 1)
    );
}

#[test]
fn unsafe_source_kind_tags_distinguish_every_current_operation() {
    let def = CRATE_DEF_ID.to_def_id();
    let cases = [
        (CallToUnsafeFunction(Some(def)), TrustUnsafeSourceKind::CallToUnsafeFunction),
        (UseOfInlineAssembly, TrustUnsafeSourceKind::UseOfInlineAssembly),
        (InitializingTypeWithUnsafeField, TrustUnsafeSourceKind::InitializingTypeWithUnsafeField),
        (UseOfMutableStatic, TrustUnsafeSourceKind::UseOfMutableStatic),
        (UseOfExternStatic, TrustUnsafeSourceKind::UseOfExternStatic),
        (UseOfUnsafeField, TrustUnsafeSourceKind::UseOfUnsafeField),
        (DerefOfRawPointer, TrustUnsafeSourceKind::DerefOfRawPointer),
        (AccessToUnionField, TrustUnsafeSourceKind::AccessToUnionField),
        (MutationOfLayoutConstrainedField, TrustUnsafeSourceKind::MutationOfLayoutConstrainedField),
        (BorrowOfLayoutConstrainedField, TrustUnsafeSourceKind::BorrowOfLayoutConstrainedField),
        (
            CallToFunctionWith { function: def, missing: Vec::new(), build_enabled: Vec::new() },
            TrustUnsafeSourceKind::CallToFunctionWith,
        ),
        (UnsafeBinderCast, TrustUnsafeSourceKind::UnsafeBinderCast),
        (CallDropExplicitly(def), TrustUnsafeSourceKind::CallDropExplicitly),
    ];

    for (kind, expected) in cases {
        assert_eq!(TrustUnsafeSourceKind::from_unsafe_op(&kind), expected);
    }
    assert_ne!(
        TrustUnsafeSourceKind::from_unsafe_op(&CallToUnsafeFunction(None)),
        TrustUnsafeSourceKind::from_unsafe_op(&CallToFunctionWith {
            function: def,
            missing: Vec::new(),
            build_enabled: Vec::new(),
        })
    );
}

#[test]
fn normal_scan_counts_many_events_without_retaining_them() {
    let mut roster = TrustUnsafeSourceEventRoster::with_retention(CRATE_DEF_ID, false);
    let kind = UnsafeOpKind::CallToFunctionWith {
        function: CRATE_DEF_ID.to_def_id(),
        missing: vec![rustc_span::sym::feature],
        build_enabled: Vec::new(),
    };

    for _ in 0..100_000 {
        assert!(
            roster
                .record(&kind, rustc_span::DUMMY_SP, HirId::INVALID, &SafetyContext::Safe)
                .is_none()
        );
    }

    assert!(roster.events.is_none());
    assert_eq!(roster.complete().event_count, 100_000);
}
