// trust-types property-based tests: serialization roundtrip + invariants
//
// Uses proptest to generate arbitrary instances of core types and verify:
// 1. JSON roundtrip: deserialize(serialize(x)) == x (or equivalent JSON)
// 2. Hash determinism: hash(x) == hash(x.clone())
// 3. Debug doesn't panic: format!("{:?}", x) is non-empty
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

use proptest::prelude::*;
use trust_types::*;

// ---------------------------------------------------------------------------
// Arbitrary strategies for core types
// ---------------------------------------------------------------------------

fn arb_bin_op() -> impl Strategy<Value = BinOp> {
    prop_oneof![
        Just(BinOp::Add),
        Just(BinOp::Sub),
        Just(BinOp::Mul),
        Just(BinOp::Div),
        Just(BinOp::Rem),
        Just(BinOp::Eq),
        Just(BinOp::Ne),
        Just(BinOp::Lt),
        Just(BinOp::Le),
        Just(BinOp::Gt),
        Just(BinOp::Ge),
        Just(BinOp::BitAnd),
        Just(BinOp::BitOr),
        Just(BinOp::BitXor),
        Just(BinOp::Shl),
        Just(BinOp::Shr),
    ]
}

fn arb_un_op() -> impl Strategy<Value = UnOp> {
    prop_oneof![Just(UnOp::Not), Just(UnOp::Neg), Just(UnOp::PtrMetadata),]
}

fn arb_ty() -> impl Strategy<Value = Ty> {
    let leaf = prop_oneof![
        Just(Ty::Bool),
        Just(Ty::Unit),
        Just(Ty::Never),
        prop::sample::select(vec![8u32, 16, 32, 64, 128])
            .prop_flat_map(|w| prop::bool::ANY.prop_map(move |s| Ty::Int { width: w, signed: s })),
        prop::sample::select(vec![32u32, 64]).prop_map(|w| Ty::Float { width: w }),
    ];

    leaf.prop_recursive(
        3,  // max depth
        32, // max nodes
        4,  // items per collection
        |inner| {
            prop_oneof![
                // Ref
                (prop::bool::ANY, inner.clone())
                    .prop_map(|(m, t)| Ty::Ref { mutable: m, inner: Box::new(t) }),
                // RawPtr generation for proptest coverage.
                (prop::bool::ANY, inner.clone())
                    .prop_map(|(m, t)| Ty::RawPtr { mutable: m, pointee: Box::new(t) }),
                // Slice
                inner.clone().prop_map(|t| Ty::Slice { elem: Box::new(t) }),
                // Array
                (inner.clone(), 0..100u64)
                    .prop_map(|(t, len)| Ty::Array { elem: Box::new(t), len }),
                // Tuple (0-4 elements)
                prop::collection::vec(inner.clone(), 0..4).prop_map(Ty::Tuple),
                // Adt (1-3 fields)
                ("[a-z]{1,8}", prop::collection::vec(("[a-z]{1,6}", inner), 1..3)).prop_map(
                    |(name, fields)| Ty::Adt { adt_kind: None, layout: None, 
                        variants: Vec::new(),
                        name,
                        fields,
                        disc_index_safe: false,
                        // Trust (B3-1 field completion): missed by 11598e13fe;
                        // kept the trust-types test suite uncompilable since B3-1.
                        faithful_enum_repr: None, enum_layout: None, }
                ),
            ]
        },
    )
}

fn arb_projection() -> impl Strategy<Value = Projection> {
    prop_oneof![
        (0..10usize).prop_map(Projection::Field),
        (0..10usize).prop_map(Projection::Index),
        Just(Projection::Deref),
        (0..5usize).prop_map(Projection::Downcast),
        Just(Projection::OpaqueCast(Ty::Unit)),
        Just(Projection::UnwrapUnsafeBinder(Ty::Unit)),
        (0..10usize, prop::bool::ANY).prop_map(|(offset, from_end)| Projection::ConstantIndex {
            offset,
            min_length: offset.saturating_add(1),
            from_end,
        }),
        (0..10usize, 0..10usize, prop::bool::ANY)
            .prop_map(|(from, to, from_end)| Projection::Subslice { from, to, from_end }),
    ]
}

fn arb_place() -> impl Strategy<Value = Place> {
    (0..20usize, prop::collection::vec(arb_projection(), 0..3))
        .prop_map(|(local, projections)| Place { local, projections })
}

fn arb_source_span() -> impl Strategy<Value = SourceSpan> {
    ("[a-z]{1,10}\\.rs", 0..1000u32, 0..200u32, 0..1000u32, 0..200u32).prop_map(
        |(file, ls, cs, le, ce)| SourceSpan {
            file,
            line_start: ls,
            col_start: cs,
            line_end: le,
            col_end: ce,
        },
    )
}

fn arb_sort() -> impl Strategy<Value = Sort> {
    let leaf = prop_oneof![
        Just(Sort::Bool),
        Just(Sort::Int),
        prop::sample::select(vec![8u32, 16, 32, 64, 128]).prop_map(Sort::BitVec),
    ];
    leaf.prop_recursive(
        2, // max depth
        8, // max nodes
        2, // items per collection
        |inner| {
            (inner.clone(), inner)
                .prop_map(|(idx, elem)| Sort::Array(Box::new(idx), Box::new(elem)))
        },
    )
}

fn arb_formula() -> impl Strategy<Value = Formula> {
    let leaf = prop_oneof![
        prop::bool::ANY.prop_map(Formula::Bool),
        (-1000i128..1000).prop_map(Formula::Int),
        (0u128..1000).prop_map(Formula::UInt),
        ((-128i128..128), prop::sample::select(vec![8u32, 16, 32, 64]))
            .prop_map(|(v, w)| Formula::BitVec { value: v, width: w }),
        ("[a-z]{1,6}", arb_sort()).prop_map(|(n, s)| Formula::Var(n, s)),
    ];

    leaf.prop_recursive(
        3,  // max depth
        24, // max nodes
        4,  // items per collection
        |inner| {
            prop_oneof![
                // Unary
                inner.clone().prop_map(|f| Formula::Not(Box::new(f))),
                inner.clone().prop_map(|f| Formula::Neg(Box::new(f))),
                // Binary
                (inner.clone(), inner.clone())
                    .prop_map(|(a, b)| Formula::Eq(Box::new(a), Box::new(b))),
                (inner.clone(), inner.clone())
                    .prop_map(|(a, b)| Formula::Add(Box::new(a), Box::new(b))),
                (inner.clone(), inner.clone())
                    .prop_map(|(a, b)| Formula::Lt(Box::new(a), Box::new(b))),
                (inner.clone(), inner.clone())
                    .prop_map(|(a, b)| Formula::Implies(Box::new(a), Box::new(b))),
                // N-ary
                prop::collection::vec(inner.clone(), 0..4).prop_map(Formula::And),
                prop::collection::vec(inner.clone(), 0..4).prop_map(Formula::Or),
                // Ite
                (inner.clone(), inner.clone(), inner.clone()).prop_map(|(c, t, e)| Formula::Ite(
                    Box::new(c),
                    Box::new(t),
                    Box::new(e)
                )),
                // BV ops (select a few representative ones)
                (inner.clone(), inner.clone(), prop::sample::select(vec![8u32, 16, 32, 64]))
                    .prop_map(|(a, b, w)| Formula::BvAdd(Box::new(a), Box::new(b), w)),
                (inner.clone(), inner.clone(), prop::sample::select(vec![8u32, 16, 32, 64]))
                    .prop_map(|(a, b, w)| Formula::BvSLe(Box::new(a), Box::new(b), w)),
                // Quantifiers
                (prop::collection::vec(("[a-z]{1,4}", arb_sort()), 1..3), inner.clone(),).prop_map(
                    |(bindings, body)| Formula::Forall(
                        bindings
                            .into_iter()
                            .map(|(s, sort)| (trust_types::Symbol::intern(&s), sort))
                            .collect(),
                        Box::new(body)
                    )
                ),
                // Select/Store
                (inner.clone(), inner.clone())
                    .prop_map(|(arr, idx)| Formula::Select(Box::new(arr), Box::new(idx))),
            ]
        },
    )
}

fn arb_contract_kind() -> impl Strategy<Value = ContractKind> {
    prop_oneof![
        Just(ContractKind::Requires),
        Just(ContractKind::Ensures),
        Just(ContractKind::Invariant),
        Just(ContractKind::Decreases),
    ]
}

fn arb_proof_level() -> impl Strategy<Value = ProofLevel> {
    prop_oneof![
        Just(ProofLevel::L0Safety),
        Just(ProofLevel::L1Functional),
        Just(ProofLevel::L2Domain),
    ]
}

fn arb_temporal_operator() -> impl Strategy<Value = TemporalOperator> {
    prop_oneof![
        Just(TemporalOperator::Eventually),
        Just(TemporalOperator::Always),
        Just(TemporalOperator::AlwaysEventually),
        Just(TemporalOperator::LeadsTo),
    ]
}

fn arb_fairness_constraint() -> impl Strategy<Value = FairnessConstraint> {
    prop_oneof![
        ("[a-z]{1,8}", prop::collection::vec("[a-z]{1,6}".prop_map(String::from), 1..3))
            .prop_map(|(action, vars)| FairnessConstraint::Weak { action, vars }),
        ("[a-z]{1,8}", prop::collection::vec("[a-z]{1,6}".prop_map(String::from), 1..3))
            .prop_map(|(action, vars)| FairnessConstraint::Strong { action, vars }),
    ]
}

fn arb_liveness_property() -> impl Strategy<Value = LivenessProperty> {
    (
        "[a-z]{1,10}",
        arb_temporal_operator(),
        "[a-z]{1,10}",
        prop::option::of("[a-z]{1,10}".prop_map(String::from)),
        prop::collection::vec(arb_fairness_constraint(), 0..2),
    )
        .prop_map(|(name, operator, predicate, consequent, fairness)| LivenessProperty {
            name,
            operator,
            predicate,
            consequent,
            fairness,
        })
}

/// VcKind strategy covering all variants.
fn arb_vc_kind() -> impl Strategy<Value = VcKind> {
    prop_oneof![
        (arb_bin_op(), arb_ty(), arb_ty())
            .prop_map(|(op, t1, t2)| VcKind::ArithmeticOverflow { op, operand_tys: (t1, t2) }),
        (arb_bin_op(), arb_ty(), arb_ty()).prop_map(|(op, ot, st)| VcKind::ShiftOverflow {
            op,
            operand_ty: ot,
            shift_ty: st
        }),
        Just(VcKind::DivisionByZero),
        Just(VcKind::RemainderByZero),
        Just(VcKind::IndexOutOfBounds),
        Just(VcKind::SliceBoundsCheck),
        "[a-z ]{1,20}".prop_map(|m| VcKind::Assertion { message: m }),
        "[a-z:]{1,20}".prop_map(|c| VcKind::Precondition { callee: c }),
        Just(VcKind::Postcondition),
        (arb_ty(), arb_ty()).prop_map(|(f, t)| VcKind::CastOverflow { from_ty: f, to_ty: t }),
        arb_ty().prop_map(|t| VcKind::NegationOverflow { ty: t }),
        Just(VcKind::Unreachable),
        "[a-z]{1,10}".prop_map(|s| VcKind::DeadState { state: s }),
        Just(VcKind::Deadlock),
        "[a-z ]{1,20}".prop_map(|p| VcKind::Temporal { machine: None, property: p }),
        arb_liveness_property().prop_map(|p| VcKind::Liveness { property: p, machine: None }),
        arb_fairness_constraint().prop_map(|c| VcKind::Fairness { constraint: c }),
        ("[a-z]{1,8}", "[a-z]{1,8}", 1..10usize).prop_map(|(s, k, l)| VcKind::TaintViolation {
            source_label: s,
            sink_kind: k,
            path_length: l,
        }),
        ("[a-z.]{1,15}", "[a-z]{1,10}")
            .prop_map(|(f, a)| VcKind::RefinementViolation { spec_file: f, action: a }),
        ("[a-z]{1,8}", "[a-z]{1,8}", "[a-z ]{1,15}").prop_map(|(s, f, r)| {
            VcKind::ResilienceViolation { service: s, failure_mode: f, reason: r }
        }),
        ("[a-z]{1,8}", "[a-z ]{1,15}")
            .prop_map(|(p, v)| VcKind::ProtocolViolation { protocol: p, violation: v }),
        ("[a-z]{1,8}", "[a-z]{1,8}")
            .prop_map(|(c, m)| VcKind::NonTermination { context: c, measure: m }),
        ("[a-z]{1,8}", "[a-z]{1,8}", "[a-z]{1,8}").prop_map(|(v, a, b)| VcKind::DataRace {
            variable: v,
            thread_a: a,
            thread_b: b,
        }),
        ("[a-z]{1,8}", "[a-z]{1,8}", "[a-z]{1,8}").prop_map(|(v, a, r)| {
            VcKind::InsufficientOrdering { variable: v, actual: a, required: r }
        }),
        ("[a-z_]{1,15}", "[a-z_]{1,15}")
            .prop_map(|(p, c)| VcKind::TranslationValidation { pass: p, check: c }),
        ("[a-z_]{1,15}", "[a-z_]{1,15}")
            .prop_map(|(fact, evidence)| VcKind::BinaryAbiContradiction { fact, evidence }),
        ("[a-z_]{1,15}", "[a-z_ ]{1,30}")
            .prop_map(|(callee, desc)| VcKind::BinaryCopySinkLengthViolation { callee, desc }),
        ("[a-z_]{1,15}", "[a-z_ ]{1,30}")
            .prop_map(|(callee, desc)| VcKind::FfiBoundaryViolation { callee, desc }),
        prop::bool::ANY.prop_map(|mutable| VcKind::AliasingViolation { mutable }),
        Just(VcKind::UseAfterFree),
        Just(VcKind::DoubleFree),
        Just(VcKind::LifetimeViolation),
        Just(VcKind::SendViolation),
        Just(VcKind::SyncViolation),
        ("[a-z_ <>=]{1,30}", 0..20usize).prop_map(|(invariant, header_block)| {
            VcKind::LoopInvariantInitiation { invariant, header_block }
        }),
        ("[a-z_ <>=]{1,30}", 0..20usize).prop_map(|(invariant, header_block)| {
            VcKind::LoopInvariantConsecution { invariant, header_block }
        }),
        ("[a-z_ <>=]{1,30}", 0..20usize).prop_map(|(invariant, header_block)| {
            VcKind::LoopInvariantSufficiency { invariant, header_block }
        }),
        ("[a-z_]{1,15}", "[a-z_ <>=]{1,30}").prop_map(|(variable, predicate)| {
            VcKind::TypeRefinementViolation { variable, predicate }
        }),
        ("[a-z_]{1,15}", "[a-z_:]{1,20}").prop_map(|(variable, function)| {
            VcKind::FrameConditionViolation { variable, function }
        }),
    ]
}

fn arb_contract_metadata() -> impl Strategy<Value = ContractMetadata> {
    (prop::bool::ANY, prop::bool::ANY, prop::bool::ANY, prop::bool::ANY).prop_map(|(r, e, i, v)| {
        ContractMetadata {
            has_requires: r,
            has_ensures: e,
            has_invariant: i,
            has_variant: v,
            ..ContractMetadata::default()
        }
    })
}

fn arb_verification_condition() -> impl Strategy<Value = VerificationCondition> {
    (
        arb_vc_kind(),
        "[a-z:_]{1,20}",
        arb_source_span(),
        arb_formula(),
        prop::option::of(arb_contract_metadata()),
    )
        .prop_map(|(kind, function, location, formula, contract_metadata)| {
            VerificationCondition {
                kind,
                function: function.into(),
                location,
                formula,
                contract_metadata,
            }
        })
}

// ---------------------------------------------------------------------------
// Helper: compute hash for types implementing Hash
// ---------------------------------------------------------------------------

fn compute_hash<T: Hash>(value: &T) -> u64 {
    let mut hasher = DefaultHasher::new();
    value.hash(&mut hasher);
    hasher.finish()
}

// ---------------------------------------------------------------------------
// Property: JSON roundtrip for types with PartialEq
// ---------------------------------------------------------------------------

proptest! {
    #![proptest_config(ProptestConfig::with_cases(200))]

    // --- Ty ---

    #[test]
    fn ty_json_roundtrip(ty in arb_ty()) {
        let json = serde_json::to_string(&ty).expect("serialize Ty");
        let round: Ty = serde_json::from_str(&json).expect("deserialize Ty");
        prop_assert_eq!(&round, &ty);
    }

    #[test]
    fn ty_debug_nonempty(ty in arb_ty()) {
        let dbg = format!("{:?}", ty);
        prop_assert!(!dbg.is_empty());
    }

    // --- BinOp ---

    #[test]
    fn binop_json_roundtrip(op in arb_bin_op()) {
        let json = serde_json::to_string(&op).expect("serialize BinOp");
        let round: BinOp = serde_json::from_str(&json).expect("deserialize BinOp");
        prop_assert_eq!(round, op);
    }

    // --- UnOp ---

    #[test]
    fn unop_json_roundtrip(op in arb_un_op()) {
        let json = serde_json::to_string(&op).expect("serialize UnOp");
        let round: UnOp = serde_json::from_str(&json).expect("deserialize UnOp");
        prop_assert_eq!(round, op);
    }

    // --- Place ---

    #[test]
    fn place_json_roundtrip(place in arb_place()) {
        let json = serde_json::to_string(&place).expect("serialize Place");
        let round: Place = serde_json::from_str(&json).expect("deserialize Place");
        prop_assert_eq!(&round, &place);
    }

    #[test]
    fn place_hash_determinism(place in arb_place()) {
        let h1 = compute_hash(&place);
        let cloned = place.clone();
        let h2 = compute_hash(&cloned);
        prop_assert_eq!(h1, h2);
    }

    // --- Sort ---

    #[test]
    fn sort_json_roundtrip(sort in arb_sort()) {
        let json = serde_json::to_string(&sort).expect("serialize Sort");
        let round: Sort = serde_json::from_str(&json).expect("deserialize Sort");
        prop_assert_eq!(&round, &sort);
    }

    #[test]
    fn sort_hash_determinism(sort in arb_sort()) {
        let h1 = compute_hash(&sort);
        let h2 = compute_hash(&sort.clone());
        prop_assert_eq!(h1, h2);
    }

    // --- Formula ---

    #[test]
    fn formula_json_roundtrip(formula in arb_formula()) {
        let json = serde_json::to_string(&formula).expect("serialize Formula");
        let round: Formula = serde_json::from_str(&json).expect("deserialize Formula");
        prop_assert_eq!(&round, &formula);
    }

    #[test]
    fn formula_debug_nonempty(formula in arb_formula()) {
        let dbg = format!("{:?}", formula);
        prop_assert!(!dbg.is_empty());
    }

    #[test]
    fn formula_smtlib_nonempty(formula in arb_formula()) {
        let smt = formula.to_smtlib();
        prop_assert!(!smt.is_empty());
    }

    #[test]
    fn formula_children_consistent(formula in arb_formula()) {
        // children() should not panic and the count should be consistent
        // with map_children identity
        let children_count = formula.children().len();
        let mapped = formula.clone().map_children(&mut |c| c);
        let mapped_children_count = mapped.children().len();
        prop_assert_eq!(children_count, mapped_children_count);
    }

    // --- ContractKind ---

    #[test]
    fn contract_kind_json_roundtrip(kind in arb_contract_kind()) {
        let json = serde_json::to_string(&kind).expect("serialize");
        let round: ContractKind = serde_json::from_str(&json).expect("deserialize");
        prop_assert_eq!(round, kind);
    }

    #[test]
    fn contract_kind_hash_determinism(kind in arb_contract_kind()) {
        let h1 = compute_hash(&kind);
        let h2 = compute_hash(&kind);
        prop_assert_eq!(h1, h2);
    }

    #[test]
    fn contract_kind_attr_name_roundtrips(kind in arb_contract_kind()) {
        let name = kind.attr_name();
        let parsed = ContractKind::from_attr_name(name);
        prop_assert_eq!(parsed, Some(kind));
    }

    // --- ProofLevel ---

    #[test]
    fn proof_level_json_roundtrip(level in arb_proof_level()) {
        let json = serde_json::to_string(&level).expect("serialize");
        let round: ProofLevel = serde_json::from_str(&json).expect("deserialize");
        prop_assert_eq!(round, level);
    }

    #[test]
    fn proof_level_ord_consistent(a in arb_proof_level(), b in arb_proof_level()) {
        // Ord should be consistent with PartialOrd
        let cmp = a.cmp(&b);
        let partial = a.partial_cmp(&b);
        prop_assert_eq!(partial, Some(cmp));
    }

    // --- SourceSpan ---

    #[test]
    fn source_span_json_roundtrip(span in arb_source_span()) {
        let json = serde_json::to_string(&span).expect("serialize");
        let round: SourceSpan = serde_json::from_str(&json).expect("deserialize");
        prop_assert_eq!(&round, &span);
    }

    // --- VcKind ---

    #[test]
    fn vc_kind_json_roundtrip(kind in arb_vc_kind()) {
        let json = serde_json::to_string(&kind).expect("serialize VcKind");
        let round: VcKind = serde_json::from_str(&json).expect("deserialize VcKind");
        // VcKind doesn't derive PartialEq, so compare via re-serialization
        let json2 = serde_json::to_string(&round).expect("re-serialize VcKind");
        prop_assert_eq!(&json, &json2);
    }

    #[test]
    fn vc_kind_description_nonempty(kind in arb_vc_kind()) {
        let desc = kind.description();
        prop_assert!(!desc.is_empty());
    }

    #[test]
    fn vc_kind_proof_level_valid(kind in arb_vc_kind()) {
        let level = kind.proof_level();
        // All VcKinds must map to a valid ProofLevel
        prop_assert!(matches!(
            level,
            ProofLevel::L0Safety | ProofLevel::L1Functional | ProofLevel::L2Domain
        ));
    }

    #[test]
    fn vc_kind_runtime_fallback_consistent(kind in arb_vc_kind()) {
        // has_runtime_fallback(true) implies has_runtime_fallback(true) OR
        // has_runtime_fallback(false) implies has_runtime_fallback(true) is not necessarily true.
        // But has_runtime_fallback(false) should be a subset of has_runtime_fallback(true):
        // if it has fallback without overflow checks, it should also have it with.
        let without = kind.has_runtime_fallback(false);
        let with = kind.has_runtime_fallback(true);
        if without {
            prop_assert!(with, "if fallback without overflow_checks, must also with");
        }
    }

    // --- VerificationCondition ---

    #[test]
    fn verification_condition_json_roundtrip(vc in arb_verification_condition()) {
        let json = serde_json::to_string(&vc).expect("serialize VC");
        let round: VerificationCondition = serde_json::from_str(&json).expect("deserialize VC");
        // Compare via re-serialization (VC doesn't derive PartialEq)
        let json2 = serde_json::to_string(&round).expect("re-serialize VC");
        prop_assert_eq!(&json, &json2);
    }

    #[test]
    fn verification_condition_debug_nonempty(vc in arb_verification_condition()) {
        let dbg = format!("{:?}", vc);
        prop_assert!(!dbg.is_empty());
    }

    // --- TemporalOperator ---

    #[test]
    fn temporal_operator_json_roundtrip(op in arb_temporal_operator()) {
        let json = serde_json::to_string(&op).expect("serialize");
        let round: TemporalOperator = serde_json::from_str(&json).expect("deserialize");
        prop_assert_eq!(round, op);
    }

    #[test]
    fn temporal_operator_tla_nonempty(op in arb_temporal_operator()) {
        prop_assert!(!op.tla_notation().is_empty());
    }

    // --- FairnessConstraint ---

    #[test]
    fn fairness_constraint_json_roundtrip(fc in arb_fairness_constraint()) {
        let json = serde_json::to_string(&fc).expect("serialize");
        let round: FairnessConstraint = serde_json::from_str(&json).expect("deserialize");
        prop_assert_eq!(round, fc);
    }

    #[test]
    fn fairness_constraint_description_nonempty(fc in arb_fairness_constraint()) {
        prop_assert!(!fc.description().is_empty());
    }

    #[test]
    fn fairness_constraint_tla_nonempty(fc in arb_fairness_constraint()) {
        prop_assert!(!fc.to_tla().is_empty());
    }

    // --- LivenessProperty ---

    #[test]
    fn liveness_property_json_roundtrip(prop_val in arb_liveness_property()) {
        let json = serde_json::to_string(&prop_val).expect("serialize");
        let round: LivenessProperty = serde_json::from_str(&json).expect("deserialize");
        prop_assert_eq!(round, prop_val);
    }

    #[test]
    fn liveness_property_description_nonempty(prop_val in arb_liveness_property()) {
        prop_assert!(!prop_val.description().is_empty());
    }

    #[test]
    fn liveness_property_tla_nonempty(prop_val in arb_liveness_property()) {
        prop_assert!(!prop_val.to_tla().is_empty());
    }

    // --- ContractMetadata ---

    #[test]
    fn contract_metadata_json_roundtrip(cm in arb_contract_metadata()) {
        let json = serde_json::to_string(&cm).expect("serialize");
        let round: ContractMetadata = serde_json::from_str(&json).expect("deserialize");
        prop_assert_eq!(round, cm);
    }

    #[test]
    fn contract_metadata_has_any_consistent(cm in arb_contract_metadata()) {
        let expected = cm.has_requires || cm.has_ensures || cm.has_invariant || cm.has_variant;
        prop_assert_eq!(cm.has_any(), expected);
    }
}
