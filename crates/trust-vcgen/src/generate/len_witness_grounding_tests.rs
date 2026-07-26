//! Len-witness return grounding (b62): the gate (`len_witness_credited_pairs`)
//! and the pin loop must agree, the emitted equality must be derived from the
//! MIR construction chain ONLY (never from the contract), and every
//! unresolvable shape must stay at the fail-closed SpecModelUngrounded
//! Unknown. The negative tests are the SOUNDNESS pins: an equality fact over
//! genuinely unequal-length components would be a false-PROVE of the crown
//! producer-well-formedness ensures.

use trust_types::{
    AggregateKind, BasicBlock, BlockId, BinOp, ConstValue, Contract, ContractKind, Formula,
    LocalDecl, Operand, Place, Projection, Rvalue, SourceSpan, Statement, Terminator, Ty,
    VariantDef, VcKind, VerifiableBody, VerifiableFunction,
};

use super::{generate_v2_contract_vcs_impl, parse_len_model_var};

fn i64_ty() -> Ty {
    Ty::Int { width: 64, signed: true }
}

fn usize_ty() -> Ty {
    Ty::Int { width: 64, signed: false }
}

fn vec_ty() -> Ty {
    Ty::Adt { adt_kind: None, layout: None,  faithful_enum_repr: None, name: "std::vec::Vec".into(), fields: vec![], variants: vec![], disc_index_safe: false, enum_layout: None, }
}

fn ref_vec_ty(mutable: bool) -> Ty {
    Ty::Ref { mutable, inner: Box::new(vec_ty()) }
}

/// `core::result::Result<ok_payload, i64>` in the flattened lowering shape
/// (machine tags: Ok = 0, Err = 1).
fn result_ty(ok_payload: Ty) -> Ty {
    Ty::Adt { adt_kind: None, layout: None, 
        name: "core::result::Result".into(),
        fields: vec![
            ("__tag".into(), i64_ty()),
            ("__v0_0".into(), ok_payload.clone()),
            ("__v1_0".into(), i64_ty()),
        ],
        variants: vec![
            VariantDef { name: "Ok".into(), discriminant: 0, fields: vec![("0".into(), ok_payload)] },
            VariantDef { name: "Err".into(), discriminant: 1, fields: vec![("0".into(), i64_ty())] },
        ],
        disc_index_safe: false,
        faithful_enum_repr: None, enum_layout: None, }
}

fn func_with(
    locals: Vec<LocalDecl>,
    blocks: Vec<BasicBlock>,
    arg_count: usize,
    ret_ty: Ty,
    ensures: &str,
) -> VerifiableFunction {
    VerifiableFunction {
        name: "len_pair".to_string(),
        def_path: "test::len_pair".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody { locals, blocks, arg_count, return_ty: ret_ty },
        contracts: vec![Contract {
            kind: ContractKind::Ensures,
            span: SourceSpan::default(),
            body: ensures.to_string(),
        }],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

fn assign(place: Place, rvalue: Rvalue) -> Statement {
    Statement::Assign { place, rvalue, span: SourceSpan::default() }
}

fn call(callee: &str, args: Vec<Operand>, dest: usize, target: usize) -> Terminator {
    Terminator::Call {
        func: callee.to_string(),
        args,
        dest: Place::local(dest),
        target: Some(BlockId(target)),
        span: SourceSpan::default(),
        atomic: None,
        is_foreign: false,
        is_unsafe_sig: false,
        unwind: Default::default(),
    }
}

fn field_place(local: usize, path: &[usize]) -> Place {
    Place { local, projections: path.iter().map(|&i| Projection::Field(i)).collect() }
}

fn ok_aggregate(op: Operand) -> Rvalue {
    Rvalue::Aggregate(
        AggregateKind::Adt { name: "core::result::Result".into(), variant: 0, active_field: None, args: None },
        vec![op],
    )
}

fn err_aggregate() -> Rvalue {
    Rvalue::Aggregate(
        AggregateKind::Adt { name: "core::result::Result".into(), variant: 1, active_field: None, args: None },
        vec![Operand::Constant(ConstValue::Int(1))],
    )
}

/// `<name> == <int>` pins on the AND-spine (NOT under `Not` — the negated
/// obligation contains its own `_0_discr == 0` atoms).
fn and_spine_int_pins(formula: &Formula, name: &str, out: &mut Vec<i128>) {
    match formula {
        Formula::And(cs) => {
            for c in cs {
                and_spine_int_pins(c, name, out);
            }
        }
        Formula::Eq(l, r) => {
            if let (Formula::Var(n, _), Formula::Int(v)) = (&**l, &**r)
                && n.as_str() == name
            {
                out.push(*v);
            }
        }
        _ => {}
    }
}

/// `Eq(<name>, <var>)` pins on the AND-spine: the RHS var names.
fn and_spine_var_pins(formula: &Formula, name: &str, out: &mut Vec<String>) {
    match formula {
        Formula::And(cs) => {
            for c in cs {
                and_spine_var_pins(c, name, out);
            }
        }
        Formula::Eq(l, r) => {
            if let (Formula::Var(n, _), Formula::Var(m, _)) = (&**l, &**r)
                && n.as_str() == name
            {
                out.push(m.clone());
            }
        }
        _ => {}
    }
}

fn postcondition_vcs(func: &VerifiableFunction) -> Vec<trust_types::VerificationCondition> {
    generate_v2_contract_vcs_impl(func, None)
        .into_iter()
        .filter(|vc| matches!(vc.kind, VcKind::Postcondition))
        .collect()
}

fn ungrounded_details(func: &VerifiableFunction) -> Vec<String> {
    generate_v2_contract_vcs_impl(func, None)
        .into_iter()
        .filter_map(|vc| match vc.kind {
            VcKind::UnsupportedMir { kind, detail, .. }
                if kind == crate::contracts::SPEC_MODEL_UNGROUNDED_KIND =>
            {
                Some(detail)
            }
            _ => None,
        })
        .collect()
}

const TUPLE_PAIR_ENSURES: &str =
    "!((result.is_ok()) && ((result.unwrap().0.len()) != (result.unwrap().1.len())))";

/// `fn f() -> Result<(Vec, Vec), i64>` building both tuple fields with
/// CHAIN-COUPLED pushes: `v1 = Vec::new(); v2 = Vec::new(); v1.push(7);
/// v2.push(9); Ok((v1, v2))`. `extra_v1_push` appends one more UNPAIRED
/// push to `v1` (the unequal-lengths negative).
fn paired_push_fn(extra_v1_push: bool, ensures: &str) -> VerifiableFunction {
    let payload = Ty::Tuple(vec![vec_ty(), vec_ty()]);
    let locals = vec![
        LocalDecl { index: 0, ty: result_ty(payload.clone()), name: None },
        LocalDecl { index: 1, ty: vec_ty(), name: None },
        LocalDecl { index: 2, ty: vec_ty(), name: None },
        LocalDecl { index: 3, ty: payload.clone(), name: None },
        LocalDecl { index: 4, ty: ref_vec_ty(true), name: None },
        LocalDecl { index: 5, ty: Ty::Unit, name: None },
        LocalDecl { index: 6, ty: ref_vec_ty(true), name: None },
        LocalDecl { index: 7, ty: Ty::Unit, name: None },
        LocalDecl { index: 8, ty: ref_vec_ty(true), name: None },
        LocalDecl { index: 9, ty: Ty::Unit, name: None },
    ];
    let push = "std::vec::Vec::<i64>::push";
    let mut blocks = vec![
        BasicBlock {
            id: BlockId(0),
            stmts: vec![],
            terminator: call("std::vec::Vec::<i64>::new", vec![], 1, 1),
        },
        BasicBlock {
            id: BlockId(1),
            stmts: vec![],
            terminator: call("std::vec::Vec::<i64>::new", vec![], 2, 2),
        },
        BasicBlock {
            id: BlockId(2),
            stmts: vec![assign(
                Place::local(4),
                Rvalue::Ref { mutable: true, place: Place::local(1) },
            )],
            terminator: call(
                push,
                vec![Operand::Move(Place::local(4)), Operand::Constant(ConstValue::Int(7))],
                5,
                3,
            ),
        },
        BasicBlock {
            id: BlockId(3),
            stmts: vec![assign(
                Place::local(6),
                Rvalue::Ref { mutable: true, place: Place::local(2) },
            )],
            terminator: call(
                push,
                vec![Operand::Move(Place::local(6)), Operand::Constant(ConstValue::Int(9))],
                7,
                4,
            ),
        },
    ];
    let mut next = 4usize;
    if extra_v1_push {
        blocks.push(BasicBlock {
            id: BlockId(next),
            stmts: vec![assign(
                Place::local(8),
                Rvalue::Ref { mutable: true, place: Place::local(1) },
            )],
            terminator: call(
                push,
                vec![Operand::Move(Place::local(8)), Operand::Constant(ConstValue::Int(11))],
                9,
                next + 1,
            ),
        });
        next += 1;
    }
    blocks.push(BasicBlock {
        id: BlockId(next),
        stmts: vec![
            assign(
                Place::local(3),
                Rvalue::Aggregate(
                    AggregateKind::Tuple,
                    vec![Operand::Move(Place::local(1)), Operand::Move(Place::local(2))],
                ),
            ),
            assign(Place::local(0), ok_aggregate(Operand::Move(Place::local(3)))),
        ],
        terminator: Terminator::Return,
    });
    func_with(locals, blocks, 0, result_ty(payload), ensures)
}

#[test]
fn len_model_var_parser_is_strict() {
    let v = parse_len_model_var("_0_value.0.1_len").expect("crown shape parses");
    assert_eq!(v.path, vec![0, 1]);
    assert_eq!(v.name, "_0_value.0.1_len");
    // Versioned copies parse to the BASE name.
    assert_eq!(parse_len_model_var("_0_value.2_len#s1_0").map(|v| v.name).as_deref(), Some("_0_value.2_len"));
    // Bare-payload length, non-numeric segments, other bases: fail closed.
    assert!(parse_len_model_var("_0_value_len").is_none());
    assert!(parse_len_model_var("_0_value.a_len").is_none());
    assert!(parse_len_model_var("_0_value._len").is_none());
    assert!(parse_len_model_var("_0_discr").is_none());
    assert!(parse_len_model_var("xs_len").is_none());
}

#[test]
fn paired_pushes_ground_both_lens_and_their_equality() {
    // Same-chain construction: both tuple fields pushed once, back-to-back
    // — lengths equal by construction. The pair is credited (no ungrounded
    // row), the ONE return path's VC pins `_0_discr == 1` and the equality
    // `_0_value.0_len == _0_value.1_len`.
    let func = paired_push_fn(false, TUPLE_PAIR_ENSURES);
    assert!(ungrounded_details(&func).is_empty(), "pair must be credited");
    let vcs = postcondition_vcs(&func);
    assert_eq!(vcs.len(), 1, "one return path -> one body-aware VC: {vcs:#?}");
    let mut discr = Vec::new();
    and_spine_int_pins(&vcs[0].formula, "_0_discr", &mut discr);
    assert_eq!(discr, vec![1], "{:#?}", vcs[0].formula);
    let mut eqs = Vec::new();
    and_spine_var_pins(&vcs[0].formula, "_0_value.0_len", &mut eqs);
    assert!(
        eqs.contains(&"_0_value.1_len".to_string()),
        "equality pin between the two len terms must be conjoined: {:#?}",
        vcs[0].formula
    );
}

#[test]
fn unpaired_pushes_stay_fail_closed_no_equality_fact() {
    // SOUNDNESS PIN: v1 is pushed twice, v2 once — the returned lengths are
    // GENUINELY UNEQUAL (2 vs 1), so an equality fact would false-PROVE the
    // ensures. The pair must stay uncredited: no refutable Postcondition VC,
    // one SpecModelUngrounded row naming both len terms (and not the
    // groundable `_0_discr`).
    let func = paired_push_fn(true, TUPLE_PAIR_ENSURES);
    assert!(
        postcondition_vcs(&func).is_empty(),
        "unpaired pushes must not emit a refutable Postcondition VC"
    );
    let details = ungrounded_details(&func);
    assert_eq!(details.len(), 1, "{details:#?}");
    assert!(
        details[0].contains("_0_value.0_len")
            && details[0].contains("_0_value.1_len")
            && !details[0].contains("_0_discr"),
        "both len terms fail closed: {}",
        details[0]
    );
}

#[test]
fn second_return_path_without_construction_blocks_grounding() {
    // EVERY-RETURN-PATH discipline: path A is the fully paired construction,
    // path B returns `Ok(param)` — a payload whose components trace to no
    // in-body construction. ONE unresolvable payload path fails the whole
    // pair closed (else the equality fact would over-claim about path B).
    let payload = Ty::Tuple(vec![vec_ty(), vec_ty()]);
    let push = "std::vec::Vec::<i64>::push";
    let locals = vec![
        LocalDecl { index: 0, ty: result_ty(payload.clone()), name: None },
        LocalDecl { index: 1, ty: i64_ty(), name: None }, // selector param
        LocalDecl { index: 2, ty: payload.clone(), name: None }, // payload param
        LocalDecl { index: 3, ty: vec_ty(), name: None },
        LocalDecl { index: 4, ty: vec_ty(), name: None },
        LocalDecl { index: 5, ty: payload.clone(), name: None },
        LocalDecl { index: 6, ty: ref_vec_ty(true), name: None },
        LocalDecl { index: 7, ty: Ty::Unit, name: None },
        LocalDecl { index: 8, ty: ref_vec_ty(true), name: None },
        LocalDecl { index: 9, ty: Ty::Unit, name: None },
    ];
    let blocks = vec![
        BasicBlock {
            id: BlockId(0),
            stmts: vec![],
            terminator: Terminator::SwitchInt {
                discr: Operand::Copy(Place::local(1)),
                targets: vec![(0, BlockId(6))],
                otherwise: BlockId(1),
                exhaustive_enum_unreachable: false,
                span: SourceSpan::default(),
            },
        },
        BasicBlock {
            id: BlockId(1),
            stmts: vec![],
            terminator: call("std::vec::Vec::<i64>::new", vec![], 3, 2),
        },
        BasicBlock {
            id: BlockId(2),
            stmts: vec![],
            terminator: call("std::vec::Vec::<i64>::new", vec![], 4, 3),
        },
        BasicBlock {
            id: BlockId(3),
            stmts: vec![assign(
                Place::local(6),
                Rvalue::Ref { mutable: true, place: Place::local(3) },
            )],
            terminator: call(
                push,
                vec![Operand::Move(Place::local(6)), Operand::Constant(ConstValue::Int(7))],
                7,
                4,
            ),
        },
        BasicBlock {
            id: BlockId(4),
            stmts: vec![assign(
                Place::local(8),
                Rvalue::Ref { mutable: true, place: Place::local(4) },
            )],
            terminator: call(
                push,
                vec![Operand::Move(Place::local(8)), Operand::Constant(ConstValue::Int(9))],
                9,
                5,
            ),
        },
        BasicBlock {
            id: BlockId(5),
            stmts: vec![
                assign(
                    Place::local(5),
                    Rvalue::Aggregate(
                        AggregateKind::Tuple,
                        vec![Operand::Move(Place::local(3)), Operand::Move(Place::local(4))],
                    ),
                ),
                assign(Place::local(0), ok_aggregate(Operand::Move(Place::local(5)))),
            ],
            terminator: Terminator::Return,
        },
        BasicBlock {
            id: BlockId(6),
            stmts: vec![assign(Place::local(0), ok_aggregate(Operand::Move(Place::local(2))))],
            terminator: Terminator::Return,
        },
    ];
    let func = func_with(locals, blocks, 2, result_ty(payload), TUPLE_PAIR_ENSURES);
    assert!(
        postcondition_vcs(&func).is_empty(),
        "a second, unresolvable payload return path must block the whole pair"
    );
    let details = ungrounded_details(&func);
    assert_eq!(details.len(), 1, "{details:#?}");
    assert!(
        details[0].contains("_0_value.0_len") && details[0].contains("_0_value.1_len"),
        "{}",
        details[0]
    );
}

/// The post-guard delegator shape the ny-side fail-closed guard produces:
///   `let c = <param>; if c.entailment.premises.len() !=
///    c.entailment.multipliers.len() { return Err(..) } Ok(c)`
/// (payload = struct { entailment: struct { premises: Vec, multipliers:
/// Vec } } — component paths `.0.0` / `.0.1`).
fn guarded_delegator_fn(mutate_before_ok: bool) -> VerifiableFunction {
    let ent_ty = Ty::Adt { adt_kind: None, layout: None, 
        name: "ny::Entailment".into(),
        fields: vec![("premises".into(), vec_ty()), ("multipliers".into(), vec_ty())],
        variants: vec![],
        disc_index_safe: false,
        faithful_enum_repr: None, enum_layout: None, };
    let cert_ty = Ty::Adt { adt_kind: None, layout: None,
        name: "ny::CertifiedDeep".into(),
        fields: vec![("entailment".into(), ent_ty)],
        variants: vec![],
        disc_index_safe: false,
        faithful_enum_repr: None, enum_layout: None, };
    let locals = vec![
        LocalDecl { index: 0, ty: result_ty(cert_ty.clone()), name: None },
        LocalDecl { index: 1, ty: cert_ty.clone(), name: None }, // param c
        LocalDecl { index: 2, ty: ref_vec_ty(false), name: None },
        LocalDecl { index: 3, ty: usize_ty(), name: None }, // premises len
        LocalDecl { index: 4, ty: ref_vec_ty(false), name: None },
        LocalDecl { index: 5, ty: usize_ty(), name: None }, // multipliers len
        LocalDecl { index: 6, ty: Ty::Bool, name: None },
    ];
    let len = "std::vec::Vec::<i64>::len";
    let mut ok_stmts = Vec::new();
    if mutate_before_ok {
        // A projected write into the payload AFTER the guard checked the
        // lengths: the guard's snapshot no longer describes the returned
        // value — the lane must fail closed.
        ok_stmts.push(assign(
            field_place(1, &[0, 0]),
            Rvalue::Use(Operand::Constant(ConstValue::Int(0))),
        ));
    }
    ok_stmts.push(assign(Place::local(0), ok_aggregate(Operand::Move(Place::local(1)))));
    let blocks = vec![
        BasicBlock {
            id: BlockId(0),
            stmts: vec![assign(
                Place::local(2),
                Rvalue::Ref { mutable: false, place: field_place(1, &[0, 0]) },
            )],
            terminator: call(len, vec![Operand::Move(Place::local(2))], 3, 1),
        },
        BasicBlock {
            id: BlockId(1),
            stmts: vec![assign(
                Place::local(4),
                Rvalue::Ref { mutable: false, place: field_place(1, &[0, 1]) },
            )],
            terminator: call(len, vec![Operand::Move(Place::local(4))], 5, 2),
        },
        BasicBlock {
            id: BlockId(2),
            stmts: vec![assign(
                Place::local(6),
                Rvalue::BinaryOp(
                    BinOp::Ne,
                    Operand::Copy(Place::local(3)),
                    Operand::Copy(Place::local(5)),
                ),
            )],
            terminator: Terminator::SwitchInt {
                discr: Operand::Move(Place::local(6)),
                targets: vec![(0, BlockId(3))],
                otherwise: BlockId(4),
                exhaustive_enum_unreachable: false,
                span: SourceSpan::default(),
            },
        },
        BasicBlock { id: BlockId(3), stmts: ok_stmts, terminator: Terminator::Return },
        BasicBlock {
            id: BlockId(4),
            stmts: vec![assign(Place::local(0), err_aggregate())],
            terminator: Terminator::Return,
        },
    ];
    func_with(
        locals,
        blocks,
        1,
        result_ty(cert_ty),
        "!((result.is_ok()) && ((result.unwrap().0.0.len()) != (result.unwrap().0.1.len())))",
    )
}

#[test]
fn dominating_length_guard_grounds_equality_and_witness_pins() {
    // The ny-side fail-closed guard shape: the equality edge of
    // `Ne(premises.len(), multipliers.len())` dominates `Ok(c)`. The Ok
    // path's VC carries the equality AND the per-component witness pins to
    // the `Vec::len` call dests (`_3` / `_5`); the Err path pins only the
    // discr. No ungrounded row remains.
    let func = guarded_delegator_fn(false);
    assert!(ungrounded_details(&func).is_empty(), "pair must be credited");
    let vcs = postcondition_vcs(&func);
    assert_eq!(vcs.len(), 2, "Ok + Err return paths: {vcs:#?}");
    let ok_vc = vcs
        .iter()
        .find(|vc| {
            let mut discr = Vec::new();
            and_spine_int_pins(&vc.formula, "_0_discr", &mut discr);
            discr == vec![1]
        })
        .expect("the Ok path VC pins _0_discr == 1");
    let mut a_pins = Vec::new();
    and_spine_var_pins(&ok_vc.formula, "_0_value.0.0_len", &mut a_pins);
    assert!(
        a_pins.contains(&"_0_value.0.1_len".to_string()),
        "equality pin missing: {:#?}",
        ok_vc.formula
    );
    assert!(
        a_pins.contains(&"_3".to_string()),
        "premises-len witness pin (guard len dest) missing: {:#?}",
        ok_vc.formula
    );
    let mut b_pins = Vec::new();
    and_spine_var_pins(&ok_vc.formula, "_0_value.0.1_len", &mut b_pins);
    assert!(
        b_pins.contains(&"_5".to_string()),
        "multipliers-len witness pin missing: {:#?}",
        ok_vc.formula
    );
}

#[test]
fn payload_mutation_after_guard_stays_fail_closed() {
    // SOUNDNESS PIN (temporal validity): the guard proved the lengths equal,
    // but the payload component is written BEFORE `Ok(c)` — the returned
    // value's lengths may differ from the guard's snapshot, so the lane must
    // emit NOTHING (stability gate: `place_source_is_stable` on the payload
    // source fails on the projected write).
    let func = guarded_delegator_fn(true);
    assert!(
        postcondition_vcs(&func).is_empty(),
        "a mutated payload source must not reach the refutable lane"
    );
    let details = ungrounded_details(&func);
    assert_eq!(details.len(), 1, "{details:#?}");
    assert!(
        details[0].contains("_0_value.0.0_len") && details[0].contains("_0_value.0.1_len"),
        "{}",
        details[0]
    );
}

/// The REAL extracted MIR of the ny extract-then-guard wrapper (probe
/// `p8_extract_then_guard` without the explicit drop — `-Ztrust-dump=mir:<dir>`
/// ground truth, b62 len-witness diagnosis):
///   `let c = match inner(..) { Ok(c) => c, Err(e) => return Err(e) };
///    if c.entailment.premises.len() != c.entailment.multipliers.len() {
///        return Err(..); }
///    Ok(c)`
/// Three return paths into the stmt-less Return block bb10:
///   bb3 (extract-Err): `_10 = Err(..); _0 = move _10; goto bb10`
///   bb8 (guard-Err):   `_16 = Err(..); _0 = move _16; Drop(_5) -> bb10`
///   bb9 (Ok):          `_20 = move _5; _4 = Ok(move _20); _0 = move _4`
/// The guard's `Vec::len` calls borrow `_5.0.0`/`_5.0.1`, while the Ok
/// aggregate's operand is the whole-value ALIAS `_20 = move _5` (itself fed
/// by `_8 = move (_2 as Ok).0`) — the candidate unfold must follow the
/// projection-free `Use` hops (`mutate_alias_source` writes into `_5` after
/// the guard: the hop's source is then unstable and everything must stay
/// fail-closed — the returned lengths may differ from the guard snapshot).
fn extract_then_guard_wrapper_fn(mutate_alias_source: bool) -> VerifiableFunction {
    let ent_ty = Ty::Adt { adt_kind: None, layout: None, 
        name: "ny::Entailment".into(),
        fields: vec![("premises".into(), vec_ty()), ("multipliers".into(), vec_ty())],
        variants: vec![],
        disc_index_safe: false,
        faithful_enum_repr: None, enum_layout: None, };
    let cert_ty = Ty::Adt { adt_kind: None, layout: None,
        name: "ny::CertifiedDeep".into(),
        fields: vec![("entailment".into(), ent_ty)],
        variants: vec![],
        disc_index_safe: false,
        faithful_enum_repr: None, enum_layout: None, };
    let locals = vec![
        LocalDecl { index: 0, ty: result_ty(cert_ty.clone()), name: None },
        LocalDecl { index: 1, ty: i64_ty(), name: None }, // param
        LocalDecl { index: 2, ty: result_ty(cert_ty.clone()), name: None }, // inner() dest
        LocalDecl { index: 3, ty: i64_ty(), name: None }, // discriminant
        LocalDecl { index: 4, ty: result_ty(cert_ty.clone()), name: None }, // Ok temp
        LocalDecl { index: 5, ty: cert_ty.clone(), name: None }, // c
        LocalDecl { index: 8, ty: cert_ty.clone(), name: None }, // downcast move
        LocalDecl { index: 9, ty: i64_ty(), name: None }, // Err payload
        LocalDecl { index: 10, ty: result_ty(cert_ty.clone()), name: None }, // Err temp
        LocalDecl { index: 11, ty: Ty::Bool, name: None }, // Ne result
        LocalDecl { index: 12, ty: usize_ty(), name: None }, // premises len
        LocalDecl { index: 13, ty: ref_vec_ty(false), name: None },
        LocalDecl { index: 14, ty: usize_ty(), name: None }, // multipliers len
        LocalDecl { index: 15, ty: ref_vec_ty(false), name: None },
        LocalDecl { index: 16, ty: result_ty(cert_ty.clone()), name: None }, // guard-Err temp
        LocalDecl { index: 20, ty: cert_ty.clone(), name: None }, // Ok operand alias
    ];
    let len = "std::vec::Vec::<i64>::len";
    let mut ok_stmts = Vec::new();
    if mutate_alias_source {
        ok_stmts.push(assign(
            field_place(5, &[0, 0]),
            Rvalue::Use(Operand::Constant(ConstValue::Int(0))),
        ));
    }
    ok_stmts.extend([
        assign(Place::local(20), Rvalue::Use(Operand::Move(Place::local(5)))),
        assign(Place::local(4), ok_aggregate(Operand::Move(Place::local(20)))),
        assign(Place::local(0), Rvalue::Use(Operand::Move(Place::local(4)))),
    ]);
    let blocks = vec![
        BasicBlock { id: BlockId(0), stmts: vec![], terminator: call("test::inner", vec![], 2, 1) },
        BasicBlock {
            id: BlockId(1),
            stmts: vec![assign(Place::local(3), Rvalue::Discriminant(Place::local(2)))],
            terminator: Terminator::SwitchInt {
                discr: Operand::Move(Place::local(3)),
                targets: vec![(0, BlockId(4)), (1, BlockId(3))],
                otherwise: BlockId(2),
                exhaustive_enum_unreachable: false,
                span: SourceSpan::default(),
            },
        },
        BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Unreachable },
        // extract-Err path: `Err(e) => return Err(e)`.
        BasicBlock {
            id: BlockId(3),
            stmts: vec![
                assign(
                    Place::local(9),
                    Rvalue::Use(Operand::Move(Place {
                        local: 2,
                        projections: vec![Projection::Downcast(1), Projection::Field(0)],
                    })),
                ),
                assign(Place::local(10), err_aggregate()),
                assign(Place::local(0), Rvalue::Use(Operand::Move(Place::local(10)))),
            ],
            terminator: Terminator::Goto(BlockId(10)),
        },
        // Ok extract + first len call.
        BasicBlock {
            id: BlockId(4),
            stmts: vec![
                assign(
                    Place::local(8),
                    Rvalue::Use(Operand::Move(Place {
                        local: 2,
                        projections: vec![Projection::Downcast(0), Projection::Field(0)],
                    })),
                ),
                assign(Place::local(5), Rvalue::Use(Operand::Move(Place::local(8)))),
                assign(
                    Place::local(13),
                    Rvalue::Ref { mutable: false, place: field_place(5, &[0, 0]) },
                ),
            ],
            terminator: call(len, vec![Operand::Move(Place::local(13))], 12, 5),
        },
        BasicBlock {
            id: BlockId(5),
            stmts: vec![assign(
                Place::local(15),
                Rvalue::Ref { mutable: false, place: field_place(5, &[0, 1]) },
            )],
            terminator: call(len, vec![Operand::Move(Place::local(15))], 14, 6),
        },
        BasicBlock {
            id: BlockId(6),
            stmts: vec![assign(
                Place::local(11),
                Rvalue::BinaryOp(
                    BinOp::Ne,
                    Operand::Move(Place::local(12)),
                    Operand::Move(Place::local(14)),
                ),
            )],
            terminator: Terminator::SwitchInt {
                discr: Operand::Move(Place::local(11)),
                targets: vec![(0, BlockId(9))],
                otherwise: BlockId(7),
                exhaustive_enum_unreachable: false,
                span: SourceSpan::default(),
            },
        },
        BasicBlock { id: BlockId(7), stmts: vec![], terminator: Terminator::Goto(BlockId(8)) },
        // guard-Err path: `_0` assigned, then the scheduled Drop of `c`
        // targets the Return block DIRECTLY (the p8b probe MIR).
        BasicBlock {
            id: BlockId(8),
            stmts: vec![
                assign(Place::local(16), err_aggregate()),
                assign(Place::local(0), Rvalue::Use(Operand::Move(Place::local(16)))),
            ],
            terminator: Terminator::Drop {
                place: Place::local(5),
                target: BlockId(10),
                span: SourceSpan::default(),
                unwind: Default::default(),
            },
        },
        BasicBlock { id: BlockId(9), stmts: ok_stmts, terminator: Terminator::Goto(BlockId(10)) },
        BasicBlock { id: BlockId(10), stmts: vec![], terminator: Terminator::Return },
    ];
    func_with(
        locals,
        blocks,
        1,
        result_ty(cert_ty),
        "!((result.is_ok()) && ((result.unwrap().0.0.len()) != (result.unwrap().0.1.len())))",
    )
}

#[test]
fn use_hop_wrapper_grounds_equality_and_witness_pins() {
    // The ny extract-then-guard wrapper (real extracted probe MIR): the Ok
    // aggregate's operand reaches the guard's borrowed root only through
    // projection-free whole-value `Use` hops (`_20 = move _5`). The pair is
    // credited, all THREE return paths yield VCs (including the guard-Err
    // path whose pred reaches Return via a Drop terminator), the Ok VC pins
    // the equality plus both `Vec::len`-dest witnesses, and the Err VCs pin
    // `_0_discr == 0`.
    let func = extract_then_guard_wrapper_fn(false);
    assert!(ungrounded_details(&func).is_empty(), "pair must be credited");
    let vcs = postcondition_vcs(&func);
    assert_eq!(vcs.len(), 3, "extract-Err + guard-Err + Ok paths: {vcs:#?}");
    let mut discr_pins = Vec::new();
    for vc in &vcs {
        let mut discr = Vec::new();
        and_spine_int_pins(&vc.formula, "_0_discr", &mut discr);
        assert_eq!(discr.len(), 1, "one discr pin per path: {:#?}", vc.formula);
        discr_pins.push(discr[0]);
    }
    discr_pins.sort_unstable();
    assert_eq!(discr_pins, vec![0, 0, 1], "two Err paths + one Ok path");
    let ok_vc = vcs
        .iter()
        .find(|vc| {
            let mut discr = Vec::new();
            and_spine_int_pins(&vc.formula, "_0_discr", &mut discr);
            discr == vec![1]
        })
        .expect("the Ok path VC pins _0_discr == 1");
    let mut a_pins = Vec::new();
    and_spine_var_pins(&ok_vc.formula, "_0_value.0.0_len", &mut a_pins);
    assert!(
        a_pins.contains(&"_0_value.0.1_len".to_string()),
        "equality pin missing: {:#?}",
        ok_vc.formula
    );
    assert!(
        a_pins.contains(&"_12".to_string()),
        "premises-len witness pin (guard len dest) missing: {:#?}",
        ok_vc.formula
    );
    let mut b_pins = Vec::new();
    and_spine_var_pins(&ok_vc.formula, "_0_value.0.1_len", &mut b_pins);
    assert!(
        b_pins.contains(&"_14".to_string()),
        "multipliers-len witness pin missing: {:#?}",
        ok_vc.formula
    );
}

#[test]
fn use_hop_source_mutation_stays_fail_closed() {
    // SOUNDNESS PIN (alias-hop stability): the guard checked `_5`'s lengths,
    // but `_5.0.0` is written AFTER the guard and BEFORE the `_20 = move _5`
    // alias feeding `Ok` — the returned lengths may differ from the guard's
    // snapshot. `place_source_is_stable(_5)` fails on the projected write,
    // the unfold stops at `_20` (whose places no len call borrows), and the
    // pair stays uncredited: no refutable VC, one ungrounded row naming both
    // len terms.
    let func = extract_then_guard_wrapper_fn(true);
    assert!(
        postcondition_vcs(&func).is_empty(),
        "a mutated alias source must not reach the refutable lane"
    );
    let details = ungrounded_details(&func);
    assert_eq!(details.len(), 1, "{details:#?}");
    assert!(
        details[0].contains("_0_value.0.0_len") && details[0].contains("_0_value.0.1_len"),
        "{}",
        details[0]
    );
}

/// A COMPOUND `||`-of-two-`!=` producer well-formedness ensures (the ny-cert
/// `SimplexSupportLp::certify_upper` crown shape): TWO independent length
/// pairs — `mu_plus`/`mu_minus` (payload fields `.2`/`.3`) and
/// `entailment.premises`/`entailment.multipliers` (`.4.0`/`.4.1`) — each
/// established by its OWN dominating `Ne(len, len)` guard before `Ok(c)`.
const TWO_PAIR_ENSURES: &str = "!((result.is_ok()) && \
    (((result.unwrap().2.len()) != (result.unwrap().3.len())) || \
     ((result.unwrap().4.0.len()) != (result.unwrap().4.1.len()))))";

/// The reshaped `certify_upper` delegator: `c` is the producer's returned
/// aggregate; two SEQUENTIAL, each-dominating guards check the two length
/// pairs before `Ok(c)`. With `second_guard = false` only the first pair's
/// guard is present (the second pair stays ungrounded — the soundness pin).
/// Payload = struct { bound: i64, lambda: i64, mu_plus: Vec, mu_minus: Vec,
/// entailment: struct { premises: Vec, multipliers: Vec } }.
fn two_pair_guarded_fn(second_guard: bool) -> VerifiableFunction {
    let ent_ty = Ty::Adt { adt_kind: None, layout: None, 
        name: "ny::EntailmentCertificate".into(),
        fields: vec![("premises".into(), vec_ty()), ("multipliers".into(), vec_ty())],
        variants: vec![],
        disc_index_safe: false,
        faithful_enum_repr: None, enum_layout: None, };
    let cert_ty = Ty::Adt { adt_kind: None, layout: None,
        name: "ny::SbarUpperCert".into(),
        fields: vec![
            ("bound".into(), i64_ty()),
            ("lambda".into(), i64_ty()),
            ("mu_plus".into(), vec_ty()),
            ("mu_minus".into(), vec_ty()),
            ("entailment".into(), ent_ty),
        ],
        variants: vec![],
        disc_index_safe: false,
        faithful_enum_repr: None, enum_layout: None, };
    let locals = vec![
        LocalDecl { index: 0, ty: result_ty(cert_ty.clone()), name: None },
        LocalDecl { index: 1, ty: cert_ty.clone(), name: None }, // param c
        LocalDecl { index: 2, ty: ref_vec_ty(false), name: None }, // &c.mu_plus
        LocalDecl { index: 3, ty: usize_ty(), name: None }, // mu_plus len
        LocalDecl { index: 4, ty: ref_vec_ty(false), name: None }, // &c.mu_minus
        LocalDecl { index: 5, ty: usize_ty(), name: None }, // mu_minus len
        LocalDecl { index: 6, ty: Ty::Bool, name: None }, // pair-1 Ne
        LocalDecl { index: 7, ty: ref_vec_ty(false), name: None }, // &c.premises
        LocalDecl { index: 8, ty: usize_ty(), name: None }, // premises len
        LocalDecl { index: 9, ty: ref_vec_ty(false), name: None }, // &c.multipliers
        LocalDecl { index: 10, ty: usize_ty(), name: None }, // multipliers len
        LocalDecl { index: 11, ty: Ty::Bool, name: None }, // pair-2 Ne
    ];
    let len = "std::vec::Vec::<i64>::len";
    // Pair-1 guard: `Ne(c.mu_plus.len(), c.mu_minus.len())`, equality edge to
    // bb3 (either the Ok block, or the pair-2 guard when present).
    let after_guard1 = 3usize;
    let guard1_err = if second_guard { 8 } else { 4 };
    let mut blocks = vec![
        BasicBlock {
            id: BlockId(0),
            stmts: vec![assign(
                Place::local(2),
                Rvalue::Ref { mutable: false, place: field_place(1, &[2]) },
            )],
            terminator: call(len, vec![Operand::Move(Place::local(2))], 3, 1),
        },
        BasicBlock {
            id: BlockId(1),
            stmts: vec![assign(
                Place::local(4),
                Rvalue::Ref { mutable: false, place: field_place(1, &[3]) },
            )],
            terminator: call(len, vec![Operand::Move(Place::local(4))], 5, 2),
        },
        BasicBlock {
            id: BlockId(2),
            stmts: vec![assign(
                Place::local(6),
                Rvalue::BinaryOp(
                    BinOp::Ne,
                    Operand::Copy(Place::local(3)),
                    Operand::Copy(Place::local(5)),
                ),
            )],
            terminator: Terminator::SwitchInt {
                discr: Operand::Move(Place::local(6)),
                targets: vec![(0, BlockId(after_guard1))],
                otherwise: BlockId(guard1_err),
                exhaustive_enum_unreachable: false,
                span: SourceSpan::default(),
            },
        },
    ];
    if second_guard {
        // Pair-2 guard: `Ne(c.premises.len(), c.multipliers.len())`, equality
        // edge to the Ok block bb6.
        blocks.extend([
            BasicBlock {
                id: BlockId(3),
                stmts: vec![assign(
                    Place::local(7),
                    Rvalue::Ref { mutable: false, place: field_place(1, &[4, 0]) },
                )],
                terminator: call(len, vec![Operand::Move(Place::local(7))], 8, 4),
            },
            BasicBlock {
                id: BlockId(4),
                stmts: vec![assign(
                    Place::local(9),
                    Rvalue::Ref { mutable: false, place: field_place(1, &[4, 1]) },
                )],
                terminator: call(len, vec![Operand::Move(Place::local(9))], 10, 5),
            },
            BasicBlock {
                id: BlockId(5),
                stmts: vec![assign(
                    Place::local(11),
                    Rvalue::BinaryOp(
                        BinOp::Ne,
                        Operand::Copy(Place::local(8)),
                        Operand::Copy(Place::local(10)),
                    ),
                )],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Move(Place::local(11)),
                    targets: vec![(0, BlockId(6))],
                    otherwise: BlockId(7),
                    exhaustive_enum_unreachable: false,
                    span: SourceSpan::default(),
                },
            },
            BasicBlock {
                id: BlockId(6),
                stmts: vec![assign(Place::local(0), ok_aggregate(Operand::Move(Place::local(1))))],
                terminator: Terminator::Return,
            },
            BasicBlock {
                id: BlockId(7),
                stmts: vec![assign(Place::local(0), err_aggregate())],
                terminator: Terminator::Return,
            },
            BasicBlock {
                id: BlockId(8),
                stmts: vec![assign(Place::local(0), err_aggregate())],
                terminator: Terminator::Return,
            },
        ]);
    } else {
        // No pair-2 guard: bb3 is the Ok block directly, bb4 the Err block.
        blocks.extend([
            BasicBlock {
                id: BlockId(3),
                stmts: vec![assign(Place::local(0), ok_aggregate(Operand::Move(Place::local(1))))],
                terminator: Terminator::Return,
            },
            BasicBlock {
                id: BlockId(4),
                stmts: vec![assign(Place::local(0), err_aggregate())],
                terminator: Terminator::Return,
            },
        ]);
    }
    func_with(locals, blocks, 1, result_ty(cert_ty), TWO_PAIR_ENSURES)
}

#[test]
fn two_pairs_both_guards_ground_both_equalities() {
    // The COMPOUND crown shape: each of the two length pairs has its own
    // dominating `Ne` guard, so BOTH are credited (no ungrounded row). The Ok
    // path's VC pins each pair's equality AND its per-component `Vec::len`-dest
    // witnesses; both guard-Err paths pin only the discr.
    let func = two_pair_guarded_fn(true);
    assert!(ungrounded_details(&func).is_empty(), "both pairs must be credited");
    let vcs = postcondition_vcs(&func);
    assert_eq!(vcs.len(), 3, "Ok + two guard-Err return paths: {vcs:#?}");
    let ok_vc = vcs
        .iter()
        .find(|vc| {
            let mut discr = Vec::new();
            and_spine_int_pins(&vc.formula, "_0_discr", &mut discr);
            discr == vec![1]
        })
        .expect("the Ok path VC pins _0_discr == 1");
    // Pair 1: mu_plus (.2) / mu_minus (.3).
    let mut p1 = Vec::new();
    and_spine_var_pins(&ok_vc.formula, "_0_value.2_len", &mut p1);
    assert!(
        p1.contains(&"_0_value.3_len".to_string()),
        "pair-1 equality pin missing: {:#?}",
        ok_vc.formula
    );
    assert!(
        p1.contains(&"_3".to_string()),
        "pair-1 mu_plus-len witness pin (guard len dest) missing: {:#?}",
        ok_vc.formula
    );
    // Pair 2: entailment.premises (.4.0) / entailment.multipliers (.4.1).
    let mut p2 = Vec::new();
    and_spine_var_pins(&ok_vc.formula, "_0_value.4.0_len", &mut p2);
    assert!(
        p2.contains(&"_0_value.4.1_len".to_string()),
        "pair-2 equality pin missing: {:#?}",
        ok_vc.formula
    );
    assert!(
        p2.contains(&"_8".to_string()),
        "pair-2 premises-len witness pin (guard len dest) missing: {:#?}",
        ok_vc.formula
    );
}

#[test]
fn two_pairs_one_guard_leaves_the_other_ungrounded() {
    // SOUNDNESS PIN: only pair 1 has a dominating guard; pair 2's components
    // (`c.4.0`/`c.4.1`) come from the unconstrained param, so NO body fact
    // grounds their lengths. Crediting pair 1 must NOT leak a ground for pair
    // 2 — the whole compound post stays fail-closed, with ONE ungrounded row
    // naming ONLY pair 2's terms (pair 1's are credited/removed).
    let func = two_pair_guarded_fn(false);
    assert!(
        postcondition_vcs(&func).is_empty(),
        "an uncredited pair must block the whole compound post"
    );
    let details = ungrounded_details(&func);
    assert_eq!(details.len(), 1, "{details:#?}");
    assert!(
        details[0].contains("_0_value.4.0_len")
            && details[0].contains("_0_value.4.1_len")
            && !details[0].contains("_0_value.2_len")
            && !details[0].contains("_0_value.3_len"),
        "only the unguarded pair-2 terms fail closed: {}",
        details[0]
    );
}

/// The REAL extracted MIR of `sbar::SimplexSupportLp::certify_upper` (dumped
/// via `-Ztrust-dump=mir:<dir>`), reproduced block-for-block. Unlike
/// `two_pair_guarded_fn` — which builds `Ok(move _cert)` from the WHOLE cert
/// param and guards its fields directly — the real wrapper DESTRUCTURES the
/// call-returned cert into named locals, guards THOSE, and REBUILDS the Ok
/// aggregate. The rebuild moves each `Vec` field through a fresh temp
/// (`_30 = move _12`), so the aggregate's field-2 operand is `_30`, one
/// whole-value move PAST the guard receiver `_12`. Structure:
///
/// ```text
/// _5 = inner();               match: Ok(cert) => _4, Err(e) => return Err
/// _12 = move _4.2 (mu_plus)   _13 = move _4.3 (mu_minus)  _14 = move _4.4 (ent)
/// guard1: Ne(len(&_12), len(&_13)) ? Err : continue        // FLAT .2/.3
/// guard2: Ne(len(&_14.0), len(&_14.1)) ? Err : continue    // NESTED .4.0/.4.1
/// _30 = move _12; _31 = move _13; _32 = move _14;
/// _29 = SbarUpperCert{ .0.._4.0, .1.._4.1, .2=move _30, .3=move _31, .4=move _32 };
/// _0 = Ok(move _29)
/// ```
///
/// The FLAT pair `.2`/`.3` resolves to the aggregate operand `_30`, which is
/// `move _12` — the guard receiver. Before the terminal-move-alias fix,
/// candidate resolution stopped at `_30` and never reached `_12`, so the
/// flat pair stayed ungrounded while the NESTED `.4.0`/`.4.1` pair (whose
/// mid-path descent already follows the same whole-value move) grounded —
/// the exact `certify_upper` asymmetry. This test pins that BOTH pairs now
/// ground on the real shape.
fn destructure_rebuild_two_pair_fn() -> VerifiableFunction {
    let ent_ty = Ty::Adt { adt_kind: None, layout: None, 
        name: "ny::EntailmentCertificate".into(),
        fields: vec![("premises".into(), vec_ty()), ("multipliers".into(), vec_ty())],
        variants: vec![],
        disc_index_safe: false,
        faithful_enum_repr: None, enum_layout: None, };
    let cert_ty = Ty::Adt { adt_kind: None, layout: None,
        name: "ny::SbarUpperCert".into(),
        fields: vec![
            ("bound".into(), i64_ty()),
            ("lambda".into(), i64_ty()),
            ("mu_plus".into(), vec_ty()),
            ("mu_minus".into(), vec_ty()),
            ("entailment".into(), ent_ty.clone()),
        ],
        variants: vec![],
        disc_index_safe: false,
        faithful_enum_repr: None, enum_layout: None, };
    let cert_agg = |ops: Vec<Operand>| {
        Rvalue::Aggregate(
            AggregateKind::Adt {
                name: "ny::SbarUpperCert".into(),
                variant: 0,
                active_field: None,
                args: None,
            },
            ops,
        )
    };
    // The `Ok`/`Err` variant downcast+field projection on the inner result.
    let downcast = |variant: usize| Place {
        local: 5,
        projections: vec![Projection::Downcast(variant), Projection::Field(0)],
    };
    // Contiguous local table (indices unused by the lane are i64 fillers).
    let f = i64_ty;
    let locals = vec![
        LocalDecl { index: 0, ty: result_ty(cert_ty.clone()), name: None }, // _0 return
        LocalDecl { index: 1, ty: f(), name: None },                        // _1 param
        LocalDecl { index: 2, ty: f(), name: None },                        // _2 filler
        LocalDecl { index: 3, ty: result_ty(cert_ty.clone()), name: None }, // _3 Ok(_29)
        LocalDecl { index: 4, ty: cert_ty.clone(), name: None },            // _4 cert (mv _7)
        LocalDecl { index: 5, ty: result_ty(cert_ty.clone()), name: None }, // _5 inner()
        LocalDecl { index: 6, ty: f(), name: None },                        // _6 discr
        LocalDecl { index: 7, ty: cert_ty.clone(), name: None },            // _7 Ok payload
        LocalDecl { index: 8, ty: f(), name: None },                        // _8 err payload
        LocalDecl { index: 9, ty: result_ty(cert_ty.clone()), name: None }, // _9 Err(_8)
        LocalDecl { index: 10, ty: f(), name: None },                       // _10 bound
        LocalDecl { index: 11, ty: f(), name: None },                       // _11 lambda
        LocalDecl { index: 12, ty: vec_ty(), name: None },                  // _12 mu_plus
        LocalDecl { index: 13, ty: vec_ty(), name: None },                  // _13 mu_minus
        LocalDecl { index: 14, ty: ent_ty.clone(), name: None },            // _14 entailment
        LocalDecl { index: 15, ty: Ty::Bool, name: None },                  // _15 Ne pair1
        LocalDecl { index: 16, ty: usize_ty(), name: None },                // _16 len mu_plus
        LocalDecl { index: 17, ty: ref_vec_ty(false), name: None },         // _17 &_12
        LocalDecl { index: 18, ty: usize_ty(), name: None },                // _18 len mu_minus
        LocalDecl { index: 19, ty: ref_vec_ty(false), name: None },         // _19 &_13
        LocalDecl { index: 20, ty: result_ty(cert_ty.clone()), name: None }, // _20 Err (pair1)
        LocalDecl { index: 21, ty: f(), name: None },                       // _21 filler
        LocalDecl { index: 22, ty: Ty::Bool, name: None },                  // _22 Ne pair2
        LocalDecl { index: 23, ty: usize_ty(), name: None },                // _23 len premises
        LocalDecl { index: 24, ty: ref_vec_ty(false), name: None },         // _24 &_14.0
        LocalDecl { index: 25, ty: usize_ty(), name: None },                // _25 len multipliers
        LocalDecl { index: 26, ty: ref_vec_ty(false), name: None },         // _26 &_14.1
        LocalDecl { index: 27, ty: result_ty(cert_ty.clone()), name: None }, // _27 Err (pair2)
        LocalDecl { index: 28, ty: f(), name: None },                       // _28 filler
        LocalDecl { index: 29, ty: cert_ty.clone(), name: None },           // _29 rebuilt cert
        LocalDecl { index: 30, ty: vec_ty(), name: None },                  // _30 mv _12
        LocalDecl { index: 31, ty: vec_ty(), name: None },                  // _31 mv _13
        LocalDecl { index: 32, ty: vec_ty(), name: None },                  // _32 mv _14
    ];
    let len = "std::vec::Vec::<i64>::len";
    let switch = |discr: usize, good: usize, bad: usize| Terminator::SwitchInt {
        discr: Operand::Move(Place::local(discr)),
        targets: vec![(0, BlockId(good))],
        otherwise: BlockId(bad),
        exhaustive_enum_unreachable: false,
        span: SourceSpan::default(),
    };
    let err_ret = |dest: usize| BasicBlock {
        id: BlockId(0),
        stmts: vec![
            assign(Place::local(dest), err_aggregate()),
            assign(Place::local(0), Rvalue::Use(Operand::Move(Place::local(dest)))),
        ],
        terminator: Terminator::Return,
    };
    let mut bb7 = err_ret(20);
    bb7.id = BlockId(7);
    let mut bb11 = err_ret(27);
    bb11.id = BlockId(11);
    let blocks = vec![
        // bb0: _5 = certify_upper_inner(_1)
        BasicBlock {
            id: BlockId(0),
            stmts: vec![],
            terminator: call("test::inner", vec![Operand::Copy(Place::local(1))], 5, 1),
        },
        // bb1: match on the inner Result's discriminant
        BasicBlock {
            id: BlockId(1),
            stmts: vec![assign(Place::local(6), Rvalue::Discriminant(Place::local(5)))],
            terminator: Terminator::SwitchInt {
                discr: Operand::Move(Place::local(6)),
                targets: vec![(0, BlockId(4)), (1, BlockId(3))],
                otherwise: BlockId(2),
                exhaustive_enum_unreachable: true,
                span: SourceSpan::default(),
            },
        },
        // bb2: unreachable
        BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Unreachable },
        // bb3: Err(e) => return Err(e)
        BasicBlock {
            id: BlockId(3),
            stmts: vec![
                assign(Place::local(8), Rvalue::Use(Operand::Move(downcast(1)))),
                assign(Place::local(9), err_aggregate()),
                assign(Place::local(0), Rvalue::Use(Operand::Move(Place::local(9)))),
            ],
            terminator: Terminator::Return,
        },
        // bb4: cert = Ok payload; destructure into _10.._14; guard-1 lhs len
        BasicBlock {
            id: BlockId(4),
            stmts: vec![
                assign(Place::local(7), Rvalue::Use(Operand::Move(downcast(0)))),
                assign(Place::local(4), Rvalue::Use(Operand::Move(Place::local(7)))),
                assign(Place::local(10), Rvalue::Use(Operand::Copy(field_place(4, &[0])))),
                assign(Place::local(11), Rvalue::Use(Operand::Copy(field_place(4, &[1])))),
                assign(Place::local(12), Rvalue::Use(Operand::Move(field_place(4, &[2])))),
                assign(Place::local(13), Rvalue::Use(Operand::Move(field_place(4, &[3])))),
                assign(Place::local(14), Rvalue::Use(Operand::Move(field_place(4, &[4])))),
                assign(
                    Place::local(17),
                    Rvalue::Ref { mutable: false, place: Place::local(12) },
                ),
            ],
            terminator: call(len, vec![Operand::Move(Place::local(17))], 16, 5),
        },
        // bb5: guard-1 rhs len
        BasicBlock {
            id: BlockId(5),
            stmts: vec![assign(
                Place::local(19),
                Rvalue::Ref { mutable: false, place: Place::local(13) },
            )],
            terminator: call(len, vec![Operand::Move(Place::local(19))], 18, 6),
        },
        // bb6: guard-1 `Ne(mu_plus.len, mu_minus.len)` — equality edge to bb8
        BasicBlock {
            id: BlockId(6),
            stmts: vec![assign(
                Place::local(15),
                Rvalue::BinaryOp(
                    BinOp::Ne,
                    Operand::Copy(Place::local(16)),
                    Operand::Copy(Place::local(18)),
                ),
            )],
            terminator: switch(15, 8, 7),
        },
        bb7,
        // bb8: guard-2 lhs len (premises = _14.0)
        BasicBlock {
            id: BlockId(8),
            stmts: vec![assign(
                Place::local(24),
                Rvalue::Ref { mutable: false, place: field_place(14, &[0]) },
            )],
            terminator: call(len, vec![Operand::Move(Place::local(24))], 23, 9),
        },
        // bb9: guard-2 rhs len (multipliers = _14.1)
        BasicBlock {
            id: BlockId(9),
            stmts: vec![assign(
                Place::local(26),
                Rvalue::Ref { mutable: false, place: field_place(14, &[1]) },
            )],
            terminator: call(len, vec![Operand::Move(Place::local(26))], 25, 10),
        },
        // bb10: guard-2 `Ne(premises.len, multipliers.len)` — equality edge to bb12
        BasicBlock {
            id: BlockId(10),
            stmts: vec![assign(
                Place::local(22),
                Rvalue::BinaryOp(
                    BinOp::Ne,
                    Operand::Copy(Place::local(23)),
                    Operand::Copy(Place::local(25)),
                ),
            )],
            terminator: switch(22, 12, 11),
        },
        bb11,
        // bb12: rebuild through fresh move-temps, then `Ok(SbarUpperCert{..})`
        BasicBlock {
            id: BlockId(12),
            stmts: vec![
                assign(Place::local(30), Rvalue::Use(Operand::Move(Place::local(12)))),
                assign(Place::local(31), Rvalue::Use(Operand::Move(Place::local(13)))),
                assign(Place::local(32), Rvalue::Use(Operand::Move(Place::local(14)))),
                assign(
                    Place::local(29),
                    cert_agg(vec![
                        Operand::Copy(Place::local(10)),
                        Operand::Copy(Place::local(11)),
                        Operand::Move(Place::local(30)),
                        Operand::Move(Place::local(31)),
                        Operand::Move(Place::local(32)),
                    ]),
                ),
                assign(Place::local(3), ok_aggregate(Operand::Move(Place::local(29)))),
                assign(Place::local(0), Rvalue::Use(Operand::Move(Place::local(3)))),
            ],
            terminator: Terminator::Return,
        },
    ];
    func_with(locals, blocks, 1, result_ty(cert_ty), TWO_PAIR_ENSURES)
}

#[test]
fn destructure_rebuild_flat_and_nested_pairs_both_ground_real_mir() {
    // Real `certify_upper` shape: the FLAT `.2`/`.3` pair must resolve
    // through the terminal `_30 = move _12` rebuild-temp to the guard
    // receiver `_12`, exactly as the NESTED `.4.0`/`.4.1` pair already does.
    let func = destructure_rebuild_two_pair_fn();
    assert!(
        ungrounded_details(&func).is_empty(),
        "both pairs must be credited on the real destructure-rebuild shape: {:#?}",
        ungrounded_details(&func)
    );
    let vcs = postcondition_vcs(&func);
    // Ok path + two guard-Err paths + the inner Err-return path.
    let ok_vc = vcs
        .iter()
        .find(|vc| {
            let mut discr = Vec::new();
            and_spine_int_pins(&vc.formula, "_0_discr", &mut discr);
            discr == vec![1]
        })
        .expect("the Ok path VC pins _0_discr == 1");
    // FLAT pair 1 (.2/.3) — the case the terminal-move-alias fix unlocks.
    let mut p1 = Vec::new();
    and_spine_var_pins(&ok_vc.formula, "_0_value.2_len", &mut p1);
    assert!(
        p1.contains(&"_0_value.3_len".to_string()),
        "flat pair-1 equality pin missing: {:#?}",
        ok_vc.formula
    );
    assert!(
        p1.contains(&"_16".to_string()),
        "flat pair-1 mu_plus-len witness pin (guard len dest _16) missing: {:#?}",
        ok_vc.formula
    );
    // NESTED pair 2 (.4.0/.4.1) — already grounded pre-fix; must still hold.
    let mut p2 = Vec::new();
    and_spine_var_pins(&ok_vc.formula, "_0_value.4.0_len", &mut p2);
    assert!(
        p2.contains(&"_0_value.4.1_len".to_string()),
        "nested pair-2 equality pin missing: {:#?}",
        ok_vc.formula
    );
    assert!(
        p2.contains(&"_23".to_string()),
        "nested pair-2 premises-len witness pin (guard len dest _23) missing: {:#?}",
        ok_vc.formula
    );
}

/// `ny::CertifiedDeep { entailment: ny::Entailment { premises: Vec,
/// multipliers: Vec } }` — payload component paths `.0.0` / `.0.1`.
fn nested_cert_ty() -> Ty {
    let ent_ty = Ty::Adt { adt_kind: None, layout: None, 
        name: "ny::Entailment".into(),
        fields: vec![("premises".into(), vec_ty()), ("multipliers".into(), vec_ty())],
        variants: vec![],
        disc_index_safe: false,
        faithful_enum_repr: None, enum_layout: None, };
    Ty::Adt { adt_kind: None, layout: None,
        name: "ny::CertifiedDeep".into(),
        fields: vec![("entailment".into(), ent_ty)],
        variants: vec![],
        disc_index_safe: false,
        faithful_enum_repr: None, enum_layout: None, }
}

const NESTED_PAIR_ENSURES: &str =
    "!((result.is_ok()) && ((result.unwrap().0.0.len()) != (result.unwrap().0.1.len())))";

/// The REAL `certify_upper` bb13 forward-return shape (b62 ROOT CAUSE): on
/// the `Err(e) => return Err(e)` arm the optimizer FORWARDS the whole inner
/// `Result` (`_0 = move _2`, `_2` the inner-call dest) instead of building a
/// fresh in-body `Err` aggregate — inner and outer share `Result<_, E>`, so
/// no wrapper aggregate is rebuilt. `resolve_enum_return_aggregate` finds no
/// in-body def there; the forward-return discriminant is instead resolved
/// via the dominating `switchInt(discriminant(_2))` Err-edge. Three return
/// paths into distinct Return blocks:
///   bb2 (extract-Err): `_0 = move _2` — the FORWARD (switch Err-edge, tag 1)
///   bb6 (Ok):          guarded `Ok(move _5)` — len pair grounds via guard
///   bb7 (guard-Err):   in-body `_0 = Err(..)`
fn forward_err_delegator_fn() -> VerifiableFunction {
    let cert_ty = nested_cert_ty();
    let downcast_ok =
        Place { local: 2, projections: vec![Projection::Downcast(0), Projection::Field(0)] };
    let locals = vec![
        LocalDecl { index: 0, ty: result_ty(cert_ty.clone()), name: None },
        LocalDecl { index: 1, ty: i64_ty(), name: None }, // param seed
        LocalDecl { index: 2, ty: result_ty(cert_ty.clone()), name: None }, // inner() dest (forwarded)
        LocalDecl { index: 3, ty: i64_ty(), name: None }, // discriminant
        LocalDecl { index: 5, ty: cert_ty.clone(), name: None }, // c (Ok payload)
        LocalDecl { index: 6, ty: ref_vec_ty(false), name: None },
        LocalDecl { index: 7, ty: usize_ty(), name: None }, // premises len
        LocalDecl { index: 8, ty: ref_vec_ty(false), name: None },
        LocalDecl { index: 9, ty: usize_ty(), name: None }, // multipliers len
        LocalDecl { index: 10, ty: Ty::Bool, name: None },
    ];
    let len = "std::vec::Vec::<i64>::len";
    let blocks = vec![
        BasicBlock {
            id: BlockId(0),
            stmts: vec![],
            terminator: call("test::inner", vec![Operand::Copy(Place::local(1))], 2, 1),
        },
        // bb1: `match inner() { .. }` — switch on the inner Result's discr.
        BasicBlock {
            id: BlockId(1),
            stmts: vec![assign(Place::local(3), Rvalue::Discriminant(Place::local(2)))],
            terminator: Terminator::SwitchInt {
                discr: Operand::Move(Place::local(3)),
                targets: vec![(0, BlockId(3)), (1, BlockId(2))],
                otherwise: BlockId(8),
                exhaustive_enum_unreachable: true,
                span: SourceSpan::default(),
            },
        },
        // bb2: extract-Err — FORWARD the whole inner Result into `_0`.
        BasicBlock {
            id: BlockId(2),
            stmts: vec![assign(Place::local(0), Rvalue::Use(Operand::Move(Place::local(2))))],
            terminator: Terminator::Return,
        },
        // bb3: Ok extract + guard lhs len.
        BasicBlock {
            id: BlockId(3),
            stmts: vec![
                assign(Place::local(5), Rvalue::Use(Operand::Move(downcast_ok))),
                assign(
                    Place::local(6),
                    Rvalue::Ref { mutable: false, place: field_place(5, &[0, 0]) },
                ),
            ],
            terminator: call(len, vec![Operand::Move(Place::local(6))], 7, 4),
        },
        BasicBlock {
            id: BlockId(4),
            stmts: vec![assign(
                Place::local(8),
                Rvalue::Ref { mutable: false, place: field_place(5, &[0, 1]) },
            )],
            terminator: call(len, vec![Operand::Move(Place::local(8))], 9, 5),
        },
        // bb5: guard `Ne(premises.len, multipliers.len)` — equality edge to bb6.
        BasicBlock {
            id: BlockId(5),
            stmts: vec![assign(
                Place::local(10),
                Rvalue::BinaryOp(
                    BinOp::Ne,
                    Operand::Copy(Place::local(7)),
                    Operand::Copy(Place::local(9)),
                ),
            )],
            terminator: Terminator::SwitchInt {
                discr: Operand::Move(Place::local(10)),
                targets: vec![(0, BlockId(6))],
                otherwise: BlockId(7),
                exhaustive_enum_unreachable: false,
                span: SourceSpan::default(),
            },
        },
        BasicBlock {
            id: BlockId(6),
            stmts: vec![assign(Place::local(0), ok_aggregate(Operand::Move(Place::local(5))))],
            terminator: Terminator::Return,
        },
        BasicBlock {
            id: BlockId(7),
            stmts: vec![assign(Place::local(0), err_aggregate())],
            terminator: Terminator::Return,
        },
        BasicBlock { id: BlockId(8), stmts: vec![], terminator: Terminator::Unreachable },
    ];
    func_with(locals, blocks, 1, result_ty(cert_ty), NESTED_PAIR_ENSURES)
}

#[test]
fn forwarded_err_return_grounds_discr_via_dominating_switch() {
    // b62 ROOT CAUSE FIX: the extract-Err arm FORWARDS the inner Result
    // whole (`_0 = move _2`), reached ONLY on the
    // `switchInt(discriminant(_2))` Err-edge (tag 1). That forward-return
    // path now grounds `_0_discr` (Err = model 0) via the dominating switch;
    // with all THREE paths grounded the len pair is credited and the post
    // reaches the refutable body-aware lane. Pre-fix the forward path failed
    // the gate (`_0_discr` UNGROUNDED for the whole fn) and the whole post
    // stayed SpecModelUngrounded (the `sbar:174` Unknown).
    let func = forward_err_delegator_fn();
    assert!(
        ungrounded_details(&func).is_empty(),
        "the forwarded-Err path must ground so the pair is credited: {:#?}",
        ungrounded_details(&func)
    );
    let vcs = postcondition_vcs(&func);
    assert_eq!(vcs.len(), 3, "forward-Err + Ok + guard-Err return paths: {vcs:#?}");
    let mut discr_pins = Vec::new();
    for vc in &vcs {
        let mut d = Vec::new();
        and_spine_int_pins(&vc.formula, "_0_discr", &mut d);
        assert_eq!(d.len(), 1, "one discr pin per path: {:#?}", vc.formula);
        discr_pins.push(d[0]);
    }
    discr_pins.sort_unstable();
    assert_eq!(discr_pins, vec![0, 0, 1], "two Err paths pin model-0, the Ok path model-1");
    // The Ok path carries the guard equality + witness pins; the two Err
    // paths (including the FORWARD) leave the Ok-payload len terms free.
    let ok_vc = vcs
        .iter()
        .find(|vc| {
            let mut d = Vec::new();
            and_spine_int_pins(&vc.formula, "_0_discr", &mut d);
            d == vec![1]
        })
        .expect("the Ok path VC pins _0_discr == 1");
    let mut a_pins = Vec::new();
    and_spine_var_pins(&ok_vc.formula, "_0_value.0.0_len", &mut a_pins);
    assert!(
        a_pins.contains(&"_0_value.0.1_len".to_string()) && a_pins.contains(&"_7".to_string()),
        "Ok path must pin the len equality + the premises-len witness (_7): {:#?}",
        ok_vc.formula
    );
}

/// SOUNDNESS PIN (no forcing switch): the inner Result is forwarded
/// UNCONDITIONALLY (`_0 = move _2`, no `match`). No dominating discriminant
/// switch forces a variant, so `_0_discr` must stay UNGROUNDED — grounding
/// it would guess the returned variant (and, if guessed Ok, leave the
/// payload len terms free-yet-refutable: a false-PROVE).
fn unconditional_forward_fn() -> VerifiableFunction {
    let cert_ty = nested_cert_ty();
    let locals = vec![
        LocalDecl { index: 0, ty: result_ty(cert_ty.clone()), name: None },
        LocalDecl { index: 1, ty: i64_ty(), name: None },
        LocalDecl { index: 2, ty: result_ty(cert_ty.clone()), name: None }, // inner() dest
    ];
    let blocks = vec![
        BasicBlock {
            id: BlockId(0),
            stmts: vec![],
            terminator: call("test::inner", vec![Operand::Copy(Place::local(1))], 2, 1),
        },
        BasicBlock {
            id: BlockId(1),
            stmts: vec![assign(Place::local(0), Rvalue::Use(Operand::Move(Place::local(2))))],
            terminator: Terminator::Return,
        },
    ];
    func_with(locals, blocks, 1, result_ty(cert_ty), NESTED_PAIR_ENSURES)
}

#[test]
fn unconditional_forward_stays_ungrounded() {
    // No switch to force the variant -> the forward stays fail-closed: no
    // refutable Postcondition VC, and the ungrounded row still names
    // `_0_discr` (proving the discr was NOT falsely grounded).
    let func = unconditional_forward_fn();
    assert!(
        postcondition_vcs(&func).is_empty(),
        "an unconditional forward must not reach the refutable lane"
    );
    let details = ungrounded_details(&func);
    assert_eq!(details.len(), 1, "{details:#?}");
    assert!(
        details[0].contains("_0_discr"),
        "the discr must stay ungrounded on an unforced forward: {}",
        details[0]
    );
}

/// SOUNDNESS PIN (never assume Ok): the forward is reached on the Ok EDGE
/// (tag 0 = the payload variant). Grounding it would leave the forwarded
/// value's payload len terms free in a refutable VC — a false-PROVE — so
/// only forced NON-payload (Err) edges ground; this Ok-edge forward stays
/// UNGROUNDED, failing the whole post closed even though the sibling Err
/// path resolves.
fn ok_edge_forward_fn() -> VerifiableFunction {
    let cert_ty = nested_cert_ty();
    let locals = vec![
        LocalDecl { index: 0, ty: result_ty(cert_ty.clone()), name: None },
        LocalDecl { index: 1, ty: i64_ty(), name: None },
        LocalDecl { index: 2, ty: result_ty(cert_ty.clone()), name: None }, // inner() dest
        LocalDecl { index: 3, ty: i64_ty(), name: None }, // discriminant
    ];
    let blocks = vec![
        BasicBlock {
            id: BlockId(0),
            stmts: vec![],
            terminator: call("test::inner", vec![Operand::Copy(Place::local(1))], 2, 1),
        },
        BasicBlock {
            id: BlockId(1),
            stmts: vec![assign(Place::local(3), Rvalue::Discriminant(Place::local(2)))],
            terminator: Terminator::SwitchInt {
                discr: Operand::Move(Place::local(3)),
                targets: vec![(0, BlockId(2))], // Ok edge (tag 0) -> the forward
                otherwise: BlockId(3),
                exhaustive_enum_unreachable: false,
                span: SourceSpan::default(),
            },
        },
        // bb2: forward on the Ok/payload edge — must stay ungrounded.
        BasicBlock {
            id: BlockId(2),
            stmts: vec![assign(Place::local(0), Rvalue::Use(Operand::Move(Place::local(2))))],
            terminator: Terminator::Return,
        },
        // bb3: in-body Err (resolves fine on its own).
        BasicBlock {
            id: BlockId(3),
            stmts: vec![assign(Place::local(0), err_aggregate())],
            terminator: Terminator::Return,
        },
    ];
    func_with(locals, blocks, 1, result_ty(cert_ty), NESTED_PAIR_ENSURES)
}

#[test]
fn ok_edge_forward_never_grounds() {
    // The forward sits on the Ok (payload) edge — the resolver refuses to
    // ground it (never assume Ok for a forwarded value), so the whole post
    // stays fail-closed with `_0_discr` ungrounded.
    let func = ok_edge_forward_fn();
    assert!(
        postcondition_vcs(&func).is_empty(),
        "an Ok-edge forward must not reach the refutable lane"
    );
    let details = ungrounded_details(&func);
    assert_eq!(details.len(), 1, "{details:#?}");
    assert!(
        details[0].contains("_0_discr"),
        "the discr must stay ungrounded on an Ok-edge forward: {}",
        details[0]
    );
}
