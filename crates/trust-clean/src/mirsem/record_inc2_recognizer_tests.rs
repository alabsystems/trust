use super::*;
use trust_types::{
    BlockId, ConstValue, LocalDecl, Operand, Place, Rvalue, Statement, Terminator,
    VerifiableFunction,
};

fn load_result_dump(name: &str) -> VerifiableFunction {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("fixtures/mass-harvest2-2026-07-21/result-widths/dumps")
        .join(name);
    let bytes = std::fs::read(&path).unwrap_or_else(|e| panic!("read {name}: {e}"));
    serde_json::from_slice(&bytes).unwrap_or_else(|e| panic!("parse {name}: {e}"))
}

/// `core::result::Result::<i32, u8>::ok` — `Ok(x) => Some(x)`, `Err(_) => None`. The
/// `Some(x)` payload reads `(_1 as Ok=v#0).0` (flattened `__v0_0`).
const OK_I32_U8: &str = "trust-mir-72435068d9038db2-f7270a8ff7882b5.json";
/// `core::result::Result::<i32, u8>::err` — `Err(e) => Some(e)`, `Ok(_) => None`. The
/// `Some(e)` payload reads `(_1 as Err=v#1).0` (flattened `__v1_0`).
const ERR_I32_U8: &str = "trust-mir-e9442eae8caf2e75-5c99743ad3ed3ecd.json";

fn param_index_of(func: &VerifiableFunction) -> impl Fn(usize) -> Option<u64> + '_ {
    let arg_count = func.body.arg_count;
    move |local: usize| {
        if (1..=arg_count).contains(&local) { u64::try_from(local - 1).ok() } else { None }
    }
}

fn use_operand_of(func: &VerifiableFunction, temp: usize) -> Operand {
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            if let Statement::Assign { place, rvalue: Rvalue::Use(op), .. } = stmt
                && place.local == temp
            {
                return op.clone();
            }
        }
    }
    panic!("no `Use` definition for _{temp}");
}

/// The ladder head is the non-entry `SwitchInt` block (the epilogue's discriminant
/// re-read); the dispatch is the entry block `bb0`.
fn ladder_head_id(func: &VerifiableFunction) -> BlockId {
    func.body
        .blocks
        .iter()
        .find(|b| b.id != BlockId(0) && matches!(b.terminator, Terminator::SwitchInt { .. }))
        .map(|b| b.id)
        .expect("a drop-ladder head")
}

fn repoint_drops(func: &mut VerifiableFunction, new_local: usize) {
    for block in &mut func.body.blocks {
        if let Terminator::Drop { place, .. } = &mut block.terminator {
            place.local = new_local;
        }
    }
}

fn push_stmt_into(func: &mut VerifiableFunction, block_id: BlockId, stmt: Statement) {
    if let Some(block) = func.body.blocks.iter_mut().find(|b| b.id == block_id) {
        block.stmts.insert(0, stmt);
    }
}

// -----------------------------------------------------------------------
// Positive: the full recognizer + kernel path (gate C positive — recognized
// DESPITE the post-`Option` `Drop(self)` ladder).
// -----------------------------------------------------------------------

#[test]
fn ok_recognizes_downcast_field_then_arm_and_certifies() {
    let func = load_result_dump(OK_I32_U8);
    let shape = sem_adt_return_shape_of(&func).expect("Result::ok must recognize");
    // then = the Ok arm => `Some(payload)` via a DowncastField at the VARIANT-DISJOINT
    // flattened key 1 (`__v0_0`), NOT the within-variant index 0.
    assert_eq!(
        shape.then_arm.payload,
        Some(SemAdtPayload::DowncastField { base_param: 0, flat_key: 1, downcast_variant: 0 }),
    );
    assert_eq!(shape.else_arm.payload, None); // else = the Err arm => `None`.
    assert_eq!(
        crate::trustir_adt::check_adt_return_refinement(&shape),
        crate::trustir_anchor::RefinementVerdict::ProvenModulo3,
    );
}

#[test]
fn err_recognizes_downcast_field_else_arm_and_certifies() {
    let func = load_result_dump(ERR_I32_U8);
    let shape = sem_adt_return_shape_of(&func).expect("Result::err must recognize");
    assert_eq!(shape.then_arm.payload, None); // then = the Ok arm => `None`.
    // else = the Err arm => `Some(payload)` via a DowncastField at flattened key 2
    // (`__v1_0`) — the ELSE arm downcast (exercises the else-side expected variant).
    assert_eq!(
        shape.else_arm.payload,
        Some(SemAdtPayload::DowncastField { base_param: 0, flat_key: 2, downcast_variant: 1 }),
    );
    assert_eq!(
        crate::trustir_adt::check_adt_return_refinement(&shape),
        crate::trustir_anchor::RefinementVerdict::ProvenModulo3,
    );
}

// -----------------------------------------------------------------------
// Gate A / gate D — the DowncastField payload recognizer, isolated.
// -----------------------------------------------------------------------

#[test]
fn downcast_field_payload_honest_key_and_gate_d_provenance() {
    let func = load_result_dump(OK_I32_U8);
    let op = use_operand_of(&func, 3); // `Move((_1 as v#0).0)`
    let pidx = param_index_of(&func);
    // Gate A: the honest key is the VARIANT-DISJOINT flattened position of `__v0_0` (1).
    assert_eq!(
        downcast_field_payload(&func.body, &op, &pidx, Some(0)),
        Some(SemAdtPayload::DowncastField { base_param: 0, flat_key: 1, downcast_variant: 0 }),
    );
    // Gate D (TAG↔DOWNCAST): a MISMATCHED dispatch-established variant declines — the
    // body downcasts v#0 but the dispatch here is asserted to be v#1.
    assert_eq!(downcast_field_payload(&func.body, &op, &pidx, Some(1)), None);
    // No dispatch-established variant (a comparison / non-discriminant guard) declines.
    assert_eq!(downcast_field_payload(&func.body, &op, &pidx, None), None);
}

#[test]
fn downcast_field_payload_declines_non_flattened_dump() {
    let mut func = load_result_dump(OK_I32_U8);
    let op = use_operand_of(&func, 3);
    // Strip the flattened `__v..` field metadata (a legacy / non-flattened dump lacks
    // it). Without a flattened position there is no VARIANT-DISJOINT key: fail closed.
    if let trust_types::Ty::Adt { fields, .. } = &mut func.body.locals[1].ty {
        fields.retain(|(name, _)| !name.starts_with("__v"));
    }
    let pidx = param_index_of(&func);
    assert_eq!(downcast_field_payload(&func.body, &op, &pidx, Some(0)), None);
}

// -----------------------------------------------------------------------
// Gate B / gate C — the value-transparent drop-ladder epilogue, isolated.
// -----------------------------------------------------------------------

#[test]
fn drop_ladder_recognizes_and_pins_self_local() {
    let func = load_result_dump(OK_I32_U8);
    let head = ladder_head_id(&func);
    assert_eq!(
        recognize_drop_ladder_epilogue(&func.body, head),
        Some(DropLadderEpilogue { switch_block: head, self_local: 1 }),
    );
}

#[test]
fn drop_ladder_declines_drop_of_different_local() {
    let mut func = load_result_dump(OK_I32_U8);
    repoint_drops(&mut func, 3); // gate B(iii): Drop must be of the dispatched self.
    let head = ladder_head_id(&func);
    assert_eq!(recognize_drop_ladder_epilogue(&func.body, head), None);
    // and the whole recognizer declines — the ladder switch is no longer stripped, so
    // the guard analysis sees two switches and the conjunctive chain fails.
    assert!(sem_adt_return_shape_of(&func).is_none());
}

#[test]
fn drop_ladder_declines_extra_statement_in_head() {
    let mut func = load_result_dump(OK_I32_U8);
    let head = ladder_head_id(&func);
    // gate B(ii): the ladder head does NOTHING but read the self discriminant — a
    // spurious value statement (here a `_3` write) declines.
    push_stmt_into(
        &mut func,
        head,
        Statement::Assign {
            place: Place::local(3),
            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(0))),
            span: Default::default(),
        },
    );
    assert_eq!(recognize_drop_ladder_epilogue(&func.body, head), None);
    assert!(sem_adt_return_shape_of(&func).is_none());
}

#[test]
fn drop_ladder_declines_zero_write_in_ladder() {
    let mut func = load_result_dump(OK_I32_U8);
    let head = ladder_head_id(&func);
    // gate B(ii): a `_0` write inside the ladder region must decline. Both the ladder
    // recognizer's head-statement gate AND the whole-body `_0` single-writer gate catch
    // it; either way the recognizer fails closed.
    push_stmt_into(
        &mut func,
        head,
        Statement::Assign {
            place: Place::local(0),
            rvalue: Rvalue::Aggregate(
                trust_types::AggregateKind::Adt {
                    name: "core::option::Option".into(),
                    variant: 0,
                    active_field: None,
                },
                vec![],
            ),
            span: Default::default(),
        },
    );
    assert_eq!(recognize_drop_ladder_epilogue(&func.body, head), None);
    assert!(sem_adt_return_shape_of(&func).is_none());
}

#[test]
fn drop_ladder_declines_reread_of_different_self_local() {
    // gate B(i): the ladder must re-read the discriminant of the SAME self local the
    // dispatch read. Add a second `Result`-typed local `_5`, repoint the ladder's
    // discriminant read AND its `Drop` onto it (a self-consistent ladder over `_5`),
    // while the dispatch stays on `_1`. The self-local cross-check declines.
    let mut func = load_result_dump(OK_I32_U8);
    let self_ty = func.body.locals[1].ty.clone();
    let new_local = func.body.locals.len();
    func.body.locals.push(LocalDecl { index: new_local, ty: self_ty, name: None });
    for block in &mut func.body.blocks {
        if let Terminator::Drop { place, .. } = &mut block.terminator {
            place.local = new_local;
        }
        for stmt in &mut block.stmts {
            if let Statement::Assign { place, rvalue: Rvalue::Discriminant(src), .. } = stmt
                && place.local == 4
            {
                src.local = new_local;
            }
        }
    }
    let head = ladder_head_id(&func);
    // The ladder over `_5` IS internally well-formed …
    assert_eq!(
        recognize_drop_ladder_epilogue(&func.body, head),
        Some(DropLadderEpilogue { switch_block: head, self_local: new_local }),
    );
    // … but the dispatch is over `_1`, so the whole recognizer declines (gate B(i)).
    assert!(sem_adt_return_shape_of(&func).is_none());
}
