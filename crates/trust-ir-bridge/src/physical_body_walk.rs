//! Visit the physical type occurrences of a compatibility body without
//! serializing it or changing the original out-of-band definition evidence.
//!
//! The mapper owns recursion within a `Ty`. This walker only locates type roots
//! in the body, including types carried by projections nested inside operands.

use trust_types::{
    AggregateKind, AssertMessage, AtomicOperation, Operand, Place, Projection, Rvalue, Statement,
    Terminator, Ty, VerifiableBody,
};

pub(super) fn map_body_types(body: &mut VerifiableBody, map: &mut impl FnMut(&Ty) -> Ty) {
    for local in &mut body.locals {
        local.ty = map(&local.ty);
    }
    body.return_ty = map(&body.return_ty);
    for block in &mut body.blocks {
        for statement in &mut block.stmts {
            map_statement(statement, map);
        }
        map_terminator(&mut block.terminator, map);
    }
    // `datatype_defs` is the producer's original evidence. The physical view
    // must not rewrite it (nor round-trip it through serde, which drops auth).
}

pub(super) fn any_body_type(body: &VerifiableBody, pred: &mut impl FnMut(&Ty) -> bool) -> bool {
    for local in &body.locals {
        if pred(&local.ty) {
            return true;
        }
    }
    if pred(&body.return_ty) {
        return true;
    }
    for block in &body.blocks {
        for statement in &block.stmts {
            if any_statement(statement, pred) {
                return true;
            }
        }
        if any_terminator(&block.terminator, pred) {
            return true;
        }
    }
    false
}

fn any_place(place: &Place, pred: &mut impl FnMut(&Ty) -> bool) -> bool {
    for projection in &place.projections {
        match projection {
            Projection::OpaqueCast(ty) | Projection::UnwrapUnsafeBinder(ty) => {
                if pred(ty) {
                    return true;
                }
            }
            Projection::Field(_)
            | Projection::Index(_)
            | Projection::Deref
            | Projection::Downcast(_)
            | Projection::ConstantIndex { .. }
            | Projection::Subslice { .. } => {}
            _ => {}
        }
    }
    false
}

fn any_operand(operand: &Operand, pred: &mut impl FnMut(&Ty) -> bool) -> bool {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => any_place(place, pred),
        Operand::Constant(_) | Operand::Symbolic(_) | Operand::Unsupported { .. } => false,
        _ => false,
    }
}

fn any_operands(operands: &[Operand], pred: &mut impl FnMut(&Ty) -> bool) -> bool {
    operands.iter().any(|operand| any_operand(operand, pred))
}

fn any_aggregate(kind: &AggregateKind, pred: &mut impl FnMut(&Ty) -> bool) -> bool {
    match kind {
        AggregateKind::Closure { captures, .. } => captures.iter().any(&mut *pred),
        AggregateKind::RawPtr { pointee_ty, .. } => pred(pointee_ty),
        AggregateKind::Tuple
        | AggregateKind::Array
        | AggregateKind::Adt { .. }
        | AggregateKind::Coroutine { .. }
        | AggregateKind::CoroutineClosure { .. } => false,
        _ => false,
    }
}

fn any_rvalue(rvalue: &Rvalue, pred: &mut impl FnMut(&Ty) -> bool) -> bool {
    match rvalue {
        Rvalue::Use(operand) | Rvalue::UnaryOp(_, operand) | Rvalue::Repeat(operand, _) => {
            any_operand(operand, pred)
        }
        Rvalue::BinaryOp(_, left, right)
        | Rvalue::CheckedBinaryOp(_, left, right)
        | Rvalue::UncheckedBinaryOp(_, left, right)
        | Rvalue::PtrOffset { ptr: left, count: right } => {
            any_operand(left, pred) || any_operand(right, pred)
        }
        Rvalue::Ref { place, .. }
        | Rvalue::Discriminant(place)
        | Rvalue::Len(place)
        | Rvalue::AddressOf(_, place)
        | Rvalue::CopyForDeref(place) => any_place(place, pred),
        Rvalue::Cast(operand, ty) => any_operand(operand, pred) || pred(ty),
        Rvalue::Aggregate(kind, operands) => {
            any_aggregate(kind, pred) || any_operands(operands, pred)
        }
        Rvalue::Unsupported { operands, .. } => any_operands(operands, pred),
        _ => false,
    }
}

fn any_statement(statement: &Statement, pred: &mut impl FnMut(&Ty) -> bool) -> bool {
    match statement {
        Statement::Assign { place, rvalue, .. } => {
            any_place(place, pred) || any_rvalue(rvalue, pred)
        }
        Statement::SetDiscriminant { place, .. }
        | Statement::Deinit { place }
        | Statement::Retag { place }
        | Statement::PlaceMention(place) => any_place(place, pred),
        Statement::Intrinsic { args, .. } => any_operands(args, pred),
        Statement::CopyNonOverlapping { src, dst, count, elem_ty, .. } => {
            any_operand(src, pred)
                || any_operand(dst, pred)
                || any_operand(count, pred)
                || pred(elem_ty)
        }
        Statement::Unsupported { operands, .. } => any_operands(operands, pred),
        Statement::StorageLive(_)
        | Statement::StorageDead(_)
        | Statement::Coverage
        | Statement::ConstEvalCounter
        | Statement::Nop => false,
        _ => false,
    }
}

fn any_atomic(operation: &AtomicOperation, pred: &mut impl FnMut(&Ty) -> bool) -> bool {
    any_place(&operation.place, pred)
        || operation.dest.as_ref().is_some_and(|place| any_place(place, pred))
}

fn any_assert_message(message: &AssertMessage, _pred: &mut impl FnMut(&Ty) -> bool) -> bool {
    match message {
        AssertMessage::BoundsCheck
        | AssertMessage::Overflow(_)
        | AssertMessage::OverflowNeg
        | AssertMessage::DivisionByZero
        | AssertMessage::RemainderByZero
        | AssertMessage::ResumedAfterReturn
        | AssertMessage::ResumedAfterPanic
        | AssertMessage::ResumedAfterDrop
        | AssertMessage::MisalignedPointerDereference
        | AssertMessage::NullPointerDereference
        | AssertMessage::InvalidEnumConstruction
        | AssertMessage::Custom(_) => false,
        _ => false,
    }
}

fn any_terminator(terminator: &Terminator, pred: &mut impl FnMut(&Ty) -> bool) -> bool {
    match terminator {
        Terminator::SwitchInt { discr, .. } => any_operand(discr, pred),
        Terminator::Call { args, dest, atomic, .. } => {
            any_operands(args, pred)
                || any_place(dest, pred)
                || atomic.as_ref().is_some_and(|operation| any_atomic(operation, pred))
        }
        Terminator::TailCall { args, atomic, .. } => {
            any_operands(args, pred)
                || atomic.as_ref().is_some_and(|operation| any_atomic(operation, pred))
        }
        Terminator::Assert { cond, msg, .. } => {
            any_operand(cond, pred) || any_assert_message(msg, pred)
        }
        Terminator::Drop { place, .. } => any_place(place, pred),
        Terminator::Goto(_)
        | Terminator::Return
        | Terminator::Opaque { .. }
        | Terminator::Unreachable
        | Terminator::Resume => false,
        _ => false,
    }
}

fn map_place(place: &mut Place, map: &mut impl FnMut(&Ty) -> Ty) {
    for projection in &mut place.projections {
        match projection {
            Projection::OpaqueCast(ty) | Projection::UnwrapUnsafeBinder(ty) => {
                *ty = map(ty);
            }
            Projection::Field(_)
            | Projection::Index(_)
            | Projection::Deref
            | Projection::Downcast(_)
            | Projection::ConstantIndex { .. }
            | Projection::Subslice { .. } => {}
            // Future non-exhaustive variants retain their original evidence.
            _ => {}
        }
    }
}

fn map_operand(operand: &mut Operand, map: &mut impl FnMut(&Ty) -> Ty) {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => map_place(place, map),
        Operand::Constant(_) | Operand::Symbolic(_) | Operand::Unsupported { .. } => {}
        _ => {}
    }
}

fn map_operands(operands: &mut [Operand], map: &mut impl FnMut(&Ty) -> Ty) {
    for operand in operands {
        map_operand(operand, map);
    }
}

fn map_aggregate(kind: &mut AggregateKind, map: &mut impl FnMut(&Ty) -> Ty) {
    match kind {
        AggregateKind::Closure { captures, .. } => {
            for ty in captures {
                *ty = map(ty);
            }
        }
        AggregateKind::RawPtr { pointee_ty, .. } => *pointee_ty = map(pointee_ty),
        AggregateKind::Tuple
        | AggregateKind::Array
        | AggregateKind::Adt { .. }
        | AggregateKind::Coroutine { .. }
        | AggregateKind::CoroutineClosure { .. } => {}
        _ => {}
    }
}

fn map_rvalue(rvalue: &mut Rvalue, map: &mut impl FnMut(&Ty) -> Ty) {
    match rvalue {
        Rvalue::Use(operand) | Rvalue::UnaryOp(_, operand) | Rvalue::Repeat(operand, _) => {
            map_operand(operand, map);
        }
        Rvalue::BinaryOp(_, left, right)
        | Rvalue::CheckedBinaryOp(_, left, right)
        | Rvalue::UncheckedBinaryOp(_, left, right)
        | Rvalue::PtrOffset { ptr: left, count: right } => {
            map_operand(left, map);
            map_operand(right, map);
        }
        Rvalue::Ref { place, .. }
        | Rvalue::Discriminant(place)
        | Rvalue::Len(place)
        | Rvalue::AddressOf(_, place)
        | Rvalue::CopyForDeref(place) => map_place(place, map),
        Rvalue::Cast(operand, ty) => {
            map_operand(operand, map);
            *ty = map(ty);
        }
        Rvalue::Aggregate(kind, operands) => {
            map_aggregate(kind, map);
            map_operands(operands, map);
        }
        Rvalue::Unsupported { operands, .. } => map_operands(operands, map),
        _ => {}
    }
}

fn map_statement(statement: &mut Statement, map: &mut impl FnMut(&Ty) -> Ty) {
    match statement {
        Statement::Assign { place, rvalue, .. } => {
            map_place(place, map);
            map_rvalue(rvalue, map);
        }
        Statement::SetDiscriminant { place, .. }
        | Statement::Deinit { place }
        | Statement::Retag { place }
        | Statement::PlaceMention(place) => map_place(place, map),
        Statement::Intrinsic { args, .. } => map_operands(args, map),
        Statement::CopyNonOverlapping { src, dst, count, elem_ty, .. } => {
            map_operand(src, map);
            map_operand(dst, map);
            map_operand(count, map);
            *elem_ty = map(elem_ty);
        }
        Statement::Unsupported { operands, .. } => map_operands(operands, map),
        Statement::StorageLive(_)
        | Statement::StorageDead(_)
        | Statement::Coverage
        | Statement::ConstEvalCounter
        | Statement::Nop => {}
        _ => {}
    }
}

fn map_atomic(operation: &mut AtomicOperation, map: &mut impl FnMut(&Ty) -> Ty) {
    map_place(&mut operation.place, map);
    if let Some(place) = &mut operation.dest {
        map_place(place, map);
    }
}

fn map_assert_message(message: &mut AssertMessage, _map: &mut impl FnMut(&Ty) -> Ty) {
    // The current assertion-message schema carries no operands or places.
    // Keep it explicitly classified beside its condition so a future schema
    // extension has one obvious traversal site.
    match message {
        AssertMessage::BoundsCheck
        | AssertMessage::Overflow(_)
        | AssertMessage::OverflowNeg
        | AssertMessage::DivisionByZero
        | AssertMessage::RemainderByZero
        | AssertMessage::ResumedAfterReturn
        | AssertMessage::ResumedAfterPanic
        | AssertMessage::ResumedAfterDrop
        | AssertMessage::MisalignedPointerDereference
        | AssertMessage::NullPointerDereference
        | AssertMessage::InvalidEnumConstruction
        | AssertMessage::Custom(_) => {}
        _ => {}
    }
}

fn map_terminator(terminator: &mut Terminator, map: &mut impl FnMut(&Ty) -> Ty) {
    match terminator {
        Terminator::SwitchInt { discr, .. } => map_operand(discr, map),
        Terminator::Call { args, dest, atomic, .. } => {
            map_operands(args, map);
            map_place(dest, map);
            if let Some(operation) = atomic {
                map_atomic(operation, map);
            }
        }
        Terminator::TailCall { args, atomic, .. } => {
            map_operands(args, map);
            if let Some(operation) = atomic {
                map_atomic(operation, map);
            }
        }
        Terminator::Assert { cond, msg, .. } => {
            map_operand(cond, map);
            map_assert_message(msg, map);
        }
        Terminator::Drop { place, .. } => map_place(place, map),
        Terminator::Goto(_)
        | Terminator::Return
        | Terminator::Opaque { .. }
        | Terminator::Unreachable
        | Terminator::Resume => {}
        _ => {}
    }
}

#[cfg(test)]
mod tests {
    use std::collections::{BTreeMap, BTreeSet};

    use trust_types::{
        AtomicOpKind, AtomicOrdering, BasicBlock, BinOp, BlockId, ClosureCallKind, ConstValue,
        LocalDecl, SourceSpan, UnOp, UnwindEdge,
    };

    use super::*;

    #[derive(Default)]
    struct Positions {
        count: usize,
    }

    impl Positions {
        fn ty(&mut self) -> Ty {
            let name = format!("physical-position-{}", self.count);
            self.count += 1;
            Ty::Datatype { name, variants: vec![] }
        }

        fn place(&mut self) -> Place {
            Place {
                local: 17,
                projections: vec![
                    Projection::OpaqueCast(self.ty()),
                    Projection::UnwrapUnsafeBinder(self.ty()),
                    Projection::Deref,
                    Projection::Downcast(3),
                    Projection::Field(4),
                    Projection::Index(5),
                    Projection::ConstantIndex { offset: 1, min_length: 4, from_end: false },
                    Projection::Subslice { from: 1, to: 2, from_end: true },
                ],
            }
        }

        fn copy(&mut self) -> Operand {
            Operand::Copy(self.place())
        }

        fn moved(&mut self) -> Operand {
            Operand::Move(self.place())
        }

        fn atomic(&mut self) -> AtomicOperation {
            AtomicOperation {
                place: self.place(),
                dest: Some(self.place()),
                op_kind: AtomicOpKind::CompareExchange,
                ordering: AtomicOrdering::AcqRel,
                failure_ordering: Some(AtomicOrdering::Acquire),
                span: span(),
            }
        }
    }

    fn span() -> SourceSpan {
        SourceSpan {
            file: "physical-types.rs".to_owned(),
            line_start: 7,
            col_start: 3,
            line_end: 9,
            col_end: 12,
        }
    }

    fn fixture() -> (VerifiableBody, usize) {
        let mut positions = Positions::default();
        let mut body = VerifiableBody {
            locals: vec![LocalDecl {
                index: 17,
                ty: positions.ty(),
                name: Some("preserved-local".to_owned()),
            }],
            blocks: vec![],
            arg_count: 1,
            return_ty: positions.ty(),
            datatype_defs: BTreeMap::from([("original-evidence".to_owned(), Ty::Unit)]),
        };
        let mut rvalues = vec![
            Rvalue::Use(positions.copy()),
            Rvalue::BinaryOp(BinOp::Add, positions.copy(), positions.moved()),
            Rvalue::CheckedBinaryOp(BinOp::Sub, positions.copy(), positions.moved()),
            Rvalue::UncheckedBinaryOp(BinOp::Mul, positions.copy(), positions.moved()),
            Rvalue::UnaryOp(UnOp::Not, positions.copy()),
            Rvalue::Ref { mutable: true, place: positions.place() },
            Rvalue::Cast(positions.copy(), positions.ty()),
            Rvalue::Discriminant(positions.place()),
            Rvalue::Len(positions.place()),
            Rvalue::Repeat(positions.copy(), 13),
            Rvalue::AddressOf(false, positions.place()),
            Rvalue::CopyForDeref(positions.place()),
            Rvalue::PtrOffset { ptr: positions.copy(), count: positions.moved() },
            Rvalue::Unsupported {
                kind: "preserved-rvalue".to_owned(),
                detail: "refusal stays refused".to_owned(),
                operands: vec![positions.copy(), positions.moved()],
            },
        ];
        for kind in [
            AggregateKind::Tuple,
            AggregateKind::Array,
            AggregateKind::Adt {
                name: "preserved-adt".to_owned(),
                variant: 3,
                active_field: Some(2),
                args: Some("preserved-adt<u8>".to_owned()),
            },
            AggregateKind::Closure {
                name: "preserved-closure".to_owned(),
                captures: vec![positions.ty(), positions.ty()],
                call_kind: ClosureCallKind::FnMut,
            },
            AggregateKind::Coroutine { name: "preserved-coroutine".to_owned() },
            AggregateKind::CoroutineClosure { name: "preserved-async-closure".to_owned() },
            AggregateKind::RawPtr { pointee_ty: positions.ty(), mutable: true },
        ] {
            rvalues.push(Rvalue::Aggregate(kind, vec![positions.copy(), positions.moved()]));
        }
        let mut statements: Vec<_> = rvalues
            .into_iter()
            .map(|rvalue| Statement::Assign { place: positions.place(), rvalue, span: span() })
            .collect();
        statements.extend([
            Statement::StorageLive(17),
            Statement::StorageDead(17),
            Statement::SetDiscriminant { place: positions.place(), variant_index: 3 },
            Statement::Deinit { place: positions.place() },
            Statement::Retag { place: positions.place() },
            Statement::PlaceMention(positions.place()),
            Statement::Intrinsic {
                name: "preserved-intrinsic".to_owned(),
                args: vec![positions.copy(), positions.moved()],
            },
            Statement::CopyNonOverlapping {
                src: positions.copy(),
                dst: positions.moved(),
                count: positions.copy(),
                elem_ty: positions.ty(),
                span: span(),
            },
            Statement::Unsupported {
                kind: "preserved-statement".to_owned(),
                detail: "refusal stays refused".to_owned(),
                operands: vec![positions.copy(), positions.moved()],
                span: span(),
            },
            Statement::Coverage,
            Statement::ConstEvalCounter,
            Statement::Nop,
        ]);
        let mut terminators = vec![
            Terminator::Goto(BlockId(9)),
            Terminator::SwitchInt {
                discr: positions.copy(),
                targets: vec![(42, BlockId(4))],
                otherwise: BlockId(6),
                exhaustive_enum_unreachable: true,
                span: span(),
            },
            Terminator::Return,
            Terminator::Call {
                func: "preserved-call".to_owned(),
                args: vec![positions.copy(), positions.moved()],
                dest: positions.place(),
                target: Some(BlockId(6)),
                span: span(),
                atomic: Some(positions.atomic()),
                is_foreign: true,
                is_unsafe_sig: true,
                unwind: UnwindEdge::Cleanup(BlockId(8)),
                callee_identity: None,
                callee_key: None,
            },
            Terminator::TailCall {
                func: "preserved-tail-call".to_owned(),
                args: vec![positions.copy(), positions.moved()],
                span: span(),
                atomic: Some(positions.atomic()),
                is_foreign: true,
                is_unsafe_sig: true,
                callee_identity: None,
                callee_key: None,
            },
            Terminator::Drop {
                place: positions.place(),
                target: BlockId(5),
                span: span(),
                unwind: UnwindEdge::Cleanup(BlockId(8)),
            },
            Terminator::Opaque {
                kind: "preserved-terminator".to_owned(),
                targets: vec![BlockId(4), BlockId(5)],
                span: span(),
            },
            Terminator::Unreachable,
            Terminator::Resume,
        ];
        for msg in [
            AssertMessage::BoundsCheck,
            AssertMessage::Overflow(BinOp::Add),
            AssertMessage::OverflowNeg,
            AssertMessage::DivisionByZero,
            AssertMessage::RemainderByZero,
            AssertMessage::ResumedAfterReturn,
            AssertMessage::ResumedAfterPanic,
            AssertMessage::ResumedAfterDrop,
            AssertMessage::MisalignedPointerDereference,
            AssertMessage::NullPointerDereference,
            AssertMessage::InvalidEnumConstruction,
            AssertMessage::Custom("preserved-message".to_owned()),
        ] {
            terminators.push(Terminator::Assert {
                cond: positions.copy(),
                expected: false,
                msg,
                target: BlockId(2),
                span: span(),
                unwind: UnwindEdge::Cleanup(BlockId(8)),
            });
        }
        body.blocks = terminators
            .into_iter()
            .enumerate()
            .map(|(index, terminator)| BasicBlock {
                id: BlockId(index),
                stmts: if index == 0 { std::mem::take(&mut statements) } else { vec![] },
                terminator,
            })
            .collect();
        (body, positions.count)
    }

    #[test]
    fn reaches_all_physical_type_roots_once_and_preserves_definition_evidence() {
        let (mut body, count) = fixture();
        let definitions = body.datatype_defs.clone();
        let mut seen = BTreeSet::new();
        map_body_types(&mut body, &mut |ty| {
            let Ty::Datatype { name, variants } = ty else {
                panic!("unexpected mapped type root: {ty:?}");
            };
            assert!(variants.is_empty());
            assert!(seen.insert(name.clone()), "type root visited twice: {name}");
            Ty::Bool
        });
        assert_eq!(seen, (0..count).map(|index| format!("physical-position-{index}")).collect());
        assert_eq!(body.datatype_defs, definitions);
        let mut visits_after = 0;
        map_body_types(&mut body, &mut |ty| {
            assert_eq!(*ty, Ty::Bool);
            visits_after += 1;
            ty.clone()
        });
        assert_eq!(visits_after, count);
    }

    #[test]
    fn identity_mapping_preserves_non_type_body_evidence() {
        let (mut body, _) = fixture();
        let before = format!("{body:?}");
        map_body_types(&mut body, &mut Clone::clone);
        assert_eq!(format!("{body:?}"), before);
    }

    #[test]
    fn mapper_owns_recursion_inside_each_type_root() {
        let mut body = VerifiableBody {
            locals: vec![LocalDecl {
                index: 0,
                ty: Ty::Tuple(vec![Ty::Bool, Ty::Tuple(vec![Ty::Unit])]),
                name: None,
            }],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Use(Operand::Constant(ConstValue::Unit)),
                    span: span(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 0,
            return_ty: Ty::Unit,
            datatype_defs: BTreeMap::new(),
        };
        let mut visited = vec![];
        map_body_types(&mut body, &mut |ty| {
            visited.push(ty.clone());
            ty.clone()
        });
        assert_eq!(visited, vec![body.locals[0].ty.clone(), Ty::Unit]);
    }

    #[test]
    fn wave489_any_body_type_visits_identical_roots_and_short_circuits() {
        let (mut mapped_body, count) = fixture();
        let mut mapped_order = Vec::with_capacity(count);
        map_body_types(&mut mapped_body, &mut |ty| {
            mapped_order.push(ty.clone());
            ty.clone()
        });
        let (scan_body, _) = fixture();
        let mut scanned_order = Vec::with_capacity(count);
        assert!(!any_body_type(&scan_body, &mut |ty| {
            scanned_order.push(ty.clone());
            false
        }));
        assert_eq!(scanned_order, mapped_order);
        assert_eq!(scanned_order.len(), count);

        for stop_at in [0, 1, count / 2, count - 1] {
            let mut visits = 0usize;
            assert!(any_body_type(&scan_body, &mut |ty| {
                let hit = visits == stop_at && *ty == mapped_order[stop_at];
                visits += 1;
                hit
            }));
            assert_eq!(visits, stop_at + 1);
        }
    }
}
