// trust-types/resilience/helpers: Helper functions for resilience analysis
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use crate::{BasicBlock, BlockId, Operand, Place, Rvalue, Statement, Terminator};

use super::types::{ErrorHandlingPattern, PanicKind};

/// Convert an AssertMessage to a human-readable description.
pub(in crate::resilience) fn assert_msg_description(msg: &crate::AssertMessage) -> String {
    match msg {
        crate::AssertMessage::BoundsCheck => "index out of bounds".to_string(),
        crate::AssertMessage::Overflow(op) => format!("{:?} overflow", op),
        crate::AssertMessage::OverflowNeg => "negation overflow".to_string(),
        crate::AssertMessage::DivisionByZero => "division by zero".to_string(),
        crate::AssertMessage::RemainderByZero => "remainder by zero".to_string(),
        crate::AssertMessage::ResumedAfterReturn => "resumed after return".to_string(),
        crate::AssertMessage::ResumedAfterPanic => "resumed after panic".to_string(),
        crate::AssertMessage::MisalignedPointerDereference => {
            "misaligned pointer dereference".to_string()
        }
        crate::AssertMessage::ResumedAfterDrop => "resumed after drop".to_string(),
        crate::AssertMessage::NullPointerDereference => "null pointer dereference".to_string(),
        crate::AssertMessage::InvalidEnumConstruction => "invalid enum construction".to_string(),
        crate::AssertMessage::Custom(s) => s.clone(),
    }
}

/// Detect if a function call is a panic-inducing call.
pub(in crate::resilience) fn detect_panic_call(func_path: &str) -> Option<PanicKind> {
    if func_path.contains("unwrap") && !func_path.contains("unwrap_or") {
        Some(PanicKind::Unwrap)
    } else if func_path.contains("expect") {
        Some(PanicKind::Expect)
    } else if func_path.contains("panic") {
        Some(PanicKind::ExplicitPanic)
    } else {
        None
    }
}

/// Classify how a call result is used in the target block.
pub(in crate::resilience) fn classify_error_handling(
    call_func: &str,
    call_block: BlockId,
    dest: &Place,
    target_block: &BasicBlock,
) -> ErrorHandlingPattern {
    // Check if the result is used in an unwrap call.
    if let Terminator::Call { func: next_func, args, .. } = &target_block.terminator
        && next_func.contains("unwrap")
        && !next_func.contains("unwrap_or")
    {
        let uses_dest = args
            .iter()
            .any(|arg| matches!(arg, Operand::Copy(p) | Operand::Move(p) if p.local == dest.local));
        if uses_dest {
            return ErrorHandlingPattern::Panicking {
                call_path: call_func.to_string(),
                block: call_block,
            };
        }
    }

    // Check if result is discarded (no statements reference dest local).
    let dest_used = target_block.stmts.iter().any(|stmt| stmt_references_local(stmt, dest.local));
    let dest_used_in_term = terminator_references_local(&target_block.terminator, dest.local);

    if !dest_used && !dest_used_in_term {
        return ErrorHandlingPattern::Swallowing {
            call_path: call_func.to_string(),
            block: call_block,
        };
    }

    // Default: assume propagation (safe pattern).
    ErrorHandlingPattern::Propagation { call_path: call_func.to_string(), block: call_block }
}

/// Check if a statement references a given local variable.
fn stmt_references_local(stmt: &Statement, local: usize) -> bool {
    match stmt {
        Statement::Assign { rvalue, .. } => rvalue_references_local(rvalue, local),
        // Trust: #828 — new statement variants: check place-bearing ones for local refs.
        Statement::SetDiscriminant { place, .. }
        | Statement::Deinit { place }
        | Statement::Retag { place }
        | Statement::PlaceMention(place) => place.local == local,
        Statement::Intrinsic { args, .. } => {
            args.iter().any(|op| operand_references_local(op, local))
        }
        Statement::Unsupported { operands, .. } => {
            operands.iter().any(|op| operand_references_local(op, local))
        }
        Statement::StorageLive(l) | Statement::StorageDead(l) => *l == local,
        Statement::Coverage | Statement::ConstEvalCounter | Statement::Nop => false,
    }
}

/// Check if an rvalue references a given local variable.
fn rvalue_references_local(rvalue: &Rvalue, local: usize) -> bool {
    match rvalue {
        Rvalue::Use(op) | Rvalue::Cast(op, _) | Rvalue::UnaryOp(_, op) => {
            operand_references_local(op, local)
        }
        Rvalue::BinaryOp(_, a, b) | Rvalue::CheckedBinaryOp(_, a, b) => {
            operand_references_local(a, local) || operand_references_local(b, local)
        }
        Rvalue::Ref { place, .. }
        | Rvalue::AddressOf(_, place)
        | Rvalue::Discriminant(place)
        | Rvalue::Len(place)
        | Rvalue::CopyForDeref(place) => place.local == local,
        Rvalue::Aggregate(_, ops) => ops.iter().any(|op| operand_references_local(op, local)),
        Rvalue::Repeat(op, _) => operand_references_local(op, local),
        // Trust: W2 inc-0 — pointer arithmetic references BOTH operands.
        Rvalue::PtrOffset { ptr, count } => {
            operand_references_local(ptr, local) || operand_references_local(count, local)
        }
        Rvalue::Unsupported { operands, .. } => {
            operands.iter().any(|op| operand_references_local(op, local))
        }
    }
}

/// Check if an operand references a given local variable.
fn operand_references_local(operand: &Operand, local: usize) -> bool {
    match operand {
        Operand::Copy(p) | Operand::Move(p) => p.local == local,
        Operand::Constant(_) | Operand::Symbolic(_) | Operand::Unsupported { .. } => false,
    }
}

/// Check if a terminator references a given local variable.
fn terminator_references_local(term: &Terminator, local: usize) -> bool {
    match term {
        Terminator::Call { args, .. } => {
            args.iter().any(|arg| operand_references_local(arg, local))
        }
        Terminator::SwitchInt { discr, .. } => operand_references_local(discr, local),
        Terminator::Assert { cond, .. } => operand_references_local(cond, local),
        Terminator::Drop { place, .. } => place.local == local,
        Terminator::Goto(_)
        | Terminator::Opaque { .. }
        | Terminator::Return
        | Terminator::Unreachable
        | Terminator::Resume => false,
    }
}
