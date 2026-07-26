//! Conservative E6 facet inference over a validated, closed MIR fragment.
//!
//! Facet booleans are potential proof inputs, so this lane must not infer trust
//! from diagnostic strings or malformed serialized MIR.  The current call IR
//! does not carry an exact rustc `DefId`/`Instance` and monomorphized signature.
//! Until it does, every `Call` fails all four facets closed and the external
//! authority allowlist is empty.  Composition remains available as graph
//! utilities in [`crate::facet_propagation`], but is deliberately quarantined
//! from this authority-producing entry point.
//!
//! A function is considered only after a shared validator establishes the
//! closed v1 fragment: canonical block/local identities, complete successor
//! targets, scalar/drop-free local types, well-formed places and a small typed
//! statement/rvalue subset.  `Drop`, `Opaque`, `Unreachable`, `Resume`, and all
//! calls are rejected even in unreachable blocks.  This is intentionally more
//! conservative than the individual structural analyses; it prevents their
//! differing assumptions from combining into a false all-four result.

use std::collections::{HashMap, HashSet};

use crate::structural_determinism::is_structurally_deterministic;
use crate::structural_panic_freedom::is_structurally_panic_free;
use crate::structural_purity::is_structurally_pure;
use crate::structural_termination::is_control_flow_loop_free;
use crate::{
    BinOp, ConstValue, Operand, Place, Projection, Rvalue, Statement, Terminator, Ty,
    VerifiableFunction,
};

/// Which of the four E6 facets a function is structurally known to have.
///
/// A `true` is emitted only for a unique def-path whose body passes the shared
/// closed-fragment validator.  A `false` remains conservative: a deeper,
/// context-bound lane may establish the property later.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct FacetSet {
    pub total: bool,
    pub no_panic: bool,
    pub pure: bool,
    pub deterministic: bool,
}

impl FacetSet {
    /// All four facets hold — the condition an eventual sealed E6 admission
    /// gate will require.
    #[must_use]
    pub fn all(self) -> bool {
        self.total && self.no_panic && self.pure && self.deterministic
    }
}

fn ty_in_closed_fragment(ty: &Ty) -> bool {
    match ty {
        Ty::Bool | Ty::Int { .. } | Ty::PtrSizedInt { .. } | Ty::Char | Ty::Unit => true,
        Ty::Tuple(fields) => fields.iter().all(ty_in_closed_fragment),
        _ => false,
    }
}

fn ty_is_integer(ty: &Ty) -> bool {
    matches!(ty, Ty::Int { .. } | Ty::PtrSizedInt { .. })
}

fn ty_is_comparable_scalar(ty: &Ty) -> bool {
    matches!(ty, Ty::Bool | Ty::Int { .. } | Ty::PtrSizedInt { .. } | Ty::Char | Ty::Unit)
}

fn place_ty<'a>(func: &'a VerifiableFunction, place: &Place) -> Option<&'a Ty> {
    let mut ty = &func.body.locals.get(place.local)?.ty;
    for projection in &place.projections {
        match (projection, ty) {
            (Projection::Field(field), Ty::Tuple(fields)) => ty = fields.get(*field)?,
            _ => return None,
        }
    }
    Some(ty)
}

fn unsigned_fits_width(value: u128, width: u32) -> bool {
    (1..=128).contains(&width) && (width == 128 || value < (1u128 << width))
}

fn signed_fits_width(value: i128, width: u32) -> bool {
    if width == 128 {
        return true;
    }
    if !(1..128).contains(&width) {
        return false;
    }
    let bound = 1i128 << (width - 1);
    (-bound..bound).contains(&value)
}

fn constant_matches_ty(value: &ConstValue, expected: &Ty) -> bool {
    match (value, expected) {
        (ConstValue::Bool(_), Ty::Bool) | (ConstValue::Unit, Ty::Unit) => true,
        (ConstValue::Int(value), Ty::Int { width, signed: true }) => {
            signed_fits_width(*value, *width)
        }
        (ConstValue::Uint(value, encoded_width), Ty::Int { width, signed: false }) => {
            encoded_width == width && unsigned_fits_width(*value, *width)
        }
        // Pointer-sized constants need the target width in the certificate
        // context.  This rustc-free lane has no such context, so it fails closed.
        _ => false,
    }
}

fn operand_matches_ty(func: &VerifiableFunction, operand: &Operand, expected: &Ty) -> bool {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => {
            place_ty(func, place).is_some_and(|actual| actual == expected)
        }
        Operand::Constant(value) => constant_matches_ty(value, expected),
        _ => false,
    }
}

fn operand_place_ty<'a>(func: &'a VerifiableFunction, operand: &Operand) -> Option<&'a Ty> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => place_ty(func, place),
        _ => None,
    }
}

fn operands_have_same_comparable_ty(
    func: &VerifiableFunction,
    lhs: &Operand,
    rhs: &Operand,
) -> bool {
    match (operand_place_ty(func, lhs), operand_place_ty(func, rhs)) {
        (Some(lhs_ty), Some(rhs_ty)) => lhs_ty == rhs_ty && ty_is_comparable_scalar(lhs_ty),
        (Some(lhs_ty), None) => {
            ty_is_comparable_scalar(lhs_ty) && operand_matches_ty(func, rhs, lhs_ty)
        }
        (None, Some(rhs_ty)) => {
            ty_is_comparable_scalar(rhs_ty) && operand_matches_ty(func, lhs, rhs_ty)
        }
        // With two untyped constants there is no closed carrier to bind the
        // operation to, so do not guess from literal spelling.
        (None, None) => false,
    }
}

fn rvalue_matches_ty(func: &VerifiableFunction, rvalue: &Rvalue, destination: &Ty) -> bool {
    match rvalue {
        Rvalue::Use(operand) => operand_matches_ty(func, operand, destination),
        Rvalue::UnaryOp(crate::UnOp::Not, operand)
            if matches!(destination, Ty::Bool | Ty::Int { .. } | Ty::PtrSizedInt { .. }) =>
        {
            operand_matches_ty(func, operand, destination)
        }
        Rvalue::BinaryOp(op, lhs, rhs) => match op {
            BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                *destination == Ty::Bool && operands_have_same_comparable_ty(func, lhs, rhs)
            }
            BinOp::Add
            | BinOp::Sub
            | BinOp::Mul
            | BinOp::Div
            | BinOp::Rem
            | BinOp::BitAnd
            | BinOp::BitOr
            | BinOp::BitXor
            | BinOp::Shl
            | BinOp::Shr
                if ty_is_integer(destination) =>
            {
                operand_matches_ty(func, lhs, destination)
                    && operand_matches_ty(func, rhs, destination)
            }
            _ => false,
        },
        Rvalue::CheckedBinaryOp(BinOp::Add | BinOp::Sub | BinOp::Mul, lhs, rhs) => {
            let Ty::Tuple(fields) = destination else { return false };
            let [value_ty, overflow_ty] = fields.as_slice() else { return false };
            ty_is_integer(value_ty)
                && *overflow_ty == Ty::Bool
                && operand_matches_ty(func, lhs, value_ty)
                && operand_matches_ty(func, rhs, value_ty)
        }
        _ => false,
    }
}

fn statement_is_valid(func: &VerifiableFunction, statement: &Statement) -> bool {
    match statement {
        Statement::Assign { place, rvalue, .. } => place_ty(func, place)
            .is_some_and(|destination| rvalue_matches_ty(func, rvalue, destination)),
        Statement::StorageLive(local) | Statement::StorageDead(local) => {
            *local < func.body.locals.len()
        }
        Statement::PlaceMention(place) => place_ty(func, place).is_some(),
        Statement::Coverage | Statement::ConstEvalCounter | Statement::Nop => true,
        // These constructs need effect, initializedness, borrow, intrinsic, or
        // unsupported-MIR semantics that the closed leaf lane does not carry.
        _ => false,
    }
}

fn target_exists(func: &VerifiableFunction, target: crate::BlockId) -> bool {
    target.0 < func.body.blocks.len()
        && func.body.blocks.get(target.0).is_some_and(|block| block.id == target)
}

fn switch_operand_is_valid(func: &VerifiableFunction, operand: &Operand) -> bool {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => place_ty(func, place).is_some_and(|ty| {
            matches!(ty, Ty::Bool | Ty::Int { .. } | Ty::PtrSizedInt { .. } | Ty::Char)
        }),
        Operand::Constant(ConstValue::Bool(_) | ConstValue::Int(_) | ConstValue::Uint(_, _)) => {
            true
        }
        _ => false,
    }
}

fn terminator_is_valid(func: &VerifiableFunction, terminator: &Terminator) -> bool {
    match terminator {
        Terminator::Goto(target) => target_exists(func, *target),
        Terminator::SwitchInt { discr, targets, otherwise, .. } => {
            let mut values = HashSet::new();
            switch_operand_is_valid(func, discr)
                && targets
                    .iter()
                    .all(|(value, target)| values.insert(*value) && target_exists(func, *target))
                && target_exists(func, *otherwise)
        }
        Terminator::Return => true,
        Terminator::Assert { cond, target, .. } => {
            operand_matches_ty(func, cond, &Ty::Bool) && target_exists(func, *target)
        }
        // Calls remain quarantined until exact instance/signature extraction.
        // Drop glue and opaque/exceptional leaves likewise have no complete
        // four-facet semantics in this lane.
        Terminator::Call { .. }
        | Terminator::Drop { .. }
        | Terminator::Opaque { .. }
        | Terminator::Unreachable
        | Terminator::Resume => false,
    }
}

fn is_valid_closed_leaf(func: &VerifiableFunction) -> bool {
    if func.def_path.trim().is_empty()
        || func.body.blocks.is_empty()
        || func.body.locals.is_empty()
        || func.body.arg_count >= func.body.locals.len()
        || !ty_in_closed_fragment(&func.body.return_ty)
        || func.body.locals[0].ty != func.body.return_ty
    {
        return false;
    }

    // Require the serialized identities to agree with their canonical vector
    // positions.  This simultaneously rejects duplicates, sparse IDs, a missing
    // bb0/return slot, and the map-overwrite/index-confusion class of bugs.
    if func
        .body
        .locals
        .iter()
        .enumerate()
        .any(|(index, local)| local.index != index || !ty_in_closed_fragment(&local.ty))
        || func.body.blocks.iter().enumerate().any(|(index, block)| block.id.0 != index)
    {
        return false;
    }

    func.body.blocks.iter().all(|block| {
        block.stmts.iter().all(|statement| statement_is_valid(func, statement))
            && terminator_is_valid(func, &block.terminator)
    })
}

fn has_undischarged_panic_operation(func: &VerifiableFunction) -> bool {
    func.body.blocks.iter().any(|block| {
        block.stmts.iter().any(|statement| {
            matches!(
                statement,
                Statement::Assign {
                    rvalue: Rvalue::BinaryOp(
                        BinOp::Add
                            | BinOp::Sub
                            | BinOp::Mul
                            | BinOp::Div
                            | BinOp::Rem
                            | BinOp::Shl
                            | BinOp::Shr,
                        _,
                        _,
                    ),
                    ..
                }
            )
        })
    })
}

/// Infer the conservative E6 structural facets for every function.
///
/// Duplicate def-paths are rejected as a group: the result contains the path
/// once with no positive facets.  This avoids `HashMap` collection collapsing a
/// good and bad body onto one apparently certified identity.
#[must_use]
pub fn infer_facets(functions: &[VerifiableFunction]) -> HashMap<String, FacetSet> {
    let mut occurrences: HashMap<&str, usize> = HashMap::new();
    for func in functions {
        *occurrences.entry(func.def_path.as_str()).or_default() += 1;
    }

    let mut inferred = HashMap::new();
    for func in functions {
        let unique = occurrences.get(func.def_path.as_str()) == Some(&1);
        let facets = if unique && is_valid_closed_leaf(func) {
            FacetSet {
                total: is_control_flow_loop_free(func),
                no_panic: !has_undischarged_panic_operation(func)
                    && is_structurally_panic_free(func),
                pure: is_structurally_pure(func),
                deterministic: is_structurally_deterministic(func),
            }
        } else {
            FacetSet::default()
        };
        inferred.insert(func.def_path.clone(), facets);
    }
    inferred
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        AssertMessage, BasicBlock, BlockId, LocalDecl, SourceSpan, UnwindEdge, VerifiableBody,
    };

    fn func_with(
        def_path: &str,
        locals: Vec<LocalDecl>,
        blocks: Vec<BasicBlock>,
        arg_count: usize,
        return_ty: Ty,
    ) -> VerifiableFunction {
        VerifiableFunction {
            name: def_path.rsplit("::").next().unwrap_or(def_path).to_string(),
            def_path: def_path.to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody { locals, blocks, arg_count, return_ty },
            contracts: Vec::new(),
            preconditions: Vec::new(),
            postconditions: Vec::new(),
            spec: Default::default(),
        }
    }

    fn unit_func(def_path: &str, blocks: Vec<BasicBlock>) -> VerifiableFunction {
        func_with(
            def_path,
            vec![LocalDecl { index: 0, ty: Ty::Unit, name: None }],
            blocks,
            0,
            Ty::Unit,
        )
    }

    fn block(id: usize, terminator: Terminator) -> BasicBlock {
        BasicBlock { id: BlockId(id), stmts: Vec::new(), terminator }
    }

    fn call(callee: &str, target: Option<usize>) -> Terminator {
        Terminator::Call {
            func: callee.to_string(),
            args: Vec::new(),
            dest: Place::local(0),
            target: target.map(BlockId),
            span: SourceSpan::default(),
            atomic: None,
            is_foreign: false,
            is_unsafe_sig: false,
            unwind: UnwindEdge::Unreachable,
        }
    }

    fn inferred(func: VerifiableFunction) -> FacetSet {
        let path = func.def_path.clone();
        infer_facets(&[func])[&path]
    }

    #[test]
    fn validated_call_free_leaf_has_all_four_facets() {
        assert!(inferred(unit_func("crate::leaf", vec![block(0, Terminator::Return)])).all());
    }

    #[test]
    fn every_call_fails_all_facets_closed() {
        for callee in
            ["core::num::<impl u64>::wrapping_add", "evil::wrapping_add", "crate::internal"]
        {
            let f = unit_func(
                "crate::caller",
                vec![block(0, call(callee, Some(1))), block(1, Terminator::Return)],
            );
            assert_eq!(inferred(f), FacetSet::default(), "call to {callee}");
        }

        let no_target = unit_func("crate::caller", vec![block(0, call("crate::never", None))]);
        assert_eq!(inferred(no_target), FacetSet::default());
    }

    #[test]
    fn ambiguous_bare_callee_never_falls_through_as_external() {
        let left = unit_func("crate::left::helper", vec![block(0, Terminator::Return)]);
        let right = unit_func("crate::right::helper", vec![block(0, Terminator::Return)]);
        let caller = unit_func(
            "crate::caller",
            vec![block(0, call("helper", Some(1))), block(1, Terminator::Return)],
        );
        let facets = infer_facets(&[left, right, caller]);
        assert!(facets["crate::left::helper"].all());
        assert!(facets["crate::right::helper"].all());
        assert_eq!(facets["crate::caller"], FacetSet::default());
    }

    #[test]
    fn duplicate_def_path_rejects_every_body_under_that_identity() {
        let good = unit_func("crate::same", vec![block(0, Terminator::Return)]);
        let bad = unit_func("crate::same", vec![block(0, Terminator::Resume)]);
        let facets = infer_facets(&[good, bad]);
        assert_eq!(facets.len(), 1);
        assert_eq!(facets["crate::same"], FacetSet::default());
    }

    #[test]
    fn malformed_block_identity_or_target_fails_closed() {
        let missing_bb0 = unit_func("crate::missing", vec![block(1, Terminator::Return)]);
        assert_eq!(inferred(missing_bb0), FacetSet::default());

        let duplicate = unit_func(
            "crate::duplicate",
            vec![block(0, Terminator::Goto(BlockId(1))), block(0, Terminator::Return)],
        );
        assert_eq!(inferred(duplicate), FacetSet::default());

        let dangling = unit_func("crate::dangling", vec![block(0, Terminator::Goto(BlockId(9)))]);
        assert_eq!(inferred(dangling), FacetSet::default());

        let dangling_switch = unit_func(
            "crate::switch",
            vec![block(
                0,
                Terminator::SwitchInt {
                    discr: Operand::Constant(ConstValue::Bool(true)),
                    targets: vec![(1, BlockId(9))],
                    otherwise: BlockId(0),
                    exhaustive_enum_unreachable: false,
                    span: SourceSpan::default(),
                },
            )],
        );
        assert_eq!(inferred(dangling_switch), FacetSet::default());

        let dangling_assert = unit_func(
            "crate::assert",
            vec![block(
                0,
                Terminator::Assert {
                    cond: Operand::Constant(ConstValue::Bool(true)),
                    expected: true,
                    msg: AssertMessage::BoundsCheck,
                    target: BlockId(4),
                    span: SourceSpan::default(),
                    unwind: UnwindEdge::Unreachable,
                },
            )],
        );
        assert_eq!(inferred(dangling_assert), FacetSet::default());
    }

    #[test]
    fn malformed_local_identity_or_place_fails_closed() {
        let bad_local = func_with(
            "crate::bad_local",
            vec![LocalDecl { index: 1, ty: Ty::Unit, name: None }],
            vec![block(0, Terminator::Return)],
            0,
            Ty::Unit,
        );
        assert_eq!(inferred(bad_local), FacetSet::default());

        let mut bad_place = unit_func("crate::bad_place", vec![block(0, Terminator::Return)]);
        bad_place.body.blocks[0].stmts.push(Statement::Assign {
            place: Place::local(3),
            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Unit)),
            span: SourceSpan::default(),
        });
        assert_eq!(inferred(bad_place), FacetSet::default());
    }

    #[test]
    fn exceptional_drop_and_opaque_terminators_fail_all_facets_closed() {
        let forbidden = [
            Terminator::Drop {
                place: Place::local(0),
                target: BlockId(0),
                span: SourceSpan::default(),
                unwind: UnwindEdge::Unreachable,
            },
            Terminator::Opaque {
                kind: "InlineAsm".into(),
                targets: vec![BlockId(0)],
                span: SourceSpan::default(),
            },
            Terminator::Unreachable,
            Terminator::Resume,
        ];
        for (index, terminator) in forbidden.into_iter().enumerate() {
            let path = format!("crate::forbidden_{index}");
            assert_eq!(inferred(unit_func(&path, vec![block(0, terminator)])), FacetSet::default());
        }
    }

    #[test]
    fn raw_division_never_claims_no_panic_without_a_discharge() {
        let u64_ty = Ty::Int { width: 64, signed: false };
        let mut f = func_with(
            "crate::div",
            vec![
                LocalDecl { index: 0, ty: u64_ty.clone(), name: None },
                LocalDecl { index: 1, ty: u64_ty.clone(), name: Some("x".into()) },
            ],
            vec![block(0, Terminator::Return)],
            1,
            u64_ty,
        );
        f.body.blocks[0].stmts.push(Statement::Assign {
            place: Place::local(0),
            rvalue: Rvalue::BinaryOp(
                BinOp::Div,
                Operand::Copy(Place::local(1)),
                Operand::Constant(ConstValue::Uint(0, 64)),
            ),
            span: SourceSpan::default(),
        });
        let facets = inferred(f);
        assert!(facets.total && facets.pure && facets.deterministic);
        assert!(!facets.no_panic);
        assert!(!facets.all());
    }

    #[test]
    fn checked_arithmetic_in_the_closed_fragment_remains_certifiable() {
        let u64_ty = Ty::Int { width: 64, signed: false };
        let checked_ty = Ty::Tuple(vec![u64_ty.clone(), Ty::Bool]);
        let mut f = func_with(
            "crate::checked",
            vec![
                LocalDecl { index: 0, ty: u64_ty.clone(), name: None },
                LocalDecl { index: 1, ty: u64_ty.clone(), name: Some("x".into()) },
                LocalDecl { index: 2, ty: checked_ty, name: None },
            ],
            vec![block(0, Terminator::Return)],
            1,
            u64_ty,
        );
        f.body.blocks[0].stmts.extend([
            Statement::Assign {
                place: Place::local(2),
                rvalue: Rvalue::CheckedBinaryOp(
                    BinOp::Add,
                    Operand::Copy(Place::local(1)),
                    Operand::Constant(ConstValue::Uint(1, 64)),
                ),
                span: SourceSpan::default(),
            },
            Statement::Assign {
                place: Place::local(0),
                rvalue: Rvalue::Use(Operand::Copy(Place {
                    local: 2,
                    projections: vec![Projection::Field(0)],
                })),
                span: SourceSpan::default(),
            },
        ]);
        assert!(inferred(f).all());
    }

    #[test]
    fn assert_poisons_only_no_panic_after_validation() {
        let f = unit_func(
            "crate::asserted",
            vec![
                block(
                    0,
                    Terminator::Assert {
                        cond: Operand::Constant(ConstValue::Bool(true)),
                        expected: true,
                        msg: AssertMessage::BoundsCheck,
                        target: BlockId(1),
                        span: SourceSpan::default(),
                        unwind: UnwindEdge::Unreachable,
                    },
                ),
                block(1, Terminator::Return),
            ],
        );
        let facets = inferred(f);
        assert!(facets.total && facets.pure && facets.deterministic);
        assert!(!facets.no_panic);
    }

    #[test]
    fn control_flow_cycle_poisons_only_total_after_validation() {
        let f = unit_func("crate::cycle", vec![block(0, Terminator::Goto(BlockId(0)))]);
        let facets = inferred(f);
        assert!(!facets.total);
        assert!(facets.no_panic && facets.pure && facets.deterministic);
    }

    #[test]
    fn non_closed_type_fails_every_facet() {
        let float = Ty::Float { width: 64 };
        let f = func_with(
            "crate::float",
            vec![LocalDecl { index: 0, ty: float.clone(), name: None }],
            vec![block(0, Terminator::Return)],
            0,
            float,
        );
        assert_eq!(inferred(f), FacetSet::default());
    }
}
