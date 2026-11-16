// Trust: kernel-checked, one-scalar-field constructor return facts.
// Copyright 2026 Andrew Yates. SPDX-License-Identifier: Apache-2.0 OR MIT.

//! Candidate synthesis is untrusted. Admission checks the ORIGINAL aggregate
//! body, not the scalar proposal used to reuse D5-B's bounded symbolic walk.
//! Facts bind actuals before the call and the result field after its success
//! edge. They do not pin the whole aggregate or authorize a SAT refutation.

use super::*;

#[derive(Clone, Debug, PartialEq, Eq)]
enum FieldValue {
    Parameter(usize),
    Integer(i128),
    Boolean(bool),
}

/// Invocation-local field fact. The producer must kernel-check EVERY candidate
/// row and establish the exact nongeneric inherent-body identity before binding
/// it. No public field, deserialization, or default can fabricate a model.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConstructorReturnSummary {
    def_path: String,
    identity: trust_types::CalleeIdentity,
    param_types: Vec<Ty>,
    result_ty: Ty,
    value: FieldValue,
}

/// A proposal, with no proof authority until its original-body checks pass.
#[derive(Clone, Debug)]
pub struct ConstructorReturnCandidate {
    def_path: String,
    param_types: Vec<Ty>,
    result_ty: Ty,
    value: FieldValue,
    postcondition: Formula,
    check_vcs: Vec<VerificationCondition>,
}

impl ConstructorReturnCandidate {
    pub fn check_vcs(&self) -> &[VerificationCondition] {
        &self.check_vcs
    }
    pub fn postcondition(&self) -> &Formula {
        &self.postcondition
    }
    pub fn result_ty(&self) -> &Ty {
        &self.result_ty
    }
    pub fn parameter_types(&self) -> &[Ty] {
        &self.param_types
    }

    /// Compiler producer contract: every check row was kernel-certified in this
    /// compilation; TyCtxt established the exact local inherent body, output
    /// layout, noninterposable symbol, absence of generics/contracts/skip, and
    /// unique summary key. Identity is the same full token stamped on calls.
    pub fn bind_checked_identity(
        &self,
        identity: trust_types::CalleeIdentity,
    ) -> ConstructorReturnSummary {
        ConstructorReturnSummary {
            def_path: self.def_path.clone(),
            identity,
            param_types: self.param_types.clone(),
            result_ty: self.result_ty.clone(),
            value: self.value.clone(),
        }
    }
}

fn scalar(ty: &Ty) -> bool {
    matches!(ty, Ty::Bool | Ty::Int { width: 1..=64, .. })
}

fn field_type(ty: &Ty) -> Option<&Ty> {
    let Ty::Adt {
        fields,
        variants,
        adt_kind: Some(trust_types::AdtKind::Struct),
        arbitrary_precision,
        ..
    } = ty
    else {
        return None;
    };
    // The live extractor stamps ordinary drop-total structs too. JSON drops
    // this transient metadata, so requiring None accepts the fixture while
    // refusing its source. This stamp grants NO constructor proof credit:
    // original-body kernel checks and the compiler's no-Drop/layout/identity
    // gates remain mandatory. Other authenticated abstract carriers stay out.
    (matches!(arbitrary_precision, None | Some(trust_types::AdtAuth::TotalDrop(None)))
        && fields.len() == 1
        && variants.is_empty()
        && scalar(&fields[0].1))
    .then(|| &fields[0].1)
}

/// Propose only a one-field struct's scalar parameter/constant passthrough.
/// The transformed scalar body proposes an expression; ONLY original-body
/// postcondition VCs can admit that expression as a constructor fact.
pub fn infer_constructor_return_candidate(
    func: &VerifiableFunction,
) -> Result<ConstructorReturnCandidate, &'static str> {
    // Extraction also places generated scalar type bounds in preconditions.
    // As in D5-B, they are never evidence: original-body checks clear ALL
    // entry hypotheses. Authored clauses are excluded here and by TyCtxt.
    if !func.contracts.is_empty() || !func.postconditions.is_empty() || !func.spec.is_empty() {
        return Err("authored contract present");
    }
    let result_ty = func.body.return_ty.clone();
    let field_ty = field_type(&result_ty).ok_or("not a one-scalar-field struct")?.clone();
    // Keep this fragment independent of additive scalar-inference changes
    // (in particular its separate unused-Marker parameter recovery).
    if func.body.locals.iter().any(|decl| decl.index != 0 && !scalar(&decl.ty)) {
        return Err("non-scalar constructor input/temporary");
    }
    let Ty::Adt { name: result_name, .. } = &result_ty else {
        return Err("not a struct return");
    };
    crate::validate_function(func).map_err(|_| "malformed function")?;
    let mut probe = func.clone();
    let Some(ret) = probe.body.locals.iter_mut().find(|decl| decl.index == 0) else {
        return Err("missing return local");
    };
    if ret.ty != result_ty {
        return Err("return type mismatch");
    }
    ret.ty = field_ty.clone();
    probe.body.return_ty = field_ty;
    let mut constructors = 0;
    for block in &mut probe.body.blocks {
        for statement in &mut block.stmts {
            let Statement::Assign { place, rvalue, .. } = statement else { continue };
            if place.local != 0 {
                continue;
            }
            if !place.projections.is_empty() {
                return Err("projected return write");
            }
            let Rvalue::Aggregate(
                trust_types::AggregateKind::Adt { name, variant: 0, active_field: None, args },
                operands,
            ) = rvalue
            else {
                return Err("non-constructor return write");
            };
            if name != result_name || args.as_deref().is_some_and(|args| args != name) {
                return Err("constructor type identity mismatch");
            }
            let [operand] = operands.as_slice() else {
                return Err("constructor field count");
            };
            *rvalue = Rvalue::Use(operand.clone());
            constructors += 1;
        }
    }
    if constructors != 1 {
        return Err("not exactly one constructor write");
    }
    let scalar_candidate = infer_return_candidate(&probe)?;
    let Formula::Eq(_, expression) = scalar_candidate.postcondition() else {
        return Err("unexpected scalar candidate");
    };
    let value = match expression.as_ref() {
        Formula::Var(name, _) => FieldValue::Parameter(
            scalar_candidate
                .param_names()
                .iter()
                .position(|param| param == name)
                .ok_or("non-parameter expression")?,
        ),
        Formula::Int(value) => FieldValue::Integer(*value),
        Formula::Bool(value) => FieldValue::Boolean(*value),
        _ => return Err("not a parameter/constant passthrough"),
    };
    let postcondition = Formula::Eq(
        Box::new(operand_to_formula(
            func,
            &Operand::Copy(Place {
                local: 0,
                projections: vec![trust_types::Projection::Field(0)],
            }),
        )),
        expression.clone(),
    );
    let check_vcs = inferred_return_check_vcs(func, &postcondition)?;
    let param_types = (1..=func.body.arg_count)
        .map(|index| crate::local_ty_ref(func, index).cloned().ok_or("missing parameter type"))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(ConstructorReturnCandidate {
        def_path: func.def_path.clone(),
        param_types,
        result_ty,
        value,
        postcondition,
        check_vcs,
    })
}

/// Intern the same original-body check rows the compiler will certify.
pub fn intern_constructor_return_rows(
    rows: &mut trust_types::vc_context::VcContext,
    candidate: &ConstructorReturnCandidate,
) {
    super::intern_eager_rows(rows, candidate.check_vcs());
}

fn actual_has_type(func: &VerifiableFunction, actual: &Operand, expected: &Ty) -> bool {
    match actual {
        Operand::Copy(place) | Operand::Move(place) => {
            crate::place_ty_cow(func, place).is_some_and(|ty| ty.as_ref() == expected)
        }
        Operand::Constant(ConstValue::Bool(_)) => *expected == Ty::Bool,
        Operand::Constant(ConstValue::Uint(value, width)) => matches!(
            expected, Ty::Int { width: expected, signed: false }
                if expected == width && *width <= 64 && *width > 0
                    && *value < (1u128 << *width)
        ),
        _ => false,
    }
}

/// Typed establish-point facts, independent of generic postcondition injection.
/// No field-spelling whitelist, global result pin, or blanket time rewrite.
pub(super) fn constructor_return_callsite_facts(
    sv: &StmtVersionCtx,
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
) -> Vec<Formula> {
    constructor_return_callsite_fact(sv, func, block).into_iter().collect()
}

fn constructor_return_callsite_fact(
    sv: &StmtVersionCtx,
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
) -> Option<Formula> {
    let Terminator::Call {
        func: callee,
        args,
        dest,
        target: Some(target),
        callee_identity: Some(identity),
        is_foreign: false,
        is_unsafe_sig: false,
        ..
    } = &block.terminator
    else {
        return None;
    };
    let summary = crate::constructor_return_summary(callee)?;
    if identity != &summary.identity
        || callee != &summary.def_path
        || args.len() != summary.param_types.len()
        || !dest.projections.is_empty()
        || crate::local_ty_ref(func, dest.local)? != &summary.result_ty
        || !crate::local_defs::dest_fact_is_version_pinnable(func, dest.local)
        || !crate::local_defs::body_storage_has_no_aliases(&func.body, dest.local)
        || target.0 == 0
        || !args.iter().zip(&summary.param_types).all(|(arg, ty)| actual_has_type(func, arg, ty))
    {
        return None;
    }
    let field = Place { local: dest.local, projections: vec![trust_types::Projection::Field(0)] };
    let field_name = crate::place_to_var_name(func, &field);
    // Only the call's actual definition token may establish this field fact.
    // A join/unknown/pre-call value cannot silently substitute for that token.
    let token = sv.version_token_at(func, *target, 0, &field_name)?;
    if token
        .strip_prefix('s')
        .and_then(|s| s.strip_suffix("_t"))
        .and_then(|s| s.parse::<usize>().ok())
        != Some(block.id.0)
    {
        return None;
    }
    let mut incoming = 0usize;
    for b in &func.body.blocks {
        let normal = match &b.terminator {
            Terminator::Goto(t)
            | Terminator::Call { target: Some(t), .. }
            | Terminator::Assert { target: t, .. }
            | Terminator::Drop { target: t, .. } => usize::from(t == target),
            Terminator::SwitchInt { targets, otherwise, .. } => {
                targets.iter().filter(|(_, t)| t == target).count()
                    + usize::from(otherwise == target)
            }
            Terminator::Opaque { targets, .. } => targets.iter().filter(|&t| t == target).count(),
            Terminator::Return
            | Terminator::Unreachable
            | Terminator::Call { target: None, .. }
            | _ => 0,
        };
        let unwind = usize::from(b.terminator.unwind_cleanup_target().as_ref() == Some(target));
        incoming += normal + unwind;
        if incoming > 1 {
            return None;
        }
    }
    if incoming != 1 {
        return None;
    }
    let rhs = match summary.value {
        FieldValue::Parameter(index) => version_rename_at(
            &operand_to_formula(func, args.get(index)?),
            sv,
            func,
            block.id,
            block.stmts.len(),
        ),
        FieldValue::Integer(value) => Formula::Int(value),
        FieldValue::Boolean(value) => Formula::Bool(value),
    };
    let lhs = version_rename_at(
        &Formula::var(&field_name, crate::place_sort(func, &field).unwrap_or(Sort::Int)),
        sv,
        func,
        *target,
        0,
    );
    Some(Formula::Eq(Box::new(lhs), Box::new(rhs)))
}

#[cfg(test)]
mod tests;
