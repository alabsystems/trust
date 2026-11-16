// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Non-authorizing source/SSA call-trace comparison. Neither reader consumes
//! the emitter's call nodes or the kernel-reflected candidate expression.

use std::collections::HashMap;

use clean_kernel::{BinderInfo, Environment, Expr, ExprKind, Level, Literal, Name};
use trust_ir::{Constant, FuncId, Inst, Module, Ty, ValueId};

use super::{CalleeInterpretation, GateRefusal, UIntCarrier, bounded_name, refuse};

#[derive(Clone, Debug, PartialEq, Eq)]
enum Atom {
    Parameter(usize),
    UInt(u32, u64),
    Bool(bool),
    Call(usize),
}

#[derive(Debug, PartialEq, Eq)]
struct Call {
    target: FuncId,
    arguments: Vec<Atom>,
}

#[derive(Debug, PartialEq, Eq)]
struct Trace {
    calls: Vec<Call>,
    result: Atom,
}

struct Source<'a> {
    environment: &'a Environment,
    callees: HashMap<Name, &'a CalleeInterpretation>,
    calls: Vec<Call>,
    fuel: usize,
    applications: usize,
}

impl Source<'_> {
    fn spend(&mut self) -> Result<(), GateRefusal> {
        self.fuel =
            self.fuel.checked_sub(1).ok_or_else(|| refuse("source trace exceeds node budget"))?;
        Ok(())
    }

    fn expression(
        &mut self,
        expression: &Expr,
        locals: &mut Vec<Atom>,
        depth: usize,
    ) -> Result<Atom, GateRefusal> {
        self.spend()?;
        if depth > 96 {
            return Err(refuse("source trace exceeds depth budget"));
        }
        match expression.kind() {
            ExprKind::MData(_, inner) => return self.expression(inner, locals, depth + 1),
            ExprKind::BVar(index) => {
                return locals
                    .len()
                    .checked_sub(*index as usize)
                    .and_then(|remaining| remaining.checked_sub(1))
                    .and_then(|index| locals.get(index))
                    .cloned()
                    .ok_or_else(|| refuse("source trace contains an unbound variable"));
            }
            ExprKind::Let(_, _, value, body, _) => {
                let value = self.expression(value, locals, depth + 1)?;
                locals.push(value);
                let result = self.expression(body, locals, depth + 1);
                locals.pop();
                return result;
            }
            _ => {}
        }

        let mut head = expression;
        let mut arguments = Vec::new();
        while let ExprKind::App(function, argument) = head.kind() {
            self.spend()?;
            if arguments.len() == 64 || self.applications == 256 {
                return Err(refuse("source trace exceeds application budget"));
            }
            self.applications += 1;
            arguments.push(argument.as_ref());
            head = function;
        }
        arguments.reverse();
        let ExprKind::Const(name, levels) = head.kind() else {
            return Err(refuse("source trace has an unsupported computational head"));
        };
        bounded_name(name)?;
        // Surface numerals use the actual OfNat dictionary. Accept only its
        // exact checked canonical body, with no beta/zeta/whnf that could erase
        // evaluation of a Rust call hidden inside a dictionary expression.
        if *name == Name::from_string("OfNat.ofNat")
            && levels.as_slice() == [Level::zero()]
            && arguments.len() == 3
        {
            for bits in [8, 16, 32, 64] {
                let carrier = Expr::const_str(&format!("UInt{bits}"));
                let ExprKind::Lit(Literal::Nat(value)) = arguments[1].kind() else {
                    return Err(refuse("source trace numeral is not a literal"));
                };
                if *arguments[0] != carrier {
                    continue;
                }
                let instance_name = Name::from_string(&format!("instOfNatUInt{bits}"));
                let instance =
                    Expr::app(Expr::const_(instance_name.clone(), vec![]), arguments[1].clone());
                let expected = Expr::lam(
                    BinderInfo::Default,
                    Expr::const_str("Nat"),
                    Expr::apps(
                        Expr::const_(Name::from_string("OfNat.mk"), vec![Level::zero()]),
                        [
                            carrier,
                            Expr::bvar(0),
                            Expr::app(Expr::const_str(&format!("UInt{bits}.ofNat")), Expr::bvar(0)),
                        ],
                    ),
                );
                if *arguments[2] != instance
                    || self
                        .environment
                        .get_const(&instance_name)
                        .and_then(|constant| constant.value.as_ref())
                        != Some(&expected)
                {
                    return Err(refuse(
                        "source trace numeral dictionary is not the exact canonical definition",
                    ));
                }
                return value
                    .to_u64()
                    .filter(|value| u128::from(*value) < (1u128 << bits))
                    .map(|value| Atom::UInt(bits, value))
                    .ok_or_else(|| refuse("source trace numeral exceeds its exact carrier"));
            }
            return Err(refuse("source trace numeral has an unsupported carrier"));
        }
        if !levels.is_empty() {
            return Err(refuse("source trace requires monomorphic computational heads"));
        }
        if let Some(callee) = self.callees.get(name).copied() {
            if arguments.len() != callee.signature.params.len() {
                return Err(refuse("source trace call arity disagrees"));
            }
            let mut operands = Vec::with_capacity(arguments.len());
            for argument in arguments {
                operands.push(self.expression(argument, locals, depth + 1)?);
            }
            if self.calls.len() == 32 {
                return Err(refuse("source trace exceeds call budget"));
            }
            let ordinal = self.calls.len();
            self.calls.push(Call { target: callee.id, arguments: operands });
            return Ok(Atom::Call(ordinal));
        }
        if arguments.is_empty() {
            if *name == Name::from_string("Bool.true") {
                return Ok(Atom::Bool(true));
            }
            if *name == Name::from_string("Bool.false") {
                return Ok(Atom::Bool(false));
            }
        }
        for bits in [8, 16, 32, 64] {
            if *name == Name::from_string(&format!("UInt{bits}.ofNat")) && arguments.len() == 1 {
                if let ExprKind::Lit(Literal::Nat(value)) = arguments[0].kind() {
                    if let Some(value) = value.to_u64() {
                        if u128::from(value) < (1u128 << bits) {
                            return Ok(Atom::UInt(bits, value));
                        }
                    }
                }
                return Err(refuse("source trace requires an exact in-range UInt literal"));
            }
        }
        Err(refuse("source trace does not unfold helpers or unknown constants"))
    }
}

fn source_trace(
    environment: &Environment,
    declaration: &Name,
    arity: usize,
    interpretations: &[CalleeInterpretation],
) -> Result<Trace, GateRefusal> {
    let definition = environment
        .get_const(declaration)
        .and_then(|constant| constant.value.as_ref())
        .ok_or_else(|| refuse("source trace has no original declaration value"))?;
    let mut source = Source {
        environment,
        callees: interpretations.iter().map(|callee| (callee.name.clone(), callee)).collect(),
        calls: Vec::new(),
        fuel: 2048,
        applications: 0,
    };
    let mut body = definition;
    let mut locals = Vec::new();
    for index in 0..arity {
        while let ExprKind::MData(_, inner) = body.kind() {
            source.spend()?;
            body = inner;
        }
        let ExprKind::Lam(_, _, inner) = body.kind() else {
            return Err(refuse("source trace has an incomplete parameter telescope"));
        };
        locals.push(Atom::Parameter(index));
        body = inner;
    }
    let result = source.expression(body, &mut locals, 0)?;
    Ok(Trace { calls: source.calls, result })
}

fn ir_trace(module: &Module, root: FuncId) -> Result<Trace, GateRefusal> {
    // The caller first validates the entire module and bounded straight-line
    // SSA grammar. Read actual instructions again, independently of reflection.
    let function = module.function_by_id(root).ok_or_else(|| refuse("trace root missing"))?;
    let [block] = function.blocks.as_slice() else {
        return Err(refuse("trace requires one actual block"));
    };
    let mut values = HashMap::<ValueId, Atom>::new();
    for (index, (id, _)) in block.params.iter().enumerate() {
        values.insert(*id, Atom::Parameter(index));
    }
    let mut calls = Vec::new();
    let operand = |values: &HashMap<ValueId, Atom>, id: &ValueId| {
        values.get(id).cloned().ok_or_else(|| refuse("trace operand precedes its definition"))
    };
    for node in &block.body {
        let atom = match &node.inst {
            Inst::Const { ty: Ty::Bool, value: Constant::Bool(value) } => Atom::Bool(*value),
            Inst::Const { ty, value: Constant::Int(value) } => {
                let width =
                    UIntCarrier::from_ir(ty).ok_or_else(|| refuse("trace literal carrier"))?;
                let value = u64::try_from(*value).map_err(|_| refuse("trace literal range"))?;
                Atom::UInt(width.bits(), value)
            }
            Inst::Call { callee, args } => {
                let arguments =
                    args.iter().map(|id| operand(&values, id)).collect::<Result<_, _>>()?;
                let ordinal = calls.len();
                calls.push(Call { target: *callee, arguments });
                Atom::Call(ordinal)
            }
            Inst::Return { values: returned } => {
                let [id] = returned.as_slice() else {
                    return Err(refuse("trace requires one returned value"));
                };
                return Ok(Trace { calls, result: operand(&values, id)? });
            }
            _ => return Err(refuse("trace instruction outside its vocabulary")),
        };
        let [id] = node.results.as_slice() else {
            return Err(refuse("trace instruction must define one result"));
        };
        if values.insert(*id, atom).is_some() {
            return Err(refuse("trace value defined twice"));
        }
    }
    Err(refuse("trace has no Return"))
}

pub(super) fn check(
    environment: &Environment,
    declaration: &Name,
    module: &Module,
    root: FuncId,
    interpretations: &[CalleeInterpretation],
) -> Result<(), GateRefusal> {
    let function = module.function_by_id(root).ok_or_else(|| refuse("trace root missing"))?;
    let arity = module
        .func_types
        .get(function.ty.index() as usize)
        .ok_or_else(|| refuse("trace root signature missing"))?
        .params
        .len();
    let source = source_trace(environment, declaration, arity, interpretations)?;
    let emitted = ir_trace(module, root)?;
    if source != emitted {
        return Err(refuse("original source call order/dataflow differs from actual SSA"));
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use trust_ir::FuncTy;

    use super::*;

    fn reader<'a>(environment: &'a Environment, callees: &'a [CalleeInterpretation]) -> Source<'a> {
        Source {
            environment,
            callees: callees.iter().map(|callee| (callee.name.clone(), callee)).collect(),
            calls: Vec::new(),
            fuel: 2048,
            applications: 0,
        }
    }

    #[test]
    fn source_node_and_depth_budgets_are_checked_before_traversal() {
        let environment = Environment::new();
        let mut source = reader(&environment, &[]);
        let mut locals = vec![Atom::Parameter(0)];
        source.fuel = 1;
        assert_eq!(source.expression(&Expr::bvar(0), &mut locals, 96).unwrap(), Atom::Parameter(0));
        assert!(
            source
                .expression(&Expr::bvar(0), &mut locals, 0)
                .unwrap_err()
                .note()
                .contains("node budget")
        );
        source.fuel = 2048;
        assert!(
            source
                .expression(&Expr::bvar(0), &mut locals, 97)
                .unwrap_err()
                .note()
                .contains("depth budget")
        );
    }

    #[test]
    fn source_application_and_call_limits_have_independent_boundary_controls() {
        let environment = Environment::new();
        let callees = [CalleeInterpretation {
            id: FuncId::new(7),
            name: Name::from_string("f"),
            signature: FuncTy::unrecorded(vec![Ty::U64], vec![Ty::U64], false),
        }];
        let expression = Expr::app(Expr::const_str("f"), Expr::bvar(0));
        let mut locals = vec![Atom::Parameter(0)];
        let mut source = reader(&environment, &callees);
        source.applications = 255;
        assert_eq!(source.expression(&expression, &mut locals, 0).unwrap(), Atom::Call(0));
        assert!(
            source
                .expression(&expression, &mut locals, 0)
                .unwrap_err()
                .note()
                .contains("application budget")
        );
        let mut source = reader(&environment, &callees);
        source.calls =
            (0..31).map(|_| Call { target: FuncId::new(7), arguments: locals.clone() }).collect();
        assert_eq!(source.expression(&expression, &mut locals, 0).unwrap(), Atom::Call(31));
        assert!(
            source
                .expression(&expression, &mut locals, 0)
                .unwrap_err()
                .note()
                .contains("call budget")
        );
    }

    #[test]
    fn source_unknown_heads_are_not_reduced_and_loose_variables_refuse() {
        let environment = Environment::new();
        let mut source = reader(&environment, &[]);
        let mut locals = vec![Atom::Parameter(0)];
        assert!(
            source
                .expression(&Expr::const_str("unknownHelper"), &mut locals, 0)
                .unwrap_err()
                .note()
                .contains("does not unfold")
        );
        let beta_redex = Expr::app(
            Expr::lam(BinderInfo::Default, Expr::const_str("UInt64"), Expr::bvar(0)),
            Expr::bvar(0),
        );
        assert!(
            source
                .expression(&beta_redex, &mut locals, 0)
                .unwrap_err()
                .note()
                .contains("unsupported computational head")
        );
        assert!(
            source
                .expression(&Expr::bvar(1_048_574), &mut locals, 0)
                .unwrap_err()
                .note()
                .contains("unbound variable")
        );
    }

    #[test]
    fn source_numerals_require_the_actual_canonical_instance_definition() {
        let numeral = Expr::apps(
            Expr::const_(Name::from_string("OfNat.ofNat"), vec![Level::zero()]),
            [
                Expr::const_str("UInt64"),
                Expr::nat_lit(7),
                Expr::app(Expr::const_str("instOfNatUInt64"), Expr::nat_lit(7)),
            ],
        );
        let environment = Environment::with_prelude();
        assert_eq!(
            reader(&environment, &[]).expression(&numeral, &mut Vec::new(), 0).unwrap(),
            Atom::UInt(64, 7)
        );
        let empty = Environment::new();
        assert!(
            reader(&empty, &[])
                .expression(&numeral, &mut Vec::new(), 0)
                .unwrap_err()
                .note()
                .contains("dictionary is not the exact canonical definition")
        );
    }
}
