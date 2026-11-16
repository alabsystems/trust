//! Proof-free, source-site analysis for the bounded constructor-import lane.
//!
//! This module neither admits a body nor discharges an obligation. Its caller
//! must bind compiler-resolved instances, preserve every call path, and charge
//! the resulting predicates to the actual caller. Unsupported shapes are an
//! explicit refusal, never an empty safety inventory.

use super::*;

#[derive(Clone, Debug, serde::Serialize)]
pub struct BundledConstructorSafetySite {
    pub block: BlockId,
    pub span: TrustSourceSpan,
    pub description: String,
    /// Entry-relative requirement, including the site's actual reachability
    /// guard. Formal names use the same positional/collision-safe convention
    /// as the existing caller-side precondition generator.
    pub requirement: Formula,
    /// All arithmetic operations covered by this MIR Assert. A single
    /// DivisionByZero check can guard BOTH division and remainder.
    pub guarded_operations: Vec<(BlockId, usize)>,
}

#[derive(Clone, Debug, serde::Serialize)]
pub struct BundledConstructorCallSite {
    pub block: BlockId,
    pub span: TrustSourceSpan,
    pub callee: String,
    pub identity: trust_types::CalleeIdentity,
    pub arguments: Vec<Operand>,
    pub guard: Formula,
}

pub fn bundled_constructor_formal_names(function: &VerifiableFunction) -> Vec<String> {
    (1..=function.body.arg_count)
        .map(|index| collision_safe_local_name(&function.body.locals, index))
        .collect()
}

struct Analyzer<'a> {
    function: &'a VerifiableFunction,
    guard_cache: std::cell::RefCell<FxHashMap<(BlockId, BlockId), Formula>>,
}

impl<'a> Analyzer<'a> {
    fn block(&self, id: BlockId) -> Result<&'a TrustBlock, &'static str> {
        let mut matches = self.function.body.blocks.iter().filter(|block| block.id == id);
        match (matches.next(), matches.next()) {
            (Some(block), None) => Ok(block),
            _ => Err("missing or duplicate constructor block identity"),
        }
    }

    fn formal(&self, place: &Place) -> Result<Formula, &'static str> {
        if !place.projections.is_empty()
            || place.local == 0
            || place.local > self.function.body.arg_count
        {
            return Err("constructor predicate operand is not a whole formal");
        }
        let local = self
            .function
            .body
            .locals
            .iter()
            .find(|local| local.index == place.local)
            .ok_or("constructor formal has no type")?;
        let sort = match local.ty {
            Ty::Int { .. } => Sort::Int,
            Ty::Bool => Sort::Bool,
            _ => return Err("constructor predicate formal is not a scalar integer or bool"),
        };
        // An entry formal is not a synonym for its later, possibly modified
        // value. Refuse both direct writes and address-taking, including a
        // borrow whose mutation occurs behind a different local name.
        for block in &self.function.body.blocks {
            for statement in &block.stmts {
                if !matches!(statement.local_write(place.local), trust_types::LocalWrite::Untouched)
                {
                    return Err("constructor predicate formal is written or escapes");
                }
                if let Statement::Assign { place: dest, rvalue, .. } = statement {
                    if dest.local == place.local {
                        return Err("constructor predicate formal is reassigned");
                    }
                    if matches!(rvalue,
                        Rvalue::Ref { place: source, .. } | Rvalue::AddressOf(_, source)
                            if source.local == place.local)
                    {
                        return Err("constructor predicate formal address escapes");
                    }
                }
            }
            if !matches!(
                block.terminator.local_write(place.local),
                trust_types::LocalWrite::Untouched
            ) {
                return Err("constructor predicate formal has a terminator write");
            }
        }
        Ok(Formula::var(&collision_safe_local_name(&self.function.body.locals, place.local), sort))
    }

    fn operand(
        &self,
        operand: &Operand,
        block: BlockId,
        before: usize,
        fuel: usize,
    ) -> Result<Formula, &'static str> {
        if fuel == 0 {
            return Err("constructor predicate alias depth exceeded");
        }
        let place = match operand {
            Operand::Constant(ConstValue::Bool(value)) => return Ok(Formula::Bool(*value)),
            Operand::Constant(ConstValue::Int(value)) => return Ok(Formula::Int(*value)),
            Operand::Constant(ConstValue::Uint(value, _)) => {
                return i128::try_from(*value)
                    .map(Formula::Int)
                    .map_err(|_| "constructor predicate integer is not representable");
            }
            Operand::Copy(place) | Operand::Move(place) => place,
            _ => return Err("unsupported constructor predicate operand"),
        };
        if place.local > 0 && place.local <= self.function.body.arg_count {
            return self.formal(place);
        }
        if !place.projections.is_empty() {
            return Err("projected constructor predicate temporary");
        }
        // This first slice deliberately accepts only dominating same-block
        // definitions. A unique assignment in a sibling/predecessor block is
        // not silently treated as an entry value.
        let mut definition = None;
        for source in &self.function.body.blocks {
            for (index, statement) in source.stmts.iter().enumerate() {
                if statement.escapes_local(place.local)
                    || matches!(statement, Statement::Assign {
                        rvalue: Rvalue::Ref { place: borrowed, .. }, ..
                    } if borrowed.local == place.local)
                {
                    return Err("constructor predicate temporary address escapes");
                }
                if !matches!(
                    statement.local_write(place.local),
                    trust_types::LocalWrite::Untouched | trust_types::LocalWrite::WholeNamed(_)
                ) {
                    return Err("constructor predicate temporary has an untracked write or escape");
                }
                if let Statement::Assign { place: dest, rvalue, .. } = statement
                    && dest.local == place.local
                {
                    if source.id != block
                        || index >= before
                        || !dest.projections.is_empty()
                        || definition.is_some()
                    {
                        return Err(
                            "constructor predicate temporary lacks a unique dominating definition",
                        );
                    }
                    definition = Some((index, rvalue));
                }
            }
            if !matches!(
                source.terminator.local_write(place.local),
                trust_types::LocalWrite::Untouched
            ) {
                return Err("constructor predicate temporary has a terminator write");
            }
        }
        let (index, rvalue) = definition.ok_or("unbound constructor predicate temporary")?;
        let child = |operand| self.operand(operand, block, index, fuel - 1);
        match rvalue {
            Rvalue::Use(operand) => child(operand),
            Rvalue::BinaryOp(BinOp::Eq, left, right) => {
                Ok(Formula::Eq(Box::new(child(left)?), Box::new(child(right)?)))
            }
            Rvalue::BinaryOp(BinOp::Ne, left, right) => Ok(Formula::Not(Box::new(Formula::Eq(
                Box::new(child(left)?),
                Box::new(child(right)?),
            )))),
            _ => Err("unsupported constructor predicate definition"),
        }
    }

    fn guard(
        &self,
        current: BlockId,
        target: BlockId,
        visiting: &mut Vec<BlockId>,
    ) -> Result<Formula, &'static str> {
        if let Some(cached) = self.guard_cache.borrow().get(&(current, target)).cloned() {
            return Ok(cached);
        }
        if current == target {
            return Ok(Formula::Bool(true));
        }
        if !self.can_reach(current, target)? {
            return Ok(Formula::Bool(false));
        }
        if visiting.contains(&current) {
            return Err("cyclic constructor reachability");
        }
        if visiting.len() >= 64 {
            return Err("constructor reachability depth exceeded");
        }
        visiting.push(current);
        let block = self.block(current)?;
        let result = match &block.terminator {
            Terminator::Goto(next) => self.guard(*next, target, visiting),
            Terminator::Return | Terminator::Resume => Ok(Formula::Bool(false)),
            Terminator::SwitchInt { discr, targets, otherwise, .. } => {
                let otherwise_guard = self.guard(*otherwise, target, visiting)?;
                let mut arms = Vec::new();
                for (value, successor) in targets {
                    arms.push((*value, self.guard(*successor, target, visiting)?));
                }
                if arms.iter().all(|(_, guard)| *guard == otherwise_guard) {
                    Ok(otherwise_guard)
                } else {
                    let discr = self.operand(discr, current, block.stmts.len(), 8)?;
                    let mut cases = Vec::new();
                    let mut alternatives = Vec::new();
                    for (value, guard) in arms {
                        let value = i128::try_from(value)
                            .map_err(|_| "constructor switch value is not representable")?;
                        let literal = if matches!(
                            discr,
                            Formula::Var(_, Sort::Bool)
                                | Formula::Bool(_)
                                | Formula::Eq(..)
                                | Formula::Not(..)
                        ) {
                            match value {
                                0 => Formula::Bool(false),
                                1 => Formula::Bool(true),
                                _ => return Err("non-boolean constructor switch value"),
                            }
                        } else {
                            Formula::Int(value)
                        };
                        let case = Formula::Eq(Box::new(discr.clone()), Box::new(literal));
                        cases.push(case.clone());
                        alternatives.push(Formula::And(vec![case, guard]));
                    }
                    alternatives.push(Formula::And(vec![
                        Formula::Not(Box::new(Formula::Or(cases))),
                        otherwise_guard,
                    ]));
                    Ok(Formula::Or(alternatives))
                }
            }
            // A pre-target call/Assert/drop can terminate or unwind. Treating
            // its normal successor as unconditional would erase that condition.
            // The acyclic call-path composer must account for such effects.
            _ => Err("constructor reachability crosses an unaccounted effect"),
        };
        visiting.pop();
        if let Ok(guard) = &result {
            self.guard_cache.borrow_mut().insert((current, target), guard.clone());
        }
        result
    }

    fn validate_cfg(&self) -> Result<(), &'static str> {
        fn visit(
            analyzer: &Analyzer<'_>,
            block: BlockId,
            active: &mut Vec<BlockId>,
            complete: &mut Vec<BlockId>,
        ) -> Result<(), &'static str> {
            if complete.contains(&block) {
                return Ok(());
            }
            if active.contains(&block) {
                return Err("cyclic constructor CFG");
            }
            active.push(block);
            let mut next_blocks = Vec::new();
            analyzer.block(block)?.terminator.for_each_exit_block_target(|next| {
                next_blocks.push(next);
            });
            for next in next_blocks {
                visit(analyzer, next, active, complete)?;
            }
            active.pop();
            complete.push(block);
            Ok(())
        }
        if self.function.body.blocks.len() > 64 {
            return Err("constructor CFG size exceeded");
        }
        let mut complete = Vec::new();
        for block in &self.function.body.blocks {
            visit(self, block.id, &mut Vec::new(), &mut complete)?;
        }
        Ok(())
    }

    fn can_reach(&self, from: BlockId, target: BlockId) -> Result<bool, &'static str> {
        let mut pending = vec![from];
        let mut visited = Vec::new();
        while let Some(current) = pending.pop() {
            if current == target {
                return Ok(true);
            }
            if visited.contains(&current) {
                continue;
            }
            if visited.len() >= 64 {
                return Err("constructor CFG size exceeded");
            }
            visited.push(current);
            self.block(current)?.terminator.for_each_exit_block_target(|next| {
                pending.push(next);
            });
        }
        Ok(false)
    }
}

/// Derive requirements for local scalar div/rem assertions and direct panic
/// calls. Ordinary calls and cleanup are NOT certified here: the compiler's
/// closure inventory must separately account for them before using these rows.
pub fn bundled_constructor_local_safety_sites(
    function: &VerifiableFunction,
) -> Result<Vec<BundledConstructorSafetySite>, &'static str> {
    let analyzer = Analyzer { function, guard_cache: Default::default() };
    analyzer.validate_cfg()?;
    let entry = function.body.blocks.first().ok_or("constructor body is empty")?.id;
    let mut sites = Vec::new();
    for block in &function.body.blocks {
        let (success, span, description, guarded_operations) = match &block.terminator {
            Terminator::Assert { cond, expected, msg, target, span, .. } => {
                if !matches!(msg, AssertMessage::DivisionByZero | AssertMessage::RemainderByZero) {
                    return Err("constructor has an unsupported MIR assertion");
                }
                let predicate = analyzer.operand(cond, block.id, block.stmts.len(), 8)?;
                let success = if *expected { predicate } else { Formula::Not(Box::new(predicate)) };
                let target = analyzer.block(*target)?;
                let mut operations = Vec::new();
                for (index, statement) in target.stmts.iter().enumerate() {
                    if let Statement::Assign {
                        rvalue: Rvalue::BinaryOp(BinOp::Div | BinOp::Rem, _, rhs),
                        ..
                    } = statement
                    {
                        let divisor = analyzer.operand(rhs, target.id, index, 8)?;
                        let nonzero = Formula::Not(Box::new(Formula::Eq(
                            Box::new(divisor),
                            Box::new(Formula::Int(0)),
                        )));
                        if success != nonzero {
                            return Err(
                                "constructor assertion condition does not check the actual divisor",
                            );
                        }
                        operations.push((target.id, index));
                    }
                }
                if operations.is_empty() {
                    return Err("constructor assertion has no matching guarded division/remainder");
                }
                (success, span.clone(), format_assert_message(msg), operations)
            }
            Terminator::Call { func, target: None, span, atomic: None, .. }
                if is_panic_call(func) =>
            {
                (
                    Formula::Bool(false),
                    span.clone(),
                    format!("panic call `{func}` must be unreachable"),
                    Vec::new(),
                )
            }
            _ => continue,
        };
        let guard = analyzer.guard(entry, block.id, &mut Vec::new())?;
        sites.push(BundledConstructorSafetySite {
            block: block.id,
            span,
            description,
            requirement: Formula::Implies(Box::new(guard), Box::new(success)),
            guarded_operations,
        });
    }
    Ok(sites)
}

/// Exact ordinary call sites to compose, never a callee-name set. Two sites
/// selecting one instance remain distinct and retain their actual arguments.
pub fn bundled_constructor_call_sites(
    function: &VerifiableFunction,
) -> Result<Vec<BundledConstructorCallSite>, &'static str> {
    let analyzer = Analyzer { function, guard_cache: Default::default() };
    analyzer.validate_cfg()?;
    let entry = function.body.blocks.first().ok_or("constructor body is empty")?.id;
    let mut calls = Vec::new();
    for block in &function.body.blocks {
        match &block.terminator {
            Terminator::Call { func, target: None, atomic: None, .. } if is_panic_call(func) => {}
            Terminator::Call {
                func,
                args,
                span,
                callee_identity,
                atomic: None,
                target: Some(_),
                ..
            } => {
                calls.push(BundledConstructorCallSite {
                    block: block.id,
                    span: span.clone(),
                    callee: func.clone(),
                    identity: callee_identity.ok_or("constructor call has no concrete identity")?,
                    arguments: args.clone(),
                    guard: analyzer.guard(entry, block.id, &mut Vec::new())?,
                });
            }
            Terminator::Call { .. } | Terminator::TailCall { .. } => {
                return Err("unsupported constructor call effect");
            }
            _ => {}
        }
    }
    Ok(calls)
}

/// Substitute a child's LOCAL requirement through this exact call site and
/// retain its parent's reachability guard. Only the small scalar grammar the
/// local analyzer produces is accepted; an unbound name or wrong argument sort
/// cannot survive into the caller as a fresh symbolic value.
pub fn bundled_constructor_rebind_requirement(
    caller: &VerifiableFunction,
    call: &BundledConstructorCallSite,
    callee: &VerifiableFunction,
    requirement: &Formula,
) -> Result<Formula, &'static str> {
    let current_calls = bundled_constructor_call_sites(caller)?;
    let actual = current_calls
        .iter()
        .find(|actual| actual.block == call.block)
        .ok_or("constructor call site is absent from the current caller")?;
    if serde_json::to_value(actual).map_err(|_| "constructor call serialization failed")?
        != serde_json::to_value(call).map_err(|_| "constructor call serialization failed")?
    {
        return Err("constructor call site differs from the current source");
    }
    if call.callee != callee.name || call.callee != callee.def_path {
        return Err("constructor call does not name the exact member body");
    }
    if call.arguments.len() != callee.body.arg_count {
        return Err("constructor call argument arity mismatch");
    }
    let analyzer = Analyzer { function: caller, guard_cache: Default::default() };
    let block = analyzer.block(call.block)?;
    let formals = bundled_constructor_formal_names(callee);
    fn replace(
        analyzer: &Analyzer<'_>,
        block: &TrustBlock,
        formals: &[String],
        arguments: &[Operand],
        formula: &Formula,
    ) -> Result<Formula, &'static str> {
        let recurse = |formula| replace(analyzer, block, formals, arguments, formula);
        Ok(match formula {
            Formula::Bool(_) | Formula::Int(_) => formula.clone(),
            Formula::Var(name, sort @ (Sort::Int | Sort::Bool)) => {
                let positions: Vec<_> = formals
                    .iter()
                    .enumerate()
                    .filter(|(_, formal)| *formal == name)
                    .map(|(index, _)| index)
                    .collect();
                let [index] = positions.as_slice() else {
                    return Err("unbound or ambiguous constructor formal");
                };
                let actual =
                    analyzer.operand(&arguments[*index], block.id, block.stmts.len(), 8)?;
                let actual_sort = match &actual {
                    Formula::Int(_) => Sort::Int,
                    Formula::Var(_, sort) => sort.clone(),
                    Formula::Bool(_) | Formula::Eq(..) | Formula::Not(..) => Sort::Bool,
                    _ => return Err("unsupported constructor actual expression"),
                };
                if &actual_sort != sort {
                    return Err("constructor actual/formal sort mismatch");
                }
                actual
            }
            Formula::Not(inner) => Formula::Not(Box::new(recurse(inner)?)),
            Formula::Eq(left, right) => {
                Formula::Eq(Box::new(recurse(left)?), Box::new(recurse(right)?))
            }
            Formula::Implies(left, right) => {
                Formula::Implies(Box::new(recurse(left)?), Box::new(recurse(right)?))
            }
            Formula::And(items) => {
                Formula::And(items.iter().map(recurse).collect::<Result<_, _>>()?)
            }
            Formula::Or(items) => Formula::Or(items.iter().map(recurse).collect::<Result<_, _>>()?),
            _ => return Err("unsupported constructor requirement grammar"),
        })
    }
    let rebound = replace(&analyzer, block, &formals, &call.arguments, requirement)?;
    Ok(Formula::Implies(Box::new(call.guard.clone()), Box::new(rebound)))
}
