// Copyright 2026 Andrew Yates. SPDX-License-Identifier: Apache-2.0 OR MIT.
//! Candidate-only evaluation of bounded pure enum bodies. Its expression has
//! no authority until EVERY check over the unchanged original body certifies.

use super::entry_bindings::{EntryAccess, EntryRead};
use super::*;

#[derive(Clone, PartialEq)]
enum Value {
    Scalar(Formula),
    EntryEnum(usize),
    Tuple(Vec<Value>),
}

impl Value {
    fn within_budget(&self) -> bool {
        let mut pending = vec![self];
        let mut nodes = 0usize;
        while let Some(value) = pending.pop() {
            match value {
                Self::Scalar(formula) => {
                    if trust_types::any_formula_node(formula, &mut |_| {
                        nodes += 1;
                        nodes > INFERRED_RETURN_MAX_NODES
                    }) {
                        return false;
                    }
                }
                Self::EntryEnum(_) => nodes += 1,
                Self::Tuple(fields) => {
                    nodes += 1;
                    pending.extend(fields);
                }
            }
            if nodes > INFERRED_RETURN_MAX_NODES {
                return false;
            }
        }
        true
    }
}

struct Exec<'a> {
    function: &'a VerifiableFunction,
    visits: usize,
    case_visits: usize,
    completed: Vec<(BlockId, Vec<Option<Value>>, Formula)>,
}

impl Exec<'_> {
    fn place(&self, env: &[Option<Value>], place: &Place) -> Result<Value, &'static str> {
        let mut value = env.get(place.local).cloned().flatten().ok_or("read before write")?;
        let mut projections = &place.projections[..];
        while let Some((projection, remaining)) = projections.split_first() {
            match (value, projection) {
                (Value::Tuple(fields), Projection::Field(index)) => {
                    value = fields.get(*index).cloned().ok_or("tuple field out of range")?;
                    projections = remaining;
                }
                (Value::EntryEnum(local), _) => {
                    let entry = Place { local, projections: projections.to_vec() };
                    // The shared typed origin model validates the full enum
                    // descriptor, variant, field and width; no name is parsed.
                    if crate::enum_entry::origin(self.function, &entry).as_ref() != Some(&entry) {
                        return Err("invalid entry enum projection");
                    }
                    let ty =
                        crate::place_ty_cow(self.function, &entry).ok_or("untyped enum field")?;
                    if !fragment_scalar(&ty) {
                        return Err("non-scalar enum payload");
                    }
                    return Ok(Value::Scalar(operand_to_formula(
                        self.function,
                        &Operand::Copy(entry),
                    )));
                }
                _ => return Err("projection outside the enum fragment"),
            }
        }
        Ok(value)
    }

    fn operand(&self, env: &[Option<Value>], operand: &Operand) -> Result<Value, &'static str> {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => self.place(env, place),
            Operand::Constant(ConstValue::Bool(_) | ConstValue::Int(_) | ConstValue::Uint(..)) => {
                match operand_to_formula(self.function, operand) {
                    value @ (Formula::Bool(_) | Formula::Int(_)) => Ok(Value::Scalar(value)),
                    _ => Err("constant outside Int/Bool"),
                }
            }
            _ => Err("operand outside the enum fragment"),
        }
    }

    fn scalar(&self, env: &[Option<Value>], operand: &Operand) -> Result<Formula, &'static str> {
        match self.operand(env, operand)? {
            Value::Scalar(value) => Ok(value),
            _ => Err("aggregate used as a scalar"),
        }
    }

    fn read_as(
        &self,
        env: &[Option<Value>],
        operand: &Operand,
        wanted: &Ty,
    ) -> Result<Value, &'static str> {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => {
                if crate::place_ty_cow(self.function, place).as_deref() != Some(wanted) {
                    return Err("operand type mismatch");
                }
            }
            Operand::Constant(constant) => {
                let valid = match (constant, wanted) {
                    (ConstValue::Bool(_), Ty::Bool) => true,
                    (ConstValue::Int(value), Ty::Int { .. }) => {
                        crate::enum_entry::tag_fits(wanted, *value)
                    }
                    (ConstValue::Uint(value, width), Ty::Int { width: expected, .. }) => {
                        width == expected
                            && i128::try_from(*value)
                                .is_ok_and(|value| crate::enum_entry::tag_fits(wanted, value))
                    }
                    _ => false,
                };
                if !valid {
                    return Err("constant type/width mismatch");
                }
            }
            _ => return Err("operand outside the enum fragment"),
        }
        self.operand(env, operand)
    }

    fn rvalue(
        &self,
        env: &[Option<Value>],
        value: &Rvalue,
        destination: &Ty,
    ) -> Result<Value, &'static str> {
        Ok(match value {
            Rvalue::Use(operand) => self.read_as(env, operand, destination)?,
            Rvalue::Aggregate(AggregateKind::Tuple, operands) => {
                let Ty::Tuple(fields) = destination else {
                    return Err("non-tuple aggregate destination");
                };
                if fields.len() != operands.len() {
                    return Err("tuple arity mismatch");
                }
                Value::Tuple(
                    operands
                        .iter()
                        .zip(fields)
                        .map(|(operand, ty)| self.read_as(env, operand, ty))
                        .collect::<Result<_, _>>()?,
                )
            }
            Rvalue::Discriminant(place) => {
                let Value::EntryEnum(local) = self.place(env, place)? else {
                    return Err("discriminant of a non-enum");
                };
                let Ty::Adt { variants, .. } =
                    local_ty(self.function, local).ok_or("missing entry declaration")?
                else {
                    return Err("untyped enum entry");
                };
                if variants
                    .iter()
                    .any(|variant| !crate::enum_entry::tag_fits(destination, variant.discriminant))
                {
                    return Err("discriminant width mismatch");
                }
                Value::Scalar(
                    crate::enum_entry::entry_discriminant(self.function, &Place::local(local))
                        .ok_or("invalid entry discriminator")?,
                )
            }
            Rvalue::UnaryOp(trust_types::UnOp::Not, operand) if *destination == Ty::Bool => {
                self.read_as(env, operand, &Ty::Bool)?;
                Value::Scalar(Formula::Not(Box::new(self.scalar(env, operand)?)))
            }
            Rvalue::BinaryOp(operator, lhs, rhs) if *destination == Ty::Bool => {
                let ty = [lhs, rhs]
                    .into_iter()
                    .find_map(|operand| match operand {
                        Operand::Copy(place) | Operand::Move(place) => {
                            crate::place_ty_cow(self.function, place)
                        }
                        _ => None,
                    })
                    .ok_or("binary operands have no declared type")?;
                self.read_as(env, lhs, &ty)?;
                self.read_as(env, rhs, &ty)?;
                let lhs = self.scalar(env, lhs)?;
                let rhs = self.scalar(env, rhs)?;
                let formula = match (ty.as_ref(), operator) {
                    (Ty::Int { width: 1..=64, .. }, _) => {
                        callee_summaries::comparison_formula(*operator, lhs, rhs)
                            .ok_or("integer arithmetic outside the fragment")?
                    }
                    (Ty::Bool, BinOp::Eq) => Formula::Eq(Box::new(lhs), Box::new(rhs)),
                    (Ty::Bool, BinOp::Ne | BinOp::BitXor) => {
                        Formula::Not(Box::new(Formula::Eq(Box::new(lhs), Box::new(rhs))))
                    }
                    (Ty::Bool, BinOp::BitAnd) => Formula::And(vec![lhs, rhs]),
                    (Ty::Bool, BinOp::BitOr) => Formula::Or(vec![lhs, rhs]),
                    _ => return Err("non-scalar comparison"),
                };
                Value::Scalar(formula)
            }
            _ => return Err("rvalue outside the enum fragment"),
        })
    }

    fn eval(&mut self, id: BlockId, env: Vec<Option<Value>>) -> Result<Formula, &'static str> {
        // Candidate evaluation is pure and the entire typed environment is the
        // input. Reuse only a completed result for this exact block AND state;
        // equal blocks reached with different values must still be evaluated.
        // No path hypothesis or proof authority is cached, and every original
        // body row still has to pass the independent kernel admission below.
        if let Some((_, _, value)) =
            self.completed.iter().find(|(block, state, _)| *block == id && *state == env)
        {
            return Ok(value.clone());
        }
        self.visits += 1;
        if self.visits > MAX_BLOCK_VISITS {
            return Err("path budget exceeded");
        }
        let state = env.clone();
        let value = self.eval_uncached(id, env)?;
        if node_count_exceeds(&value, INFERRED_RETURN_MAX_NODES) {
            return Err("inferred expression too large");
        }
        self.completed.push((id, state, value.clone()));
        Ok(value)
    }

    fn eval_uncached(
        &mut self,
        id: BlockId,
        mut env: Vec<Option<Value>>,
    ) -> Result<Formula, &'static str> {
        let block =
            self.function.body.blocks.iter().find(|block| block.id == id).ok_or("missing block")?;
        for statement in &block.stmts {
            match statement {
                Statement::StorageLive(_)
                | Statement::StorageDead(_)
                | Statement::Coverage
                | Statement::ConstEvalCounter
                | Statement::Nop => {}
                Statement::Assign { place, rvalue, .. }
                    if place.projections.is_empty()
                        && !(1..=self.function.body.arg_count).contains(&place.local) =>
                {
                    let ty = local_ty(self.function, place.local).ok_or("missing local type")?;
                    let value = self.rvalue(&env, rvalue, ty)?;
                    if !value.within_budget() {
                        return Err("inferred expression too large");
                    }
                    *env.get_mut(place.local).ok_or("invalid local index")? = Some(value);
                }
                _ => return Err("statement outside the enum fragment"),
            }
        }
        match &block.terminator {
            Terminator::Goto(next) => self.eval(*next, env),
            call @ Terminator::Call { dest, target: Some(next), .. } => {
                let callee = crate::inferred_return_call_for(self.function, call)
                    .ok_or("call has no exact checked return input")?;
                let value = callee.value_in_state(
                    self.function,
                    call,
                    env.iter().enumerate().filter_map(|(local, value)| {
                        let Some(Value::Scalar(value)) = value else { return None };
                        Some((local, value))
                    }),
                )?;
                *env.get_mut(dest.local).ok_or("invalid call destination")? =
                    Some(Value::Scalar(value));
                self.eval(*next, env)
            }
            Terminator::Return => match env.first().cloned().flatten() {
                Some(Value::Scalar(result)) => Ok(result),
                _ => Err("return before scalar result"),
            },
            // Proposal outside the source's valid enum domain is arbitrary.
            // The ORIGINAL Unreachable row remains mandatory kernel work;
            // this branch itself grants no evidence or reachability fact.
            Terminator::Unreachable => Ok(Formula::Bool(false)),
            Terminator::SwitchInt { discr, targets, otherwise, .. } => {
                let (Operand::Copy(place) | Operand::Move(place)) = discr else {
                    return Err("untyped switch");
                };
                let ty = crate::place_ty_cow(self.function, place).ok_or("missing switch type")?;
                let value = self.scalar(&env, discr)?;
                let mut result = if targets.is_empty() {
                    return self.eval(*otherwise, env);
                } else {
                    self.eval(*otherwise, env.clone())?
                };
                let mut seen = (targets.len() > 8).then(FxHashSet::default);
                let mut iter = targets.iter().enumerate().rev().peekable();
                while let Some((idx, (label, target))) = iter.next() {
                    // A memo hit saves evaluation, but a long switch still
                    // consumes work even when all labels have one result.
                    if self.case_visits == MAX_BLOCK_VISITS {
                        return Err("path budget exceeded");
                    }
                    self.case_visits += 1;
                    let dup = match &mut seen {
                        Some(set) => !set.insert(*label),
                        None => targets[idx + 1..].iter().any(|(prev, _)| prev == label),
                    };
                    if dup {
                        return Err("duplicate switch label");
                    }
                    let condition = match (ty.as_ref(), label) {
                        (Ty::Bool, 0) => Formula::Not(Box::new(value.clone())),
                        (Ty::Bool, 1) => value.clone(),
                        (Ty::Bool, _) => return Err("invalid boolean switch label"),
                        _ => Formula::Eq(
                            Box::new(value.clone()),
                            Box::new(
                                crate::switch_label_to_formula(&ty, *label)
                                    .ok_or("invalid switch label")?,
                            ),
                        ),
                    };
                    let branch_env =
                        if iter.peek().is_some() { env.clone() } else { std::mem::take(&mut env) };
                    let yes = self.eval(*target, branch_env)?;
                    result = if yes == result {
                        yes
                    } else {
                        match (&yes, &result) {
                            (Formula::Bool(true), Formula::Bool(false)) => condition,
                            (Formula::Bool(false), Formula::Bool(true)) => {
                                Formula::Not(Box::new(condition))
                            }
                            _ => Formula::Ite(Box::new(condition), Box::new(yes), Box::new(result)),
                        }
                    };
                    // A compact DAG can denote an exponentially large tree.
                    // Bound each construction before cloning/caching it again.
                    if node_count_exceeds(&result, INFERRED_RETURN_MAX_NODES) {
                        return Err("inferred expression too large");
                    }
                }
                Ok(result)
            }
            _ => Err("terminator outside the enum fragment"),
        }
    }
}

pub(super) fn infer(function: &VerifiableFunction) -> Result<InferredReturn, &'static str> {
    if !function.contracts.is_empty()
        || !function.postconditions.is_empty()
        || !function.spec.is_empty()
    {
        return Err("authored contract present");
    }
    // Like scalar D5-B, extracted entry hypotheses do not authorize the lemma:
    // original-body check generation clears ALL of them. Authored clauses are
    // separately refused through the typed contract/spec carriers above.
    let _analysis = crate::generate::FuncAnalysisScope::enter_if_unbound(function);
    if !crate::enum_entry::pure_body(function)
        || crate::generate::body_contains_memory_image_for(function)
    {
        return Err("body outside pure enum fragment");
    }
    crate::validate_function(function).map_err(|_| "malformed function")?;
    if function
        .body
        .blocks
        .iter()
        .filter(|block| matches!(block.terminator, Terminator::Return))
        .count()
        != 1
    {
        return Err("not exactly one Return block");
    }
    if !matches!(operand_to_formula(function, &Operand::Copy(Place::local(0))), Formula::Var(name, Sort::Bool) if name == "_0")
    {
        return Err("return slot does not render as `_0`");
    }
    if !acyclic_from(function, BlockId(0)) {
        return Err("cyclic control flow");
    }
    let mut env = vec![None; function.body.locals.len()];
    let mut parameters = Vec::new();
    let mut accesses = Vec::new();
    let mut domains = Vec::new();
    for local in 1..=function.body.arg_count {
        let ty = local_ty(function, local).ok_or("missing parameter")?;
        let Formula::Var(name, _) =
            operand_to_formula(function, &Operand::Copy(Place::local(local)))
        else {
            return Err("non-variable parameter");
        };
        parameters.push((name, ty.clone()));
        env[local] = Some(if crate::enum_entry::enum_shape(ty) {
            let Ty::Adt { fields, variants, .. } = ty else {
                return Err("missing enum descriptor");
            };
            let discriminator =
                crate::enum_entry::entry_discriminant(function, &Place::local(local))
                    .ok_or("missing typed entry discriminator")?;
            // The body is checked over valid enum values. Retain that exact
            // type domain in the checked clause so a caller/SAT screen cannot
            // mistake the proposal's arbitrary invalid-tag arm for an execution.
            // This conjunct receives every original-body kernel check too.
            domains.push(Formula::Or(
                variants
                    .iter()
                    .map(|variant| {
                        Formula::Eq(
                            Box::new(discriminator.clone()),
                            Box::new(Formula::Int(variant.discriminant)),
                        )
                    })
                    .collect(),
            ));
            let mut paths = Vec::new();
            if variants.iter().any(|variant| !variant.fields.is_empty()) {
                let Formula::Var(symbol, Sort::Int) =
                    crate::enum_entry::entry_discriminant(function, &Place::local(local))
                        .ok_or("missing entry discriminator")?
                else {
                    return Err("non-variable entry discriminator");
                };
                accesses.push(EntryAccess {
                    formal: local - 1,
                    read: EntryRead::Discriminant,
                    scalar_ty: fields.first().ok_or("missing tag descriptor")?.1.clone(),
                    symbol,
                });
            }
            for (variant, definition) in variants.iter().enumerate() {
                for field in 0..definition.fields.len() {
                    paths.push(vec![Projection::Downcast(variant), Projection::Field(field)]);
                }
            }
            for projections in paths {
                let place = Place { local, projections: projections.clone() };
                let scalar_ty = crate::place_ty(function, &place).ok_or("untyped entry access")?;
                accesses.push(EntryAccess {
                    formal: local - 1,
                    read: EntryRead::Projection(projections),
                    scalar_ty,
                    symbol: place_to_var_name(function, &place),
                });
            }
            Value::EntryEnum(local)
        } else if fragment_scalar(ty) {
            Value::Scalar(operand_to_formula(function, &Operand::Copy(Place::local(local))))
        } else {
            return Err("parameter outside enum/scalar fragment");
        });
    }
    let mut execution = Exec { function, visits: 0, case_visits: 0, completed: Vec::new() };
    let value = execution.eval(BlockId(0), env)?;
    if node_count_exceeds(&value, INFERRED_RETURN_MAX_NODES) {
        return Err("inferred expression too large");
    }
    let mut names: FxHashSet<&str> =
        FxHashSet::with_capacity_and_hasher(parameters.len() + accesses.len(), Default::default());
    for (name, _) in &parameters {
        if name == "_0" || !names.insert(name.as_str()) {
            return Err("ambiguous entry spelling");
        }
    }
    for access in &accesses {
        if access.symbol == "_0" || !names.insert(access.symbol.as_str()) {
            return Err("ambiguous entry spelling");
        }
    }
    if !trust_types::all_free_variable_names(&value, &mut |name| names.contains(name)) {
        return Err("ambiguous entry spelling");
    }
    domains.push(Formula::Eq(Box::new(Formula::Var("_0".into(), Sort::Bool)), Box::new(value)));
    let postcondition = Formula::And(domains);
    if node_count_exceeds(&postcondition, INFERRED_RETURN_MAX_NODES) {
        return Err("checked enum expression too large");
    }
    let check_vcs = inferred_enum_return_check_vcs(function, &postcondition)?;
    Ok(InferredReturn {
        def_path: function.def_path.clone(),
        param_names: parameters.iter().map(|(name, _)| name.clone()).collect(),
        postcondition: postcondition.clone(),
        check_vcs,
        entry_bindings: Some(EntryBindings {
            return_ty: Ty::Bool,
            parameters,
            accesses,
            postcondition,
            def_path: function.def_path.clone(),
        }),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn resource_input() -> VerifiableFunction {
        // Synthetic acyclic stress graph over the captured typed enum. Its
        // 32 blocks denote a multi-million-node tree if shared results expand.
        serde_json::from_str(include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/tests/fixtures/d5b_shared_dag_resource.json"
        )))
        .unwrap()
    }

    fn evaluate(function: &VerifiableFunction) -> (Result<Formula, &'static str>, Exec<'_>) {
        assert!(crate::enum_entry::pure_body(function));
        assert!(acyclic_from(function, BlockId(0)));
        let mut env = vec![None; function.body.locals.len()];
        env[1] = Some(Value::EntryEnum(1));
        env[2] = Some(Value::Scalar(operand_to_formula(function, &Operand::Copy(Place::local(2)))));
        let mut execution = Exec { function, visits: 0, case_visits: 0, completed: Vec::new() };
        let result = execution.eval(BlockId(0), env);
        (result, execution)
    }

    #[test]
    fn enum_memo_refuses_shared_dag_before_materializing_its_large_result() {
        let function = resource_input();
        let (result, execution) = evaluate(&function);
        assert!(result.is_err(), "a shared CFG must not return its expanded candidate tree");
        assert!(
            execution
                .completed
                .iter()
                .all(|(_, _, value)| { node_count(value) <= INFERRED_RETURN_MAX_NODES })
        );
    }

    #[test]
    fn enum_memo_still_bounds_repeated_switch_labels() {
        let mut function = resource_input();
        function.body.locals[2].ty = Ty::Int { width: 64, signed: true };
        function.body.blocks[0].terminator = Terminator::SwitchInt {
            discr: Operand::Copy(Place::local(2)),
            targets: (0..10_000).map(|label| (label, BlockId(30))).collect(),
            otherwise: BlockId(30),
            exhaustive_enum_unreachable: false,
            span: function.span.clone(),
        };
        let (result, execution) = evaluate(&function);
        assert!(result.is_err(), "equal cached results cannot make switch work unbounded");
        assert_eq!(execution.case_visits, MAX_BLOCK_VISITS);
    }
}
