//! Exact source-query to generated postcondition correspondence.
//!
//! This establishes a translation relation, not a proof. A caller must still
//! independently check every returned body VC's certificate. The current
//! Boolean admission reconstructs exact bounded scalar/nominal-enum entry
//! domains and type-validity premises. Nominal arguments acquire no invented
//! scalar source binders. Unsigned call bodies reuse the bounded scalar return
//! evaluator; canonical unsigned selects retain their shared recognizer.
//! These relations grant no proof authority or additional caller assumptions.

use super::*;

/// A complete, unambiguous group of generated VCs for one authored clause.
/// Construction requires the original typed function and compiler query.
#[derive(Debug, Clone)]
pub struct ExactEnsuresBodyGroup {
    source_contract_index: usize,
    body_indices: Vec<usize>,
}

impl ExactEnsuresBodyGroup {
    #[must_use]
    pub fn source_contract_index(&self) -> usize {
        self.source_contract_index
    }

    /// Indices into the supplied VC carrier, including every return obligation.
    #[must_use]
    pub fn body_indices(&self) -> &[usize] {
        &self.body_indices
    }
}

/// Reconstruct the production VC group from the exact typed source/query pair.
/// No row ID, suffix, result label, or caller-supplied count establishes this
/// relation. Raw and interval-augmented production VCs use the existing unique
/// bijection checker; unsupported reconstruction fails closed.
#[must_use]
pub fn exact_boolean_ensures_body_group(
    function: &VerifiableFunction,
    compiler_contracts: &CompilerContractBundle,
    source_contract_index: usize,
    supplied_vcs: &[VerificationCondition],
    target_pointer_width_bits: Option<u32>,
) -> Option<ExactEnsuresBodyGroup> {
    exact_boolean_ensures_body_group_inner(
        function,
        compiler_contracts,
        source_contract_index,
        supplied_vcs,
        target_pointer_width_bits,
        None,
    )
}

/// The same exact relation with explicit candidate-only inferred call inputs.
/// Callers must validate their original-body proof DAG before spending this
/// relation. This function itself never returns a proof or raises a grade.
#[must_use]
pub fn exact_boolean_ensures_body_group_with_inferred_calls(
    function: &VerifiableFunction,
    compiler_contracts: &CompilerContractBundle,
    source_contract_index: usize,
    supplied_vcs: &[VerificationCondition],
    target_pointer_width_bits: Option<u32>,
    callees: &[trust_vcgen::InferredReturnCall],
) -> Option<ExactEnsuresBodyGroup> {
    exact_boolean_ensures_body_group_inner(
        function,
        compiler_contracts,
        source_contract_index,
        supplied_vcs,
        target_pointer_width_bits,
        Some(callees),
    )
}

/// Select the one supported source/body relation for checked replay.
///
/// `Some` denotes an inferred-return graph, even when its caller input slice
/// is empty. Both Boolean and bounded unsigned returns use the shared typed
/// call relation. Every original callee proof must independently replay; the
/// unsigned branch additionally binds the complete authored-clause VC carrier.
#[must_use]
pub fn exact_ensures_body_group(
    function: &VerifiableFunction,
    compiler_contracts: &CompilerContractBundle,
    source_contract_index: usize,
    supplied_vcs: &[VerificationCondition],
    target_pointer_width_bits: Option<u32>,
    inferred_calls: Option<&[trust_vcgen::InferredReturnCall]>,
) -> Option<ExactEnsuresBodyGroup> {
    if function.body.return_ty == Ty::Bool {
        return exact_boolean_ensures_body_group_inner(
            function,
            compiler_contracts,
            source_contract_index,
            supplied_vcs,
            target_pointer_width_bits,
            inferred_calls,
        );
    }
    if let Some(callees) = inferred_calls {
        let domains = trust_vcgen::scalar_return_source_entry_domains(function, Some(callees))?;
        return exact_ensures_body_group_for_domains(
            function,
            compiler_contracts,
            source_contract_index,
            supplied_vcs,
            target_pointer_width_bits,
            Some(callees),
            &domains,
            true,
        );
    }
    exact_unsigned_select_ensures_body_group(
        function,
        compiler_contracts,
        source_contract_index,
        supplied_vcs,
        target_pointer_width_bits,
    )
    .or_else(|| {
        exact_unsigned_straight_line_ensures_body_group(
            function,
            compiler_contracts,
            source_contract_index,
            supplied_vcs,
            target_pointer_width_bits,
        )
    })
}

/// Exact conditional source/body correspondence for unsigned scalar arithmetic.
///
/// The retained compiler query must account for every authored Requires and
/// Ensures, and the remaining premises must be exactly the argument type
/// ranges. The body is a single finite chain of pure assignments/asserts; no
/// call model, loop invariant, memory effect or inferred-return premise enters
/// this fragment. The production generator must reconstruct a bijection for
/// every authored Ensures, including all return obligations. This is trusted
/// translation correspondence, not proof: each selected original body goal
/// still requires its own independently replayed kernel certificate, and the
/// Requires remain explicit conditional context rather than proof credit.
#[must_use]
pub fn exact_unsigned_straight_line_ensures_body_group(
    function: &VerifiableFunction,
    compiler_contracts: &CompilerContractBundle,
    source_contract_index: usize,
    supplied_vcs: &[VerificationCondition],
    target_pointer_width_bits: Option<u32>,
) -> Option<ExactEnsuresBodyGroup> {
    use trust_types::CompilerContractValueDomain as Domain;

    let domain_for = |ty: &Ty| match ty {
        Ty::Int { width, signed: false } if matches!(*width, 8 | 16 | 32 | 64) => {
            Some(Domain::MachineInt { width: *width, signed: false })
        }
        _ => None,
    };
    let result_domain = domain_for(&function.body.return_ty)?;
    let mut result_locals = function.body.locals.iter().filter(|local| local.index == 0);
    let result_local = result_locals.next()?;
    if result_locals.next().is_some() || result_local.ty != function.body.return_ty {
        return None;
    }
    if function.contracts != compiler_contracts.contracts
        || function.contracts.is_empty()
        || !compiler_contracts.loop_contracts.is_empty()
        || !compiler_contracts.proof_items.is_empty()
        || compiler_contracts.loop_clause_source_locals.is_some()
        || compiler_contracts.typed_propositions.len() != function.contracts.len()
        || !unsigned_pure_straight_line(function)
        || supplied_vcs.iter().any(|vc| vc.kind.declined_contract_body().is_some())
    {
        return None;
    }
    let mut domains = BTreeMap::from([("_0".to_string(), result_domain)]);
    let mut ranges = Vec::new();
    for index in 1..=function.body.arg_count {
        let mut locals = function.body.locals.iter().filter(|local| local.index == index);
        let local = locals.next()?;
        if locals.next().is_some() || local.name.is_none() {
            return None;
        }
        let domain = domain_for(&local.ty)?;
        let Domain::MachineInt { width, .. } = domain else { return None };
        let name = trust_vcgen::local_var_name(function, local);
        if domains.insert(name.clone(), domain).is_some() {
            return None;
        }
        let var = || Box::new(Formula::Var(name.clone(), Sort::Int));
        ranges.push(Formula::And(vec![
            Formula::Ge(var(), Box::new(Formula::Int(0))),
            Formula::Le(
                var(),
                Box::new(Formula::Int(i128::from(trust_intbound::unsigned_max(width)))),
            ),
        ]));
    }
    let mut requires = Vec::new();
    let mut ensures = Vec::new();
    let mut ensure_indices = Vec::new();
    for (index, contract) in function.contracts.iter().enumerate() {
        let proposition = compiler_contracts.typed_proposition(index, contract)?;
        if proposition.variable_domains.iter().any(|variable| {
            domains.get(&variable.name) != Some(&variable.domain)
                || (contract.kind == TrustTypesContractKind::Requires && variable.name == "_0")
        }) {
            return None;
        }
        match contract.kind {
            TrustTypesContractKind::Requires => requires.push(proposition.formula.clone()),
            TrustTypesContractKind::Ensures => {
                ensures.push(proposition.formula.clone());
                ensure_indices.push(index);
            }
            _ => return None,
        }
    }
    requires.extend(ranges);
    if function.preconditions != requires
        || function.postconditions != ensures
        || !ensure_indices.contains(&source_contract_index)
    {
        return None;
    }
    let (raw, augmented) = trust_vcgen::regenerate_postcondition_production_variants(function)?;
    for index in ensure_indices {
        if !exact_fresh_source_role_rows_match(
            function,
            compiler_contracts,
            supplied_vcs,
            index,
            "postcondition",
            &raw,
            &augmented,
            target_pointer_width_bits,
        ) {
            return None;
        }
    }
    let body_indices = supplied_vcs
        .iter()
        .enumerate()
        .filter_map(|(index, vc)| {
            let (bound_index, role) =
                validated_vc_source_contract_index_and_role(function, compiler_contracts, vc)?;
            (bound_index == source_contract_index && role == "postcondition").then_some(index)
        })
        .collect();
    Some(ExactEnsuresBodyGroup { source_contract_index, body_indices })
}

fn unsigned_pure_straight_line(function: &VerifiableFunction) -> bool {
    let blocks = &function.body.blocks;
    if blocks.is_empty() || blocks.len() > 1024 {
        return false;
    }
    let by_id = blocks
        .iter()
        .map(|block| (block.id.0, block))
        .collect::<trust_types::fx::FxHashMap<_, _>>();
    if by_id.len() != blocks.len() {
        return false;
    }
    let mut visited =
        trust_types::fx::FxHashSet::with_capacity_and_hasher(blocks.len(), Default::default());
    let mut next = trust_types::BlockId(0);
    loop {
        let Some(&block) = by_id.get(&next.0) else { return false };
        if !visited.insert(next.0)
            || block.stmts.iter().any(|statement| match statement {
                Statement::Assign { place, rvalue, .. } => {
                    if !pure_scalar_place(function, place) {
                        return true;
                    }
                    match rvalue {
                        Rvalue::Use(value) | Rvalue::UnaryOp(_, value) => {
                            !pure_scalar_operand(function, value)
                        }
                        Rvalue::BinaryOp(_, lhs, rhs) | Rvalue::CheckedBinaryOp(_, lhs, rhs) => {
                            !pure_scalar_operand(function, lhs)
                                || !pure_scalar_operand(function, rhs)
                        }
                        _ => true,
                    }
                }
                Statement::StorageLive(_) | Statement::StorageDead(_) | Statement::Nop => false,
                _ => true,
            })
        {
            return false;
        }
        next = match &block.terminator {
            Terminator::Goto(next) => *next,
            Terminator::Assert { cond, target, .. } if pure_scalar_operand(function, cond) => {
                *target
            }
            Terminator::Return => return visited.len() == blocks.len(),
            _ => return false,
        };
    }
}

fn pure_scalar_operand(function: &VerifiableFunction, operand: &Operand) -> bool {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => pure_scalar_place(function, place),
        Operand::Constant(trust_types::ConstValue::Bool(_)) => true,
        Operand::Constant(trust_types::ConstValue::Uint(value, width)) => {
            matches!(*width, 8 | 16 | 32 | 64)
                && *value <= u128::from(trust_intbound::unsigned_max(*width))
        }
        _ => false,
    }
}

fn pure_scalar_place(function: &VerifiableFunction, place: &Place) -> bool {
    let mut locals = function.body.locals.iter().filter(|local| local.index == place.local);
    let Some(local) = locals.next() else { return false };
    if locals.next().is_some() {
        return false;
    }
    let mut ty = &local.ty;
    for projection in &place.projections {
        let (Projection::Field(index), Ty::Tuple(fields)) = (projection, ty) else { return false };
        let Some(field) = fields.get(*index) else { return false };
        ty = field;
    }
    let scalar = |ty: &Ty| matches!(ty, Ty::Bool | Ty::Int { width: 8 | 16 | 32 | 64, .. });
    scalar(ty) || matches!(ty, Ty::Tuple(fields) if fields.iter().all(scalar))
}

fn exact_boolean_ensures_body_group_inner(
    function: &VerifiableFunction,
    compiler_contracts: &CompilerContractBundle,
    source_contract_index: usize,
    supplied_vcs: &[VerificationCondition],
    target_pointer_width_bits: Option<u32>,
    callees: Option<&[trust_vcgen::InferredReturnCall]>,
) -> Option<ExactEnsuresBodyGroup> {
    let domains = trust_vcgen::boolean_source_entry_domains(function, callees)?;
    exact_ensures_body_group_for_domains(
        function,
        compiler_contracts,
        source_contract_index,
        supplied_vcs,
        target_pointer_width_bits,
        callees,
        &domains,
        false,
    )
}

/// Exact source/body correspondence for a canonical unsigned scalar select.
///
/// Uses the existing shared select recognizer, never a second MIR decoder.
/// Arguments and result must share one fixed width (8/16/32/64), clauses must
/// compare bare scalar values, and the only premises are the exact full type
/// ranges of the arguments. Arithmetic, calls, loops, signed/pointer-sized
/// types, and additional caller assumptions remain outside this fragment.
/// Every supplied body row and every authored clause must participate in the
/// original generator's complete raw/interval-augmented bijection. Returned
/// indices still require independently checked certificates; this is no proof.
#[must_use]
pub fn exact_unsigned_select_ensures_body_group(
    function: &VerifiableFunction,
    compiler_contracts: &CompilerContractBundle,
    source_contract_index: usize,
    supplied_vcs: &[VerificationCondition],
    target_pointer_width_bits: Option<u32>,
) -> Option<ExactEnsuresBodyGroup> {
    use trust_types::CompilerContractValueDomain as Domain;

    let Ty::Int { width, signed: false } = function.body.return_ty else { return None };
    if !matches!(width, 8 | 16 | 32 | 64)
        || !function.spec.requires.is_empty()
        || !function.spec.invariants.is_empty()
    {
        return None;
    }
    trust_types::admissible_body::recognize_unsigned_ordered_select(function)?;
    let domain = Domain::MachineInt { width, signed: false };
    let mut domains = BTreeMap::from([("_0".to_string(), domain)]);
    let mut ranges = Vec::new();
    for arg in function
        .body
        .locals
        .iter()
        .filter(|arg| arg.index > 0 && arg.index <= function.body.arg_count)
    {
        if arg.ty != function.body.return_ty || arg.name.is_none() {
            return None;
        }
        let name = trust_vcgen::local_var_name(function, arg);
        if domains.insert(name.clone(), domain).is_some() {
            return None;
        }
        let var = || Box::new(Formula::Var(name.clone(), Sort::Int));
        ranges.push(Formula::And(vec![
            Formula::Ge(var(), Box::new(Formula::Int(0))),
            Formula::Le(
                var(),
                Box::new(Formula::Int(i128::from(trust_intbound::unsigned_max(width)))),
            ),
        ]));
    }
    if domains.len() != function.body.arg_count.checked_add(1)?
        || function.preconditions != ranges
        || function
            .postconditions
            .iter()
            .any(|formula| !unsigned_scalar_comparison(formula, &domains, width))
    {
        return None;
    }
    exact_ensures_body_group_for_domains(
        function,
        compiler_contracts,
        source_contract_index,
        supplied_vcs,
        target_pointer_width_bits,
        None,
        &domains,
        true,
    )
}

fn unsigned_scalar_comparison(
    formula: &Formula,
    domains: &BTreeMap<String, trust_types::CompilerContractValueDomain>,
    width: u32,
) -> bool {
    let value = |formula: &Formula| match formula {
        Formula::Var(name, Sort::Int) => domains.contains_key(name),
        Formula::Int(value) => {
            *value >= 0 && *value <= i128::from(trust_intbound::unsigned_max(width))
        }
        _ => false,
    };
    match formula {
        Formula::Eq(lhs, rhs)
        | Formula::Lt(lhs, rhs)
        | Formula::Le(lhs, rhs)
        | Formula::Gt(lhs, rhs)
        | Formula::Ge(lhs, rhs) => value(lhs) && value(rhs),
        _ => false,
    }
}

fn exact_ensures_body_group_for_domains(
    function: &VerifiableFunction,
    compiler_contracts: &CompilerContractBundle,
    source_contract_index: usize,
    supplied_vcs: &[VerificationCondition],
    target_pointer_width_bits: Option<u32>,
    callees: Option<&[trust_vcgen::InferredReturnCall]>,
    domains: &BTreeMap<String, trust_types::CompilerContractValueDomain>,
    require_complete_carrier: bool,
) -> Option<ExactEnsuresBodyGroup> {
    if function.contracts != compiler_contracts.contracts
        || function.contracts.is_empty()
        || !compiler_contracts.loop_contracts.is_empty()
        || !compiler_contracts.proof_items.is_empty()
        || compiler_contracts.loop_clause_source_locals.is_some()
        || compiler_contracts.typed_propositions.len() != function.contracts.len()
        || function.postconditions.len() != function.contracts.len()
    {
        return None;
    }
    // The generator consumes function.postconditions. Bind EACH of those to
    // the compiler's exact typed clause, not merely the selected row, so a
    // changed unselected clause cannot supply new hypotheses or alter indices.
    for (index, contract) in function.contracts.iter().enumerate() {
        if contract.kind != TrustTypesContractKind::Ensures {
            return None;
        }
        let proposition = compiler_contracts.typed_proposition(index, contract)?;
        if proposition
            .variable_domains
            .iter()
            .any(|variable| domains.get(&variable.name) != Some(&variable.domain))
            || proposition.formula != function.postconditions[index]
            || !matches!(trust_types::check_formula_sort(&proposition.formula), Ok(Sort::Bool))
        {
            return None;
        }
    }
    compiler_contracts.contracts.get(source_contract_index)?;
    let (raw, augmented) = match callees {
        None => trust_vcgen::regenerate_postcondition_production_variants(function)?,
        Some(callees) => {
            trust_vcgen::regenerate_postcondition_production_variants_with_inferred_calls(
                function, callees,
            )?
        }
    };
    let indices = if require_complete_carrier {
        for vc in supplied_vcs {
            let (bound_index, role) =
                validated_vc_source_contract_index_and_role(function, compiler_contracts, vc)?;
            if role != "postcondition" || bound_index >= function.contracts.len() {
                return None;
            }
        }
        0..function.contracts.len()
    } else {
        source_contract_index..source_contract_index.checked_add(1)?
    };
    for index in indices {
        if !exact_fresh_source_role_rows_match(
            function,
            compiler_contracts,
            supplied_vcs,
            index,
            "postcondition",
            &raw,
            &augmented,
            target_pointer_width_bits,
        ) {
            return None;
        }
    }
    let body_indices = supplied_vcs
        .iter()
        .enumerate()
        .filter_map(|(index, vc)| {
            let (bound_index, role) =
                validated_vc_source_contract_index_and_role(function, compiler_contracts, vc)?;
            (bound_index == source_contract_index && role == "postcondition").then_some(index)
        })
        .collect();
    Some(ExactEnsuresBodyGroup { source_contract_index, body_indices })
}

/// Compare a retained public row with the original typed producer result.
/// Native routing may append metadata; it may not replace any original field
/// or duplicate/alter a producer metadata entry. This grants no proof authority.
#[must_use]
pub fn public_obligation_preserves_source(
    expected: &TrustObligation,
    actual: &TrustObligation,
) -> bool {
    let TrustObligation {
        obligation_id,
        kind,
        contract_id,
        proof_item_id,
        source,
        description,
        required_strength,
        summary_facts,
        metadata,
    } = expected;
    actual.obligation_id == *obligation_id
        && actual.kind == *kind
        && actual.contract_id == *contract_id
        && actual.proof_item_id == *proof_item_id
        && actual.source == *source
        && actual.description == *description
        && actual.required_strength == *required_strength
        && actual.summary_facts == *summary_facts
        && metadata_preserves(metadata, &actual.metadata)
}

#[must_use]
pub fn public_contract_preserves_source(expected: &TrustContract, actual: &TrustContract) -> bool {
    let TrustContract { contract_id, kind, predicate, source, metadata } = expected;
    actual.contract_id == *contract_id
        && actual.kind == *kind
        && actual.predicate == *predicate
        && actual.source == *source
        && metadata_preserves(metadata, &actual.metadata)
}

fn metadata_preserves(expected: &[MetadataEntry], actual: &[MetadataEntry]) -> bool {
    expected.iter().all(|entry| {
        let mut matching = actual.iter().filter(|other| other.key == entry.key);
        matching.next() == Some(entry) && matching.next().is_none()
    })
}

/// Canonical identity of one exact compiler-query clause in the typed function.
#[must_use]
pub fn verifier_source_contract_id(
    function: &VerifiableFunction,
    contracts: &CompilerContractBundle,
    index: usize,
) -> Option<String> {
    Some(contract_id(function, index, canonical_source_contract(function, contracts, index)?))
}

/// Accounting row for a raw authored ensures clause. The Boolean is a
/// placeholder, never a proof goal; only a checked source/body relation may
/// discharge it. Both the compiler and certificate replay use this constructor.
#[must_use]
pub fn boolean_ensures_source_marker(
    function: &VerifiableFunction,
    index: usize,
) -> Option<VerificationCondition> {
    let contract = function.contracts.get(index)?;
    if contract.kind != TrustTypesContractKind::Ensures {
        return None;
    }
    Some(VerificationCondition {
        kind: VcKind::Postcondition,
        function: trust_types::Symbol::intern(&function.def_path),
        location: contract.span.clone(),
        formula: Formula::Bool(false),
        contract_metadata: None,
        obligation: None,
    })
}
