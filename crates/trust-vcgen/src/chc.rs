// trust_vcgen/chc.rs: Constrained Horn Clause encoding for loop invariant inference
//
// Encodes MIR loops as CHC systems for ay's Spacer engine. Each loop header
// becomes an uninterpreted predicate, each path through the loop body becomes
// a Horn clause. Spacer solves for the predicate interpretations, yielding
// loop invariants.
//
// CHC system structure for a simple loop `while cond { body }`:
//   Entry:     pre(vars) => inv(vars_init)
//   Inductive: inv(vars) /\ cond /\ body_constraint => inv(vars')
//   Exit:      inv(vars) /\ !cond => post(vars)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashSet;
use trust_types::*;

pub use crate::loop_analysis::{LoopInfo, detect_loops};
use crate::u128_to_formula;

/// Namespace CHC-owned theory variables away from legal source identifiers.
/// CHC formulas can contain both source locals and these derived symbols, so
/// cosmetic names such as `ref_x` or `x_init` are not collision-safe.
fn generated_chc_symbol(unqualified: &str) -> String {
    crate::generated_formula_symbol("chc", unqualified)
}

fn chc_local_decl(func: &VerifiableFunction, local: usize) -> Option<&LocalDecl> {
    let mut matches = func.body.locals.iter().filter(|decl| decl.index == local);
    let found = matches.next()?;
    matches.next().is_none().then_some(found)
}

fn chc_local_name(func: &VerifiableFunction, local: usize) -> String {
    if func.body.locals.iter().enumerate().all(|(position, decl)| decl.index == position)
        && local < func.body.locals.len()
    {
        // Share the VC generator's collision-safe local vocabulary. In
        // particular, two shadowed MIR locals must not collapse to one CHC
        // predicate parameter or transition equality.
        crate::place_to_var_name(func, &Place::local(local))
    } else {
        format!("_{local}")
    }
}

fn chc_block(func: &VerifiableFunction, block: usize) -> Option<&BasicBlock> {
    let mut matches = func.body.blocks.iter().filter(|candidate| candidate.id.0 == block);
    let found = matches.next()?;
    // Duplicate block identifiers make every edge lookup ambiguous.  This lane
    // is proof-producing, so ambiguity is an applicability failure.
    matches.next().is_none().then_some(found)
}

fn validate_chc_function(func: &VerifiableFunction) -> Result<(), ChcError> {
    crate::validate_function(func).map_err(|error| ChcError::UnsupportedMir {
        kind: "MalformedTrustIr".to_string(),
        detail: error.to_string(),
    })
}

/// Errors arising from CHC encoding.
#[derive(Debug, Clone, thiserror::Error)]
pub enum ChcError {
    /// The function contains no loops to encode.
    #[error("no loops found in function `{function}`")]
    NoLoops { function: String },

    /// A loop has no induction variables, making CHC encoding impractical.
    #[error("loop at block {header} has no induction variables")]
    NoInductionVars { header: usize },

    /// The loop body could not be symbolically encoded.
    #[error("failed to encode loop body: {reason}")]
    EncodingFailed { reason: String },

    /// CHC lowering encountered MIR whose semantics are not modeled.
    #[error("unsupported MIR in CHC lowering: {kind}: {detail}")]
    UnsupportedMir { kind: String, detail: String },

    /// A source contract contains fixed-width arithmetic whose wrap/panic
    /// semantics are not represented by this legacy integer CHC lane.
    #[error(
        "unsupported fixed-width arithmetic in {contract_kind} #{contract_index} for function `{function}`"
    )]
    UnsupportedContractArithmetic {
        function: String,
        contract_kind: &'static str,
        contract_index: usize,
    },

    /// A relevant loop-body operation has fixed-width Rust semantics that the
    /// CHC transition relation cannot represent exactly.
    #[error(
        "unsupported fixed-width body arithmetic `{operation}` in function `{function}` at block {block}, statement {statement}: {detail}"
    )]
    UnsupportedBodyArithmetic {
        function: String,
        block: usize,
        statement: usize,
        operation: String,
        detail: String,
    },

    /// The legacy transition builder would strengthen a multi-path or
    /// multi-write loop by keeping only one update. Such a transition can
    /// false-prove both an exit postcondition and an added safety query.
    #[error(
        "loop {header} in function `{function}` is outside the faithful single-path, single-write CHC transition fragment"
    )]
    UnfaithfulLoopTransition { function: String, header: usize },
}

/// Reject source contract arithmetic before the legacy CHC lane can reinterpret
/// fixed-width Rust operations as mathematical-integer operations.
fn reject_unmodeled_contract_arithmetic(func: &VerifiableFunction) -> Result<(), ChcError> {
    for (contract_kind, formulas) in
        [("precondition", &func.preconditions), ("postcondition", &func.postconditions)]
    {
        for (contract_index, formula) in formulas.iter().enumerate() {
            if crate::contracts::formula_uses_unmodeled_machine_arithmetic_in_function(
                func, formula,
            ) {
                return Err(ChcError::UnsupportedContractArithmetic {
                    function: func.def_path.clone(),
                    contract_kind,
                    contract_index,
                });
            }
        }
    }
    Ok(())
}

/// The width and signed interpretation of a first-class machine integer.
/// `Ty::Char` deliberately stays out: Rust does not admit arithmetic on char.
fn machine_int_info(ty: &Ty) -> Option<(u32, bool)> {
    match ty {
        Ty::Int { width, signed } if (1..=128).contains(width) => Some((*width, *signed)),
        Ty::PtrSizedInt { signed } => Some((64, *signed)),
        // Lifted machine-register bodies use `Bv`; absent recovered signedness,
        // its faithful interpretation is the unsigned bit pattern.
        Ty::Bv(width) if (1..=128).contains(width) => Some((*width, false)),
        _ => None,
    }
}

fn is_machine_int_family(ty: &Ty) -> bool {
    matches!(ty, Ty::Int { .. } | Ty::PtrSizedInt { .. } | Ty::Bv(_))
}

fn chc_scalar_state_ty_supported(ty: &Ty) -> bool {
    // This is only the coarse, structural scalar-family gate.  Width validity
    // belongs to the typed arithmetic preflight below, where an invalid width
    // can be reported as `UnsupportedBodyArithmetic` instead of being silently
    // collapsed into the less precise "unmodelled loop body" refusal.
    matches!(ty, Ty::Bool | Ty::PtrSizedInt { .. } | Ty::Int { .. } | Ty::Bv(_))
}

fn operand_machine_int_info(func: &VerifiableFunction, operand: &Operand) -> Option<(u32, bool)> {
    crate::operand_ty_cow(func, operand).as_deref().and_then(machine_int_info)
}

fn place_machine_int_info(func: &VerifiableFunction, place: &Place) -> Option<(u32, bool)> {
    crate::place_ty_cow(func, place).as_deref().and_then(machine_int_info)
}

fn operand_is_machine_int_family(func: &VerifiableFunction, operand: &Operand) -> bool {
    crate::operand_ty_cow(func, operand).as_deref().is_some_and(is_machine_int_family)
}

fn place_is_machine_int_family(func: &VerifiableFunction, place: &Place) -> bool {
    crate::place_ty_cow(func, place).as_deref().is_some_and(is_machine_int_family)
}

fn operation_has_machine_int_family(
    func: &VerifiableFunction,
    dest: Option<&Place>,
    lhs: &Operand,
    rhs: Option<&Operand>,
) -> bool {
    dest.is_some_and(|place| place_is_machine_int_family(func, place))
        || operand_is_machine_int_family(func, lhs)
        || rhs.is_some_and(|rhs| operand_is_machine_int_family(func, rhs))
}

fn operand_is_compatible_machine_value(
    func: &VerifiableFunction,
    operand: &Operand,
    expected: (u32, bool),
) -> bool {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => {
            place_machine_int_info(func, place) == Some(expected)
        }
        // MIR constants are interpreted at the operation's destination type.
        // Several historical fixtures serialize small integer literals with a
        // wider carrier, so the destination width—not literal storage width—is
        // load-bearing here.
        Operand::Constant(
            ConstValue::Int(_)
            | ConstValue::Uint(_, _)
            | ConstValue::OpaqueScalar { .. }
            | ConstValue::ConstParam { .. },
        ) => true,
        Operand::Symbolic(formula) => matches!(trust_types::infer_sort(formula), Sort::Int),
        _ => false,
    }
}

fn operation_machine_int_info(
    func: &VerifiableFunction,
    dest: Option<&Place>,
    lhs: &Operand,
    rhs: Option<&Operand>,
) -> Option<(u32, bool)> {
    dest.and_then(|place| place_machine_int_info(func, place))
        .or_else(|| operand_machine_int_info(func, lhs))
        .or_else(|| rhs.and_then(|rhs| operand_machine_int_info(func, rhs)))
}

fn unsupported_machine_body_arithmetic(
    func: &VerifiableFunction,
    dest: &Place,
    rvalue: &Rvalue,
) -> Option<(&'static str, String)> {
    match rvalue {
        // These three operations have an exact BV round-trip below. The
        // destination type is authoritative even when a test/source constant's
        // serialized width is wider than the MIR operation's inferred type.
        Rvalue::BinaryOp(BinOp::Add | BinOp::Sub | BinOp::Mul, lhs, rhs) => {
            if let Some(machine) = place_machine_int_info(func, dest) {
                if operand_is_compatible_machine_value(func, lhs, machine)
                    && operand_is_compatible_machine_value(func, rhs, machine)
                {
                    None
                } else {
                    Some((
                        "BinaryOp",
                        "machine arithmetic operands do not match the destination's fixed-width integer type"
                            .to_string(),
                    ))
                }
            } else if operation_has_machine_int_family(func, Some(dest), lhs, Some(rhs)) {
                Some((
                    "BinaryOp",
                    "machine arithmetic destination has an unsupported or unavailable width; exact wrapping lowering is impossible"
                        .to_string(),
                ))
            } else {
                None // a non-machine arithmetic domain may retain mathematical semantics
            }
        }
        Rvalue::CheckedBinaryOp(op, lhs, rhs)
            if matches!(
                op,
                BinOp::Add
                    | BinOp::Sub
                    | BinOp::Mul
                    | BinOp::Div
                    | BinOp::Rem
                    | BinOp::Shl
                    | BinOp::Shr
            ) && operation_has_machine_int_family(func, Some(dest), lhs, Some(rhs)) =>
        {
            Some((
                "CheckedBinaryOp",
                "the (wrapped value, overflow flag) tuple and its success-path assert are not represented in the CHC transition"
                    .to_string(),
            ))
        }
        Rvalue::BinaryOp(op @ (BinOp::Div | BinOp::Rem), lhs, rhs)
            if operation_has_machine_int_family(func, Some(dest), lhs, Some(rhs)) =>
        {
            Some((
                match op {
                    BinOp::Div => "Div",
                    BinOp::Rem => "Rem",
                    _ => unreachable!("pattern restricts the operation"),
                },
                "division-by-zero and signed MIN/-1 panic conditions are not carried by the CHC transition"
                    .to_string(),
            ))
        }
        Rvalue::BinaryOp(op @ (BinOp::Shl | BinOp::Shr), lhs, rhs)
            if operation_has_machine_int_family(func, Some(dest), lhs, Some(rhs)) =>
        {
            Some((
                match op {
                    BinOp::Shl => "Shl",
                    BinOp::Shr => "Shr",
                    _ => unreachable!("pattern restricts the operation"),
                },
                "out-of-range shift panic conditions are not carried by the CHC transition"
                    .to_string(),
            ))
        }
        Rvalue::UnaryOp(UnOp::Neg, operand)
            if operation_has_machine_int_family(func, Some(dest), operand, None) =>
        {
            Some((
                "Neg",
                "signed MIN negation panic/wrapping semantics are not carried by the CHC transition"
                    .to_string(),
            ))
        }
        _ => None,
    }
}

/// Audit precisely the blocks whose statements feed this loop's condition or
/// transition. Arithmetic elsewhere in the function is irrelevant to this CHC
/// system and must not disable an otherwise supported loop.
fn reject_unmodeled_loop_body_arithmetic(
    func: &VerifiableFunction,
    loop_info: &LoopInfo,
) -> Result<(), ChcError> {
    for block_id in &loop_info.body_blocks {
        let Some(block) = func.body.blocks.get(block_id.0) else {
            continue;
        };
        for (statement, stmt) in block.stmts.iter().enumerate() {
            let Statement::Assign { place, rvalue, .. } = stmt else {
                continue;
            };
            if let Some((operation, detail)) =
                unsupported_machine_body_arithmetic(func, place, rvalue)
            {
                return Err(ChcError::UnsupportedBodyArithmetic {
                    function: func.def_path.clone(),
                    block: block.id.0,
                    statement,
                    operation: operation.to_string(),
                    detail,
                });
            }
        }
    }
    Ok(())
}

/// A predicate symbol in a CHC system (e.g., the loop invariant).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ChcPredicate {
    /// Name of the predicate (e.g., "inv_bb1").
    pub name: String,
    /// Parameter names with their sorts.
    pub params: Vec<(String, Sort)>,
}

impl ChcPredicate {
    /// Create a predicate application with the given argument formulas.
    #[must_use]
    pub fn apply(&self, args: &[Formula]) -> ChcAtom {
        ChcAtom { predicate: self.name.clone(), args: args.to_vec() }
    }

    /// Create a predicate application using primed variable names (post-state).
    #[must_use]
    pub fn apply_primed(&self) -> ChcAtom {
        let args: Vec<Formula> = self
            .params
            .iter()
            .map(|(name, sort)| Formula::Var(format!("{name}'"), sort.clone()))
            .collect();
        ChcAtom { predicate: self.name.clone(), args }
    }

    /// Create a predicate application using unprimed variable names (pre-state).
    #[must_use]
    pub fn apply_unprimed(&self) -> ChcAtom {
        let args: Vec<Formula> = self
            .params
            .iter()
            .map(|(name, sort)| Formula::Var(name.clone(), sort.clone()))
            .collect();
        ChcAtom { predicate: self.name.clone(), args }
    }
}

/// An application of a predicate to arguments.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ChcAtom {
    /// Predicate name being applied.
    pub predicate: String,
    /// Arguments to the predicate.
    pub args: Vec<Formula>,
}

/// A single Constrained Horn Clause.
///
/// Semantics: `body_atoms /\ constraint => head`
///
/// In CHC format:
///   - head is a predicate application (or `false` for queries)
///   - body_atoms are predicate applications
///   - constraint is a first-order formula over theory sorts
#[derive(Debug, Clone)]
pub struct ChcClause {
    /// The head predicate (conclusion). None means the query clause (head = false).
    pub head: Option<ChcAtom>,
    /// Body predicate applications (premises).
    pub body_atoms: Vec<ChcAtom>,
    /// First-order constraint over variables.
    pub constraint: Formula,
    /// Human-readable label for diagnostics.
    pub label: String,
}

/// The role of a clause in the CHC system.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ClauseRole {
    /// Entry clause: precondition => inv(init_vars)
    Entry,
    /// Inductive clause: inv(vars) /\ body => inv(vars')
    Inductive,
    /// Exit/query clause: inv(vars) /\ exit_cond => postcondition
    Exit,
    /// Safety query clause: inv(vars) /\ loop_cond /\ violation => false.
    /// Discharges a loop-carried safety obligation (bounds/overflow) via the
    /// PDR-synthesized invariant: UNSAT = the violation is unreachable = safe;
    /// SAT = fail-closed (obligation stays undischarged). Additive-only, so it
    /// never weakens the transition system and cannot false-prove by itself.
    Safety,
}

/// A complete CHC system encoding one or more loops.
#[derive(Debug, Clone)]
pub struct ChcSystem {
    /// Predicates to solve for (one per loop).
    pub predicates: Vec<ChcPredicate>,
    /// Horn clauses defining the system.
    pub clauses: Vec<ChcClause>,
    /// Role annotations for each clause (parallel to `clauses`).
    pub roles: Vec<ClauseRole>,
    /// Source function name for diagnostics.
    pub function_name: String,
}

impl ChcSystem {
    /// Number of predicates to infer.
    #[must_use]
    pub fn predicate_count(&self) -> usize {
        self.predicates.len()
    }

    /// Number of clauses in the system.
    #[must_use]
    pub fn clause_count(&self) -> usize {
        self.clauses.len()
    }

    /// Get clauses by role.
    #[must_use]
    pub fn clauses_by_role(&self, role: ClauseRole) -> Vec<&ChcClause> {
        self.clauses
            .iter()
            .zip(self.roles.iter())
            .filter(|(_, r)| **r == role)
            .map(|(c, _)| c)
            .collect()
    }

    /// Get entry clauses.
    #[must_use]
    pub fn entry_clauses(&self) -> Vec<&ChcClause> {
        self.clauses_by_role(ClauseRole::Entry)
    }

    /// Get inductive clauses.
    #[must_use]
    pub fn inductive_clauses(&self) -> Vec<&ChcClause> {
        self.clauses_by_role(ClauseRole::Inductive)
    }

    /// Get exit/query clauses.
    #[must_use]
    pub fn exit_clauses(&self) -> Vec<&ChcClause> {
        self.clauses_by_role(ClauseRole::Exit)
    }
}

/// Encode all loops in a function as a CHC system.
///
/// For each detected loop:
///   1. Creates an invariant predicate over the loop's modified variables
///   2. Generates entry clause: precondition => inv(init_vars)
///   3. Generates inductive clause: inv(vars) /\ loop_body => inv(vars')
///   4. Generates exit clause: inv(vars) /\ exit_cond => post
///
/// The resulting system can be passed to Spacer via `spacer_bridge::to_smtlib2`.
pub fn encode_function_loops(func: &VerifiableFunction) -> Result<ChcSystem, ChcError> {
    // CHC is a proof-producing public adapter and must share the complete
    // Trust-MIR admission boundary with ordinary VC generation. The narrower
    // transition gate below checks semantic applicability; it is not a
    // substitute for validating every local/block reference and retained
    // positional invariant.
    validate_chc_function(func)?;
    let loops = detect_loops(func);
    if loops.is_empty() {
        return Err(ChcError::NoLoops { function: func.name.clone() });
    }

    // Establish the complete semantic shape before reporting arithmetic gaps.
    // `encode_single_loop` uses the same first-write transition builder as the
    // safety adapter; without this gate a branching or multi-write loop can
    // make the transition too strong and false-prove its exit postcondition.
    for loop_info in &loops {
        let modified = collect_modified_variables(func, loop_info);
        if !loop_transition_is_faithful(func, loop_info, &modified) {
            return Err(ChcError::UnfaithfulLoopTransition {
                function: func.def_path.clone(),
                header: loop_info.header.0,
            });
        }
        if modified.is_empty() {
            return Err(ChcError::NoInductionVars { header: loop_info.header.0 });
        }
    }

    // Applicability precedes semantic-gap reporting: arithmetic contracts on
    // functions outside the exact loop fragment are not owned by this lane.
    reject_unmodeled_contract_arithmetic(func)?;

    let mut predicates = Vec::new();
    let mut clauses = Vec::new();
    let mut roles = Vec::new();

    for loop_info in &loops {
        reject_unmodeled_loop_body_arithmetic(func, loop_info)?;
        let (pred, loop_clauses, loop_roles) = encode_single_loop(func, loop_info)?;
        predicates.push(pred);
        clauses.extend(loop_clauses);
        roles.extend(loop_roles);
    }

    Ok(ChcSystem { predicates, clauses, roles, function_name: func.name.clone() })
}

/// Encode a single loop as CHC clauses.
///
/// Returns the predicate and the entry/inductive/exit clauses.
fn encode_single_loop(
    func: &VerifiableFunction,
    loop_info: &LoopInfo,
) -> Result<(ChcPredicate, Vec<ChcClause>, Vec<ClauseRole>), ChcError> {
    // Collect variables modified in the loop body
    let modified_vars = collect_modified_variables(func, loop_info);
    if modified_vars.is_empty() {
        return Err(ChcError::NoInductionVars { header: loop_info.header.0 });
    }

    // Create invariant predicate
    let pred_name = format!("inv_bb{}", loop_info.header.0);
    let predicate = ChcPredicate { name: pred_name, params: modified_vars.clone() };

    let mut clauses = Vec::new();
    let mut roles = Vec::new();

    // --- Entry clause ---
    // precondition => inv(init_values)
    let init_args = build_init_args(func, loop_info, &modified_vars);
    let entry_head = predicate.apply(&init_args);
    let precondition = build_precondition(func);

    clauses.push(ChcClause {
        head: Some(entry_head),
        body_atoms: vec![],
        constraint: precondition,
        label: format!("entry_bb{}", loop_info.header.0),
    });
    roles.push(ClauseRole::Entry);

    // --- Inductive clause ---
    // inv(vars) /\ cond /\ body_transition => inv(vars')
    let body_pred = predicate.apply_unprimed();
    let primed_head = predicate.apply_primed();

    let loop_cond =
        exact_header_loop_condition(func, loop_info).ok_or_else(|| ChcError::EncodingFailed {
            reason: format!(
                "loop header {} is outside the exact comparison fragment",
                loop_info.header.0
            ),
        })?;
    let body_transition = build_body_transition(func, loop_info, &modified_vars)?;

    let inductive_constraint = Formula::And(vec![loop_cond.clone(), body_transition]);

    clauses.push(ChcClause {
        head: Some(primed_head),
        body_atoms: vec![body_pred],
        constraint: inductive_constraint,
        label: format!("inductive_bb{}", loop_info.header.0),
    });
    roles.push(ClauseRole::Inductive);

    // --- Exit clause (query) ---
    // inv(vars) /\ !cond => postcondition
    // Encoded as: inv(vars) /\ !cond /\ !post => false
    let exit_pred = predicate.apply_unprimed();
    let exit_cond = Formula::Not(Box::new(loop_cond));
    let postcondition = build_postcondition(func);

    let exit_constraint = Formula::And(vec![exit_cond, Formula::Not(Box::new(postcondition))]);

    clauses.push(ChcClause {
        head: None, // query: head = false
        body_atoms: vec![exit_pred],
        constraint: exit_constraint,
        label: format!("exit_bb{}", loop_info.header.0),
    });
    roles.push(ClauseRole::Exit);

    Ok((predicate, clauses, roles))
}

/// Encode a loop-carried SAFETY obligation as an additional CHC query on the loop
/// invariant: `inv(vars) /\ loop_cond /\ violation => false`.
///
/// `violation` is the NEGATION of the safety condition at the obligation's point
/// (e.g. for `a - b` with `a, b: usize`, `violation = Lt(a, b)`; for `slice[i]`,
/// `violation = Ge(i, len)`). When PDR synthesizes an invariant strong enough that
/// the violation is unreachable under it, this query is UNSAT and the obligation is
/// DISCHARGED; if no such invariant exists, PDR returns SAT and the obligation stays
/// undischarged (fail-closed).
///
/// SOUNDNESS: this ADDS a query clause and never modifies/weakens the entry or
/// inductive clauses, so it cannot, by itself, make a reachable violation look
/// unreachable — an invariant satisfying it is a genuine proof. (The soundness of
/// the *whole* integration additionally requires that the caller's `loop_cond` and
/// `violation` faithfully OVER-approximate the real loop — a dropped transition or a
/// too-strong violation is the only false-proof vector, which is why the wiring must
/// ship with known-unsafe regression pins.)
pub fn encode_loop_safety_query(
    predicate: &ChcPredicate,
    loop_cond: Formula,
    violation: Formula,
    header: usize,
) -> (ChcClause, ClauseRole) {
    let clause = ChcClause {
        head: None, // query: head = false
        body_atoms: vec![predicate.apply_unprimed()],
        constraint: Formula::And(vec![loop_cond, violation]),
        label: format!("safety_bb{header}"),
    };
    (clause, ClauseRole::Safety)
}

/// Conservative soundness gate for the CHC lane: is `build_body_transition` a
/// faithful OVER-approximation of this loop?
///
/// `build_body_transition` emits, per modified variable `v`, a single equality
/// `v' = update` where `update` is the FIRST assignment to `v` found in the body
/// (or `v' = v` if none), assuming the body executes straight-line. That model is
/// faithful — holds on every iterating path — only when:
///
///   (a) the header is exactly `bool_temp = comparison; SwitchInt(bool_temp)`
///       with one explicit edge entering the loop body and no `otherwise` body
///       edge, so the comparison can be recomputed from current state;
///   (b) the unique taken path visits every NON-header body block exactly once
///       and each block ends in `Goto` or `Assert` — i.e. NOT an
///       internal `SwitchInt` (a data-flow branch that would make a single write
///       conditional — the "branch-drop" false-PROVE), nor a `Call`/`Drop`/
///       `Opaque`/`Return`/`Resume`/`Unreachable` (an unmodeled write or edge —
///       the "call-dest" false-PROVE). `Assert` is allowed: on the iterating
///       (success) path it is straight-line and it writes nothing;
///   (c) each modified variable is assigned AT MOST ONCE across the whole body, so
///       no shadowing second write is silently dropped (the "multi-assign"
///       false-PROVE); projected/non-scalar writes and unmodeled statements are
///       rejected; and
///   (d) no RHS reads a local already written earlier on the ordered path, since
///       all emitted RHS formulas denote the iteration's unprimed state.
///
/// Together these guarantee the body is single-path from the body entry to the
/// latch, so every emitted `v' = update` is unconditional and complete. Anything
/// else returns `false` => the encoder yields `None` and the obligation stays on
/// the single-formula lane (fail-closed). Over-conservative by design: a rejected
/// loop is never a soundness bug, only a missed discharge.
fn loop_transition_is_faithful(
    func: &VerifiableFunction,
    loop_info: &LoopInfo,
    modified: &[(String, Sort)],
) -> bool {
    // Shared MIR helpers interpret local/block identifiers positionally. Keep
    // the public CHC adapters fail-closed on hand-built or deserialized bodies
    // that violate rustc extraction's dense layout invariant.
    if func.body.arg_count >= func.body.locals.len()
        || !func.body.locals.iter().enumerate().all(|(position, decl)| decl.index == position)
        || !func.body.blocks.iter().enumerate().all(|(position, block)| block.id.0 == position)
    {
        return false;
    }

    // Recover the one real, ordered path from the taken header edge back to the
    // header. Merely checking terminator *kinds* is insufficient: a Goto can
    // leave the loop, skip a block, or form a smaller cycle.
    let Some(body_order) = ordered_loop_body_blocks(func, loop_info) else {
        return false;
    };

    // The condition temporary is recomputed in the header.  It is not loop
    // state, and using the stale temporary in the exit clause admits an extra
    // iteration (`i == n + 1`).  Require the exact comparison shape that the
    // inductive and exit clauses lower directly instead.
    if exact_header_loop_condition(func, loop_info).is_none() {
        return false;
    }

    // (c) each modified variable is assigned at most once across the whole body.
    // Projected writes are rejected: this scalar transition has no heap/field
    // update relation and must not silently treat the root as unchanged.
    let mut modified_locals = FxHashSet::default();
    for &bid in &body_order {
        let Some(block) = chc_block(func, bid) else {
            return false;
        };
        for stmt in &block.stmts {
            match stmt {
                Statement::Assign { place, .. } => {
                    if !place.projections.is_empty() {
                        return false;
                    }
                    let Some(decl) = chc_local_decl(func, place.local) else {
                        return false;
                    };
                    if !chc_scalar_state_ty_supported(&decl.ty) {
                        return false;
                    }
                    modified_locals.insert(place.local);
                }
                // These extraction markers have no value semantics.
                Statement::StorageLive(_)
                | Statement::StorageDead(_)
                | Statement::Coverage
                | Statement::ConstEvalCounter
                | Statement::Nop => {}
                // Discriminant/deinit/intrinsic/borrow-event and future
                // statements are not represented in this scalar transition.
                Statement::SetDiscriminant { .. }
                | Statement::Deinit { .. }
                | Statement::Retag { .. }
                | Statement::PlaceMention(_)
                | Statement::Intrinsic { .. }
                | Statement::Unsupported { .. } => return false,
                _ => return false,
            }
        }
    }

    for (name, _) in modified {
        let mut writes = 0usize;
        for &bid in &body_order {
            let Some(block) = chc_block(func, bid) else {
                return false;
            };
            for stmt in &block.stmts {
                if let Statement::Assign { place, .. } = stmt
                    && place.projections.is_empty()
                    && chc_local_name(func, place.local) == *name
                {
                    writes += 1;
                    if writes > 1 {
                        return false;
                    }
                }
            }
        }
    }

    // (d) `build_body_transition` expresses each RHS over the iteration's
    // unprimed state. That is exact for reads before any write (including
    // `sum += i; i += 1`) but not for a read-after-write (`x += 1; y = x`).
    // Walk the actual path in order and reject only the latter.
    let mut written_locals = FxHashSet::default();
    let mut written_names = FxHashSet::default();
    for &bid in &body_order {
        let Some(block) = chc_block(func, bid) else {
            return false;
        };
        for stmt in &block.stmts {
            let Statement::Assign { place, rvalue, .. } = stmt else {
                continue;
            };
            if rvalue_reads_written_local(rvalue, &written_locals, &written_names) {
                return false;
            }
            written_locals.insert(place.local);
            written_names.insert(chc_local_name(func, place.local));
        }
    }

    true
}

/// Return the unique, ordered, non-header loop-body path.
///
/// The supported fragment has one explicit `SwitchInt` target entering the
/// body, no `otherwise` body edge, and a chain of `Goto`/successful `Assert`
/// edges which visits every non-header loop block exactly once before returning
/// to the header.
fn ordered_loop_body_blocks(func: &VerifiableFunction, loop_info: &LoopInfo) -> Option<Vec<usize>> {
    let header_id = loop_info.header.0;
    let mut remaining: FxHashSet<usize> = loop_info
        .body_blocks
        .iter()
        .map(|block| block.0)
        .filter(|block| *block != header_id)
        .collect();
    if remaining.is_empty() {
        return None;
    }

    let header = chc_block(func, header_id)?;
    let Terminator::SwitchInt { targets, otherwise, .. } = &header.terminator else {
        return None;
    };
    if remaining.contains(&otherwise.0) {
        return None;
    }
    let mut entries = targets.iter().filter(|(_, target)| remaining.contains(&target.0));
    let (_, entry) = entries.next()?;
    if entries.next().is_some() {
        return None;
    }

    let mut current = entry.0;
    let mut ordered = Vec::with_capacity(remaining.len());
    loop {
        if !remaining.remove(&current) {
            return None;
        }
        ordered.push(current);
        let block = chc_block(func, current)?;
        let next = match &block.terminator {
            Terminator::Goto(target) | Terminator::Assert { target, .. } => target.0,
            _ => return None,
        };
        if next == header_id {
            break;
        }
        if !remaining.contains(&next) {
            return None;
        }
        current = next;
    }

    remaining.is_empty().then_some(ordered)
}

fn operand_reads_written_local(
    operand: &Operand,
    written_locals: &FxHashSet<usize>,
    written_names: &FxHashSet<String>,
) -> bool {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => written_locals.contains(&place.local),
        Operand::Constant(_) => false,
        Operand::Symbolic(formula) => {
            formula.free_variables().into_iter().any(|name| written_names.contains(name.as_str()))
        }
        Operand::Unsupported { .. } => true,
        _ => true,
    }
}

fn rvalue_reads_written_local(
    rvalue: &Rvalue,
    written_locals: &FxHashSet<usize>,
    written_names: &FxHashSet<String>,
) -> bool {
    let operand_reads =
        |operand: &Operand| operand_reads_written_local(operand, written_locals, written_names);
    let place_reads = |place: &Place| written_locals.contains(&place.local);
    match rvalue {
        Rvalue::Use(operand)
        | Rvalue::UnaryOp(_, operand)
        | Rvalue::Cast(operand, _)
        | Rvalue::Repeat(operand, _) => operand_reads(operand),
        Rvalue::BinaryOp(_, lhs, rhs) | Rvalue::CheckedBinaryOp(_, lhs, rhs) => {
            operand_reads(lhs) || operand_reads(rhs)
        }
        Rvalue::Ref { place, .. }
        | Rvalue::Discriminant(place)
        | Rvalue::Len(place)
        | Rvalue::AddressOf(_, place)
        | Rvalue::CopyForDeref(place) => place_reads(place),
        Rvalue::Aggregate(_, operands) | Rvalue::Unsupported { operands, .. } => {
            operands.iter().any(operand_reads)
        }
        _ => true,
    }
}

/// Assemble a complete CHC system that discharges a single loop-carried safety
/// obligation (Step 4). The system has exactly three clauses:
///
///   entry:     precond            => inv(init_vars)
///   inductive: inv(vars) /\ cond /\ body_transition => inv(vars')
///   safety:    inv(vars) /\ loop_cond /\ violation  => false
///
/// The entry + inductive clauses are built from the SAME primitives the
/// functional lane's `encode_single_loop` uses (`collect_modified_variables`,
/// `build_init_args`, `build_precondition`, `extract_loop_condition`,
/// `build_body_transition`), so the transition relation the invariant is proven
/// against is byte-identical to the functional encoding — no second, weaker model.
///
/// It DELIBERATELY OMITS the functional exit-post query (`inv /\ !cond /\ !post
/// => false`): a safety obligation is discharged iff PDR finds an inductive
/// invariant under which the `violation` is unreachable, independent of any user
/// postcondition. Adding an unrelated exit-post query could only add constraints
/// on `inv` and make the system HARDER to prove (fail-closed), so omitting it is
/// a precision choice, never a soundness one.
///
/// Returns `Ok(None)` — caller MUST fall back to the single-formula lane, never
/// drop the obligation — when the loop carries no modifiable induction state,
/// the transition/condition cannot be lowered, or the obligation's violation is
/// not faithfully / non-vacuously expressible
/// (`extract_loop_safety_query_inputs`). Source contract arithmetic that this
/// legacy lane cannot model is instead a visible `Err`; it must never be confused
/// with an inapplicable loop shape.
///
/// SOUNDNESS: additivity of the safety query (documented on
/// `encode_loop_safety_query`) means an invariant satisfying this system is a
/// genuine proof PROVIDED `build_body_transition` OVER-approximates the real loop
/// (never asserts a transition that can fail to hold). That over-approximation is
/// NOT guaranteed for arbitrary loops — `build_body_transition` models only the
/// first, unconditional write per variable — so this function enforces it up front
/// via `loop_transition_is_faithful` and returns `None` for any loop shape outside
/// that faithful class. The known-unsafe regression pins are a second,
/// independent check on that gate, not the sole guarantee.
pub fn try_build_loop_safety_chc_system(
    func: &VerifiableFunction,
    loop_info: &LoopInfo,
    obligation: &LoopSafetyObligation<'_>,
) -> Result<Option<ChcSystem>, ChcError> {
    validate_chc_function(func)?;
    // Faithful loop state: the same modified-variable set the functional lane
    // solves over. An empty set means there is no induction variable to relate
    // the violation to => fall back.
    let modified_vars = collect_modified_variables(func, loop_info);
    if modified_vars.is_empty() {
        return Ok(None);
    }

    // SOUNDNESS GATE: `build_body_transition` picks the FIRST assignment it finds
    // per variable and assumes straight-line body flow. It therefore only
    // faithfully OVER-approximates loops whose body is single-path with at most
    // one write per modified variable. For any other shape (an internal branch, a
    // shadowing second write, a call-written destination) its `v' = update`
    // relation can be too STRONG, which would let the safety query discharge a
    // reachable violation (false-PROVE). Reject those here => the caller falls
    // back to the single-formula lane (fail-closed). This gate is what makes the
    // whole CHC lane sound to enable, independent of the compiler-side router.
    if !loop_transition_is_faithful(func, loop_info, &modified_vars) {
        return Ok(None);
    }

    // Finish the obligation/condition applicability checks before turning a
    // semantic gap into a typed lane-owned error. A syntactically faithful
    // loop with an unrelated or unexpressible safety obligation still belongs
    // to the ordinary single-formula lane.
    let Some(inductive_cond) = exact_header_loop_condition(func, loop_info) else {
        return Ok(None);
    };
    let Some((loop_cond, violation)) =
        extract_loop_safety_query_inputs(func, loop_info, obligation)
    else {
        return Ok(None);
    };

    // An otherwise applicable transition owns exact body-arithmetic
    // diagnostics. Other unsupported transition shapes remain an ordinary
    // `Ok(None)` fallback, and an arithmetic source contract is reported only
    // after the full body relation was successfully constructed.
    reject_unmodeled_loop_body_arithmetic(func, loop_info)?;
    let Ok(body_transition) = build_body_transition(func, loop_info, &modified_vars) else {
        return Ok(None);
    };
    reject_unmodeled_contract_arithmetic(func)?;

    let predicate = ChcPredicate {
        name: format!("inv_bb{}", loop_info.header.0),
        params: modified_vars.clone(),
    };

    let mut clauses = Vec::new();
    let mut roles = Vec::new();

    // --- Entry: precondition => inv(init_values) ---
    let init_args = build_init_args(func, loop_info, &modified_vars);
    clauses.push(ChcClause {
        head: Some(predicate.apply(&init_args)),
        body_atoms: vec![],
        constraint: build_precondition(func),
        label: format!("entry_bb{}", loop_info.header.0),
    });
    roles.push(ClauseRole::Entry);

    // --- Inductive: inv(vars) /\ cond /\ body_transition => inv(vars') ---
    // Identical to encode_single_loop's inductive clause: reuse verbatim so the
    // safety query is answered against the exact same transition relation.
    clauses.push(ChcClause {
        head: Some(predicate.apply_primed()),
        body_atoms: vec![predicate.apply_unprimed()],
        constraint: Formula::And(vec![inductive_cond, body_transition]),
        label: format!("inductive_bb{}", loop_info.header.0),
    });
    roles.push(ClauseRole::Inductive);

    // --- Safety query: inv(vars) /\ loop_cond /\ violation => false ---
    let (safety_clause, safety_role) =
        encode_loop_safety_query(&predicate, loop_cond, violation, loop_info.header.0);
    clauses.push(safety_clause);
    roles.push(safety_role);

    Ok(Some(ChcSystem {
        predicates: vec![predicate],
        clauses,
        roles,
        function_name: func.name.clone(),
    }))
}

/// Compatibility wrapper for the historical safety-CHC API.
///
/// Encoding errors are deliberately collapsed to `None`: callers of the old
/// API can only lose a CHC discharge and fall back to the ordinary VC lane;
/// they can never accept an unsound transition. New code should use
/// [`try_build_loop_safety_chc_system`] to retain the typed diagnostic.
#[deprecated(
    since = "0.1.0",
    note = "use try_build_loop_safety_chc_system to retain fail-closed encoding diagnostics"
)]
#[must_use]
pub fn build_loop_safety_chc_system(
    func: &VerifiableFunction,
    loop_info: &LoopInfo,
    obligation: &LoopSafetyObligation<'_>,
) -> Option<ChcSystem> {
    try_build_loop_safety_chc_system(func, loop_info, obligation).ok().flatten()
}

/// Render a `ChcSystem` as an SMT-LIB2 HORN script — `(set-logic HORN)`, one
/// `declare-fun` per invariant predicate, one `(assert (forall … (=> body head)))`
/// per clause, and `(check-sat)` — ready for a Spacer/PDR solver such as ay-chc.
///
/// This is a serialization helper, not a verdict API. With these assertions a
/// consistent safe system normally returns `sat` (a predicate interpretation
/// exists), while a forced reachable `false` clause makes the full assertion set
/// `unsat`. That raw result is therefore the opposite of the typed reachability
/// query convention used by some CHC frontends. Callers must not interpret
/// `unsat` here as an obligation discharge; use the typed transport/query API for
/// proof verdicts.
///
/// This is the direct-solve counterpart to `chc_system_to_typed_chc_json` (the
/// structured transport to trust-bmc): identical clause semantics, emitted as
/// text. A head-`None` query clause becomes `(=> body false)`. Primed variable
/// names (`i'`) are rewritten uniformly to a legal SMT-LIB simple symbol (`i.p`),
/// since `'` is not a permitted simple-symbol character; `'` occurs ONLY in primed
/// names in our generated systems, so the global rewrite stays consistent per
/// variable.
pub fn chc_system_to_smtlib2_horn(sys: &ChcSystem) -> String {
    let printer = SmtPrinter::with_defaults();
    let mut lines = vec!["(set-logic HORN)".to_string()];

    for pred in &sys.predicates {
        let sorts: Vec<Sort> = pred.params.iter().map(|(_, s)| s.clone()).collect();
        lines.push(printer.print_declare_fun(&pred.name, &sorts, &Sort::Bool));
    }

    for clause in &sys.clauses {
        // Free variables across the constraint and every atom argument.
        let mut vars: std::collections::BTreeSet<(String, Sort)> =
            trust_types::collect_free_var_decls(&clause.constraint);
        for atom in clause.body_atoms.iter().chain(clause.head.iter()) {
            for arg in &atom.args {
                vars.extend(trust_types::collect_free_var_decls(arg));
            }
        }

        // Body = conjunction of the body-atom applications and the constraint.
        let mut body_parts: Vec<String> =
            clause.body_atoms.iter().map(|a| chc_render_atom_smt(&printer, a)).collect();
        let constraint_str = printer.to_smtlib2(&clause.constraint);
        if constraint_str != "true" {
            body_parts.push(constraint_str);
        }
        let body = if body_parts.is_empty() {
            "true".to_string()
        } else if body_parts.len() == 1 {
            body_parts.into_iter().next().unwrap_or_default()
        } else {
            format!("(and {})", body_parts.join(" "))
        };

        let head = match &clause.head {
            Some(atom) => chc_render_atom_smt(&printer, atom),
            None => "false".to_string(),
        };

        let rule = format!("(=> {body} {head})");
        let assertion = if vars.is_empty() {
            format!("(assert {rule})")
        } else {
            let binders: Vec<String> =
                vars.iter().map(|(n, s)| format!("({} {})", n, s.to_smtlib())).collect();
            format!("(assert (forall ({}) {rule}))", binders.join(" "))
        };
        lines.push(assertion);
    }

    lines.push("(check-sat)".to_string());
    lines.join("\n").replace('\'', ".p")
}

/// Render a single predicate application `(name arg1 arg2 …)` (or bare `name` for
/// a nullary predicate) with each argument rendered by the shared SMT printer.
fn chc_render_atom_smt(printer: &SmtPrinter, atom: &ChcAtom) -> String {
    if atom.args.is_empty() {
        atom.predicate.clone()
    } else {
        let args: Vec<String> = atom.args.iter().map(|a| printer.to_smtlib2(a)).collect();
        format!("({} {})", atom.predicate, args.join(" "))
    }
}

// ── ChcSystem → typed-CHC transport JSON (trust-mc.typed-chc-obligation.v1) ──
//
// Serializes a `ChcSystem` into the UNTYPED serde_json shape consumed by
// trust-bmc's `TrustMcTypedChcObligationInput` deserializer
// (crates/trust-bmc/src/verifier_api.rs:1281 / to_trust_mc_chc_vc @1372).
//
// Field-by-field per the transport map:
//   * each `ChcPredicate`            -> one `relations[{name, arg_sorts}]` entry
//                                       (arg_sorts = the predicate's param sorts)
//                                       and its params/primed/init occurrences
//                                       populate `vars[{name, sort}]`.
//   * each `ChcClause`               -> one `rules[{head, body}]`.
//   * a head=false clause
//     (`ClauseRole::Safety`/`Exit`)  -> a rule whose head is the synthetic
//                                       nullary `error` relation, and it sets
//                                       `query.target = "error"` (reachability
//                                       of `error` == the violation is
//                                       reachable == UNSAFE; UNSAT == safe).
//   * `ChcClause.constraint`         -> `body.constraints` (top-level `And`
//                                       flattened; `Bool(true)` conjuncts
//                                       dropped so an entry clause is not a
//                                       vacuous "generic Bool-true fact").
//   * `ChcClause.body_atoms`         -> at most ONE `body.relation` (the schema
//                                       admits a single body predicate atom); a
//                                       clause with >1 atom is a HARD ERROR so
//                                       the caller falls back to the
//                                       single-formula lane rather than lossily
//                                       dropping an atom.
//
// Only the int/bool/bit-vector `Formula` fragment is representable; any other
// node (arrays, quantifiers, floats, ITE, uninterpreted preds, unsupported
// sorts, >1 body atom, missing query) returns `Err`, which the caller maps to
// `None` == "fall back to the single-formula lane" (fail-closed).

/// The synthetic nullary reachability target relation for a loop-safety query.
/// Matches the compiler's structural panic-freedom convention
/// (`trust_mc_default_function_chc_from_trust_ir`: `relations=[{name:"error"}]`,
/// `query.target="error"`, head-false clauses derive `error`).
pub const CHC_TYPED_ERROR_RELATION: &str = "error";

/// Serialize a [`ChcSystem`] into the `trust-mc.typed-chc-obligation.v1`
/// transport JSON fragment (`vars` / `relations` / `rules` / `query`).
///
/// The compiler (step 7/8) splices these keys into the full obligation `value`
/// (which additionally carries `origin="mir_derived"` and `native_metadata`);
/// `function_name` is emitted as a convenience and may be overridden there.
///
/// Returns `Err` (=> caller `.ok()` => single-formula fallback) when the system
/// contains anything outside the representable int/bool/bit-vec CHC fragment.
pub fn chc_system_to_typed_chc_json(sys: &ChcSystem) -> Result<serde_json::Value, ChcError> {
    // Rule lowering also collects every referenced variable (unprimed params,
    // primed post-state names, init vars, and any free var in a constraint)
    // into `vars`, guaranteeing the `vars` block is closed over the rules —
    // the deserializer rejects any undeclared Var reference.
    let mut vars: std::collections::BTreeMap<String, Sort> = std::collections::BTreeMap::new();

    let mut rules = Vec::with_capacity(sys.clauses.len());
    let mut has_query = false;
    for clause in &sys.clauses {
        if clause.head.is_none() {
            has_query = true;
        }
        rules.push(chc_clause_to_typed_rule(clause, &mut vars)?);
    }
    if !has_query {
        return Err(ChcError::EncodingFailed {
            reason: format!(
                "CHC system for `{}` has no query (head-false) clause; a proof-grade typed-CHC obligation needs a reachability target",
                sys.function_name
            ),
        });
    }

    // One relation per invariant predicate (arg_sorts = param sorts, in order),
    // plus the synthetic nullary `error` target.
    let mut relations = Vec::with_capacity(sys.predicates.len() + 1);
    for pred in &sys.predicates {
        let arg_sorts = pred
            .params
            .iter()
            .map(|(_, sort)| chc_sort_to_typed_json(sort))
            .collect::<Result<Vec<_>, _>>()?;
        relations.push(serde_json::json!({ "name": pred.name, "arg_sorts": arg_sorts }));
    }
    relations.push(serde_json::json!({ "name": CHC_TYPED_ERROR_RELATION, "arg_sorts": [] }));

    let vars_json = vars
        .iter()
        .map(|(name, sort)| {
            Ok::<_, ChcError>(
                serde_json::json!({ "name": name, "sort": chc_sort_to_typed_json(sort)? }),
            )
        })
        .collect::<Result<Vec<_>, _>>()?;

    Ok(serde_json::json!({
        "function_name": sys.function_name,
        "query": { "target": CHC_TYPED_ERROR_RELATION },
        "vars": vars_json,
        "relations": relations,
        "rules": rules,
    }))
}

/// Lower one `ChcClause` to a typed-CHC `rules[]` entry.
fn chc_clause_to_typed_rule(
    clause: &ChcClause,
    vars: &mut std::collections::BTreeMap<String, Sort>,
) -> Result<serde_json::Value, ChcError> {
    // head: a real predicate application, or the synthetic `error` target for a
    // head=false (query) clause.
    let head = match &clause.head {
        Some(atom) => chc_atom_to_relation_app(atom, vars)?,
        None => serde_json::json!({ "name": CHC_TYPED_ERROR_RELATION }),
    };

    // body: the schema admits at most one predicate atom.
    if clause.body_atoms.len() > 1 {
        return Err(ChcError::EncodingFailed {
            reason: format!(
                "clause `{}` has {} body atoms; the typed-CHC rule body admits at most one predicate atom",
                clause.label,
                clause.body_atoms.len()
            ),
        });
    }
    let mut body = serde_json::Map::new();
    if let Some(atom) = clause.body_atoms.first() {
        body.insert("relation".to_string(), chc_atom_to_relation_app(atom, vars)?);
    }

    // constraints: flatten a top-level conjunction and drop `true` so an entry
    // clause (`true => inv(init)`) does NOT serialize to the single Bool-true
    // fact that `validate_non_vacuous_mir_rule_binding` rejects.
    let mut conjuncts: Vec<&Formula> = Vec::new();
    chc_flatten_conjuncts(&clause.constraint, &mut conjuncts);
    let constraints = conjuncts
        .iter()
        .map(|c| chc_formula_to_typed_expr(c, vars))
        .collect::<Result<Vec<_>, _>>()?;
    body.insert("constraints".to_string(), serde_json::Value::Array(constraints));

    Ok(serde_json::json!({ "head": head, "body": serde_json::Value::Object(body) }))
}

/// Lower a `ChcAtom` (predicate application) to a typed-CHC relation-app object.
fn chc_atom_to_relation_app(
    atom: &ChcAtom,
    vars: &mut std::collections::BTreeMap<String, Sort>,
) -> Result<serde_json::Value, ChcError> {
    let args = atom
        .args
        .iter()
        .map(|arg| chc_formula_to_typed_expr(arg, vars))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(serde_json::json!({ "name": atom.predicate, "args": args }))
}

/// Flatten a top-level (possibly nested) `And`, dropping `Bool(true)` conjuncts.
/// A lone `Bool(true)` flattens to the empty conjunct list.
fn chc_flatten_conjuncts<'a>(f: &'a Formula, out: &mut Vec<&'a Formula>) {
    match f {
        Formula::And(items) => {
            for item in items {
                chc_flatten_conjuncts(item, out);
            }
        }
        Formula::Bool(true) => {}
        other => out.push(other),
    }
}

/// Map a `Sort` to the typed-CHC sort JSON (`{"kind": ...}`). Only the
/// bool/int/bit-vec fragment is representable.
fn chc_sort_to_typed_json(sort: &Sort) -> Result<serde_json::Value, ChcError> {
    match sort {
        Sort::Bool => Ok(serde_json::json!({ "kind": "bool" })),
        Sort::Int => Ok(serde_json::json!({ "kind": "int" })),
        Sort::BitVec(width) if *width > 0 => {
            Ok(serde_json::json!({ "kind": "bit_vec", "width": width }))
        }
        Sort::BitVec(width) => Err(ChcError::EncodingFailed {
            reason: format!("bit-vector sort width must be positive, got {width}"),
        }),
        other => Err(ChcError::UnsupportedMir {
            kind: "Sort".to_string(),
            detail: format!("{other:?} is outside the typed-CHC bool/int/bit-vec sort fragment"),
        }),
    }
}

/// Record a referenced variable, enforcing a single consistent sort per name.
fn chc_record_var(
    vars: &mut std::collections::BTreeMap<String, Sort>,
    name: &str,
    sort: &Sort,
) -> Result<(), ChcError> {
    if let Some(prev) = vars.get(name) {
        if prev != sort {
            return Err(ChcError::EncodingFailed {
                reason: format!(
                    "variable `{name}` is referenced with conflicting sorts {prev:?} and {sort:?}"
                ),
            });
        }
    } else {
        vars.insert(name.to_string(), sort.clone());
    }
    Ok(())
}

/// Emit a JSON number for an integer, falling back to a decimal STRING when the
/// value is outside the i64/u64 range serde_json can render as a bare number
/// (the deserializer accepts both — `trust_mc_typed_chc_integer_to_i128`).
fn chc_int_to_json(v: i128) -> serde_json::Value {
    if let Ok(n) = i64::try_from(v) {
        serde_json::json!(n)
    } else if let Ok(n) = u64::try_from(v) {
        serde_json::json!(n)
    } else {
        serde_json::json!(v.to_string())
    }
}

/// Lower a `Formula` to a typed-CHC `TrustMcTypedChcExprInput` JSON value,
/// recording every `Var`/`SymVar` occurrence into `vars`. Mirrors the compiler's
/// `trust_mc_typed_chc_expr_from_trust_spec` op tables. Any node outside the
/// int/bool/bit-vec fragment is a hard error (=> single-formula fallback).
fn chc_formula_to_typed_expr(
    f: &Formula,
    vars: &mut std::collections::BTreeMap<String, Sort>,
) -> Result<serde_json::Value, ChcError> {
    match f {
        // ── literals ──
        Formula::Bool(b) => Ok(serde_json::json!({ "kind": "bool_const", "value": b })),
        Formula::Int(i) => {
            Ok(serde_json::json!({ "kind": "int_const", "value": chc_int_to_json(*i) }))
        }
        Formula::UInt(u) => {
            let value = match i128::try_from(*u) {
                Ok(v) => chc_int_to_json(v),
                Err(_) => serde_json::json!(u.to_string()),
            };
            Ok(serde_json::json!({ "kind": "int_const", "value": value }))
        }
        Formula::BitVec { value, width } if *width > 0 => Ok(serde_json::json!({
            "kind": "bit_vec_const",
            "value": chc_int_to_json(*value),
            "width": width,
        })),
        Formula::BitVec { width, .. } => Err(ChcError::EncodingFailed {
            reason: format!("bit-vector constant width must be positive, got {width}"),
        }),

        // ── variables ──
        Formula::Var(name, sort) => {
            chc_record_var(vars, name, sort)?;
            Ok(serde_json::json!({
                "kind": "var",
                "name": name,
                "sort": chc_sort_to_typed_json(sort)?,
            }))
        }
        Formula::SymVar(sym, sort) => {
            let name = sym.as_str();
            chc_record_var(vars, name, sort)?;
            Ok(serde_json::json!({
                "kind": "var",
                "name": name,
                "sort": chc_sort_to_typed_json(sort)?,
            }))
        }

        // ── unary ──
        Formula::Not(a) => chc_unary_expr("not", a, vars),
        Formula::Neg(a) => chc_unary_expr("neg", a, vars),
        Formula::BvNot(a, _) => chc_unary_expr("bv_not", a, vars),
        // ── Int↔BV bridges (the width-128 wrapping/reinterpret glue) ──
        // A faithful fixed-width wrapping op on an Int-sorted operand is modeled
        // as `BvToInt(Bv{Add,Sub,Mul,URem}(IntToBv(a, w), IntToBv(b, w), w), w,
        // signed)` — the exact two's-complement machine result. The wrapping BV
        // ops themselves encode below (`bv_add`/`bv_sub`/`bv_mul`/`bv_urem` via
        // `chc_binary_expr`, any width including 128); these two bridges are the
        // remaining edges — without them a >64-bit wrapping body-def
        // (Lcg::range_i128 / range_usize) had no typed-CHC payload and its whole
        // postcondition CHC fell back to the single-formula lane. Both map 1:1 to
        // the consumer's `int_to_bv`/`bv_to_int` unary ops
        // (`TrustMcTypedChcUnaryOpInput`, verifier_api.rs): `int_to_bv` carries
        // ONLY `width`, `bv_to_int` carries ONLY `signed` — matching the
        // consumer's strict parameter gate exactly. `signed` selects
        // `bv2int_signed` vs unsigned `bv2int`, mirroring `Formula::BvToInt`'s
        // flag (the load-bearing "top-bit byte = 255 unsigned, not −1 signed"
        // distinction). SOUNDNESS: these are faithful sort-changing identities
        // (`int2bv` = value mod 2^w; `bv2int{_signed}` = the exact
        // (un)signed reading), so they can only translate a genuine
        // machine-arithmetic fact — never manufacture one. Non-positive widths
        // are meaningless and fail closed.
        Formula::IntToBv(a, width) if *width > 0 => {
            trust_types::check_formula_sort(f).map_err(|err| ChcError::EncodingFailed {
                reason: format!("ill-sorted typed-CHC int-to-bv expression: {err}"),
            })?;
            let expr = chc_formula_to_typed_expr(a, vars)?;
            Ok(serde_json::json!({
                "kind": "unary", "op": "int_to_bv", "width": width, "expr": expr,
            }))
        }
        Formula::IntToBv(_, width) => Err(ChcError::EncodingFailed {
            reason: format!("int-to-bv width must be positive, got {width}"),
        }),
        Formula::BvToInt(a, width, signed) if *width > 0 => {
            trust_types::check_formula_sort(f).map_err(|err| ChcError::EncodingFailed {
                reason: format!("ill-sorted typed-CHC bv-to-int expression: {err}"),
            })?;
            let expr = chc_formula_to_typed_expr(a, vars)?;
            Ok(serde_json::json!({
                "kind": "unary", "op": "bv_to_int", "signed": signed, "expr": expr,
            }))
        }
        Formula::BvToInt(_, width, _) => Err(ChcError::EncodingFailed {
            reason: format!("bv-to-int width must be positive, got {width}"),
        }),
        Formula::BvSignExt(a, extend_by) => {
            let expr = chc_formula_to_typed_expr(a, vars)?;
            Ok(serde_json::json!({
                "kind": "unary", "op": "bv_sign_ext", "extend_by": extend_by, "expr": expr,
            }))
        }
        Formula::BvExtract { inner, high, low } => {
            let expr = chc_formula_to_typed_expr(inner, vars)?;
            Ok(serde_json::json!({
                "kind": "unary", "op": "bv_extract", "high": high, "low": low, "expr": expr,
            }))
        }

        // ── n-ary boolean connectives folded to a binary chain ──
        Formula::And(items) => chc_fold_bool_expr("and", items, vars, true),
        Formula::Or(items) => chc_fold_bool_expr("or", items, vars, false),

        // ── binary ──
        Formula::Implies(a, b) => chc_binary_expr("implies", a, b, vars),
        Formula::Eq(a, b) => chc_binary_expr("eq", a, b, vars),
        Formula::Lt(a, b) => chc_binary_expr("lt", a, b, vars),
        Formula::Le(a, b) => chc_binary_expr("le", a, b, vars),
        Formula::Gt(a, b) => chc_binary_expr("gt", a, b, vars),
        Formula::Ge(a, b) => chc_binary_expr("ge", a, b, vars),
        Formula::Add(a, b) => chc_binary_expr("add", a, b, vars),
        Formula::Sub(a, b) => chc_binary_expr("sub", a, b, vars),
        Formula::Mul(a, b) => chc_binary_expr("mul", a, b, vars),
        Formula::Div(a, b) => chc_binary_expr("div", a, b, vars),
        Formula::Rem(a, b) => chc_binary_expr("mod", a, b, vars),
        Formula::BvAdd(a, b, _) => chc_binary_expr("bv_add", a, b, vars),
        Formula::BvSub(a, b, _) => chc_binary_expr("bv_sub", a, b, vars),
        Formula::BvMul(a, b, _) => chc_binary_expr("bv_mul", a, b, vars),
        Formula::BvUDiv(a, b, _) => chc_binary_expr("bv_udiv", a, b, vars),
        Formula::BvURem(a, b, _) => chc_binary_expr("bv_urem", a, b, vars),
        Formula::BvAnd(a, b, _) => chc_binary_expr("bv_and", a, b, vars),
        Formula::BvOr(a, b, _) => chc_binary_expr("bv_or", a, b, vars),
        Formula::BvXor(a, b, _) => chc_binary_expr("bv_xor", a, b, vars),
        Formula::BvShl(a, b, _) => chc_binary_expr("bv_shl", a, b, vars),
        Formula::BvLShr(a, b, _) => chc_binary_expr("bv_lshr", a, b, vars),
        Formula::BvAShr(a, b, _) => chc_binary_expr("bv_ashr", a, b, vars),
        Formula::BvULt(a, b, _) => chc_binary_expr("bv_ult", a, b, vars),
        Formula::BvULe(a, b, _) => chc_binary_expr("bv_ule", a, b, vars),
        Formula::BvSLt(a, b, _) => chc_binary_expr("bv_slt", a, b, vars),
        Formula::BvSLe(a, b, _) => chc_binary_expr("bv_sle", a, b, vars),

        // Everything else (ITE, arrays, quantifiers, floats, uninterpreted
        // preds, Bv{S}Div/{S}Rem/Concat/ZeroExt) has no typed-CHC encoding —
        // fail closed to the single-formula lane. (`IntToBv`/`BvToInt` ARE
        // encoded above; the consumer has no `bv_sdiv`/`bv_srem` op, so signed
        // BV division/remainder stays fail-closed.)
        other => Err(ChcError::UnsupportedMir {
            kind: "Formula".to_string(),
            detail: format!(
                "{other:?} is outside the typed-CHC bool/int/bit-vec expression fragment"
            ),
        }),
    }
}

fn chc_unary_expr(
    op: &str,
    inner: &Formula,
    vars: &mut std::collections::BTreeMap<String, Sort>,
) -> Result<serde_json::Value, ChcError> {
    let expr = chc_formula_to_typed_expr(inner, vars)?;
    Ok(serde_json::json!({ "kind": "unary", "op": op, "expr": expr }))
}

fn chc_binary_expr(
    op: &str,
    lhs: &Formula,
    rhs: &Formula,
    vars: &mut std::collections::BTreeMap<String, Sort>,
) -> Result<serde_json::Value, ChcError> {
    let lhs = chc_formula_to_typed_expr(lhs, vars)?;
    let rhs = chc_formula_to_typed_expr(rhs, vars)?;
    Ok(serde_json::json!({ "kind": "binary", "op": op, "lhs": lhs, "rhs": rhs }))
}

/// Fold an n-ary `And`/`Or` into a left-associated binary chain. An empty
/// conjunction is `true`; an empty disjunction is `false`.
fn chc_fold_bool_expr(
    op: &str,
    items: &[Formula],
    vars: &mut std::collections::BTreeMap<String, Sort>,
    empty_value: bool,
) -> Result<serde_json::Value, ChcError> {
    if items.is_empty() {
        return Ok(serde_json::json!({ "kind": "bool_const", "value": empty_value }));
    }
    let mut acc = chc_formula_to_typed_expr(&items[0], vars)?;
    for item in &items[1..] {
        let rhs = chc_formula_to_typed_expr(item, vars)?;
        acc = serde_json::json!({ "kind": "binary", "op": op, "lhs": acc, "rhs": rhs });
    }
    Ok(acc)
}

/// Collect variables modified inside the loop body.
///
/// These become the parameters of the invariant predicate.
pub(crate) fn collect_modified_variables(
    func: &VerifiableFunction,
    loop_info: &LoopInfo,
) -> Vec<(String, Sort)> {
    let mut modified = Vec::new();
    let mut seen_locals = FxHashSet::default();
    let body_set: FxHashSet<usize> = loop_info
        .body_blocks
        .iter()
        .map(|b| b.0)
        .filter(|block| *block != loop_info.header.0)
        .collect();

    for &body_id in &body_set {
        let Some(block) = chc_block(func, body_id) else {
            continue;
        };
        for stmt in &block.stmts {
            if let Statement::Assign { place, .. } = stmt
                && place.projections.is_empty()
                && !seen_locals.contains(&place.local)
            {
                seen_locals.insert(place.local);
                if let Some(decl) = chc_local_decl(func, place.local) {
                    let name = chc_local_name(func, place.local);
                    let sort = crate::sort_for_ty(&decl.ty);
                    modified.push((name, sort));
                }
            }
        }
    }

    // Sort for deterministic output
    modified.sort_by(|a, b| a.0.cmp(&b.0));
    modified
}

/// Build initial values for the invariant predicate arguments.
///
/// Uses induction variable init values where available, falls back to
/// uninterpreted variable references.
fn build_init_args(
    func: &VerifiableFunction,
    loop_info: &LoopInfo,
    params: &[(String, Sort)],
) -> Vec<Formula> {
    params
        .iter()
        .map(|(name, sort)| {
            // Try to find an induction variable with a known init
            if let Some(ivar) = loop_info.induction_vars.iter().find(|iv| {
                let iv_name = chc_local_name(func, iv.local_idx);
                iv_name == *name
            }) && let Some(init) = &ivar.init
            {
                return init.clone();
            }
            // Fallback: use an initial-state variable
            Formula::Var(generated_chc_symbol(&format!("init_{name}")), sort.clone())
        })
        .collect()
}

/// Extract the loop continuation condition from the header block.
///
/// Looks for a SwitchInt terminator in the header and extracts the
/// condition under which the loop body is entered.
pub(crate) fn extract_loop_condition(
    func: &VerifiableFunction,
    loop_info: &LoopInfo,
) -> Result<Formula, ChcError> {
    let Some(header) = func.body.blocks.get(loop_info.header.0) else {
        return Ok(Formula::Bool(true));
    };

    match &header.terminator {
        Terminator::SwitchInt { discr, targets, .. } => {
            // The loop body is entered when the discriminant matches a target
            // that leads to a body block
            let body_set: FxHashSet<usize> = loop_info.body_blocks.iter().map(|b| b.0).collect();

            let discr_formula = operand_to_formula_checked(func, discr)?;
            // A Bool discriminant must NOT be compared to an integer switch value:
            // `(= cond 1)` mixes the Bool and Int sorts and is ill-typed SMT, which
            // the PDR backend cannot solve (it diverges / returns Unknown). Emit the
            // boolean condition directly instead — value 1 => `cond`, value 0 =>
            // `!cond` — which is semantically identical and well-typed.
            let discr_is_bool = matches!(crate::operand_sort(func, discr), Some(Sort::Bool));

            for (value, target) in targets {
                if body_set.contains(&target.0) && *target != loop_info.header {
                    // This target enters the loop body
                    return Ok(if discr_is_bool {
                        match *value {
                            1 => discr_formula,
                            0 => Formula::Not(Box::new(discr_formula)),
                            _ => Formula::Eq(
                                Box::new(discr_formula),
                                Box::new(u128_to_formula(*value)),
                            ),
                        }
                    } else {
                        Formula::Eq(Box::new(discr_formula), Box::new(u128_to_formula(*value)))
                    });
                }
            }
            Ok(Formula::Bool(true))
        }
        _ => Ok(Formula::Bool(true)),
    }
}

/// Extract the loop exit condition (negation of the continuation condition).
pub(crate) fn extract_exit_condition(
    func: &VerifiableFunction,
    loop_info: &LoopInfo,
) -> Result<Formula, ChcError> {
    let cond = extract_loop_condition(func, loop_info)?;
    Ok(Formula::Not(Box::new(cond)))
}

/// Build the body transition relation: how variables change in one iteration.
///
/// For each modified variable, generates `var' = update_expr(var, ...)`.
fn build_body_transition(
    func: &VerifiableFunction,
    loop_info: &LoopInfo,
    params: &[(String, Sort)],
) -> Result<Formula, ChcError> {
    let mut constraints = Vec::new();
    let body_order =
        ordered_loop_body_blocks(func, loop_info).ok_or_else(|| ChcError::EncodingFailed {
            reason: format!(
                "loop {} does not have one exact ordered body path",
                loop_info.header.0
            ),
        })?;

    for (name, sort) in params {
        let primed = Formula::Var(format!("{name}'"), sort.clone());

        // Try to find the update expression from the loop body
        let update = find_variable_update(func, &body_order, name)?;

        match update {
            Some(update_formula) => {
                let actual_sort =
                    trust_types::check_formula_sort(&update_formula).map_err(|e| {
                        ChcError::UnsupportedMir {
                            kind: "loop assignment".to_string(),
                            detail: format!("update for `{name}` is ill-sorted: {e:?}"),
                        }
                    })?;
                if actual_sort != *sort {
                    return Err(ChcError::UnsupportedMir {
                        kind: "loop assignment".to_string(),
                        detail: format!(
                            "update for `{name}` has sort {actual_sort:?}, expected {sort:?}"
                        ),
                    });
                }
                constraints.push(Formula::Eq(Box::new(primed), Box::new(update_formula)));
            }
            None => {
                // Variable not updated in this path -- stays the same
                let unprimed = Formula::Var(name.clone(), sort.clone());
                constraints.push(Formula::Eq(Box::new(primed), Box::new(unprimed)));
            }
        }
    }

    if constraints.is_empty() {
        Ok(Formula::Bool(true))
    } else if constraints.len() == 1 {
        // SAFETY: len == 1 arm of the match guarantees .next() returns Some.
        Ok(constraints
            .into_iter()
            .next()
            .unwrap_or_else(|| unreachable!("empty iter despite len == 1")))
    } else {
        Ok(Formula::And(constraints))
    }
}

/// Find the update expression for a variable in the loop body.
fn find_variable_update(
    func: &VerifiableFunction,
    body_order: &[usize],
    var_name: &str,
) -> Result<Option<Formula>, ChcError> {
    for &body_id in body_order {
        let Some(block) = chc_block(func, body_id) else {
            continue;
        };
        for stmt in &block.stmts {
            if let Statement::Assign { place, rvalue, .. } = stmt
                && place.projections.is_empty()
                && let Some(decl) = chc_local_decl(func, place.local)
            {
                let name = chc_local_name(func, place.local);
                if name == var_name {
                    let sort = crate::place_sort(func, place)
                        .unwrap_or_else(|| crate::sort_for_ty(&decl.ty));
                    return Ok(Some(rvalue_to_formula_with_dest(
                        func,
                        rvalue,
                        Some((
                            name.as_str(),
                            sort,
                            machine_int_info(&decl.ty),
                            is_machine_int_family(&decl.ty),
                        )),
                    )?));
                }
            }
        }
    }
    Ok(None)
}

/// Convert an Rvalue to a Formula.
pub(crate) fn rvalue_to_formula(
    func: &VerifiableFunction,
    rvalue: &Rvalue,
) -> Result<Formula, ChcError> {
    rvalue_to_formula_with_dest(func, rvalue, None)
}

fn rvalue_to_formula_with_dest(
    func: &VerifiableFunction,
    rvalue: &Rvalue,
    dest: Option<(&str, Sort, Option<(u32, bool)>, bool)>,
) -> Result<Formula, ChcError> {
    match rvalue {
        Rvalue::Use(op) => operand_to_formula_checked(func, op),
        Rvalue::BinaryOp(op, lhs, rhs) => {
            let l = operand_to_formula_checked(func, lhs)?;
            let r = operand_to_formula_checked(func, rhs)?;
            let machine = dest
                .as_ref()
                .and_then(|(_, _, machine, _)| *machine)
                .or_else(|| operation_machine_int_info(func, None, lhs, Some(rhs)));
            let has_machine_family = dest.as_ref().is_some_and(|(_, _, _, machine)| *machine)
                || operation_has_machine_int_family(func, None, lhs, Some(rhs));
            match (*op, machine) {
                (BinOp::Add | BinOp::Sub | BinOp::Mul, Some((width, signed))) => {
                    if !operand_is_compatible_machine_value(func, lhs, (width, signed))
                        || !operand_is_compatible_machine_value(func, rhs, (width, signed))
                    {
                        Err(unsupported_chc_lowering(
                            "Rvalue::BinaryOp",
                            "machine arithmetic operands do not match the selected fixed-width integer type"
                                .to_string(),
                        ))
                    } else {
                        wrapping_machine_binop_to_formula(*op, l, r, width, signed)
                    }
                }
                (BinOp::Div | BinOp::Rem, Some(_)) => Err(unsupported_chc_lowering(
                    "Rvalue::BinaryOp",
                    format!("{op:?} requires its MIR panic conditions in the CHC transition"),
                )),
                (BinOp::Shl | BinOp::Shr, Some(_)) => Err(unsupported_chc_lowering(
                    "Rvalue::BinaryOp",
                    format!(
                        "{op:?} requires its out-of-range panic condition in the CHC transition"
                    ),
                )),
                (
                    BinOp::Add
                    | BinOp::Sub
                    | BinOp::Mul
                    | BinOp::Div
                    | BinOp::Rem
                    | BinOp::Shl
                    | BinOp::Shr,
                    None,
                ) if has_machine_family => Err(unsupported_chc_lowering(
                    "Rvalue::BinaryOp",
                    format!(
                        "{op:?} has an unsupported or unavailable machine width; mathematical-Int fallback is forbidden"
                    ),
                )),
                (_, machine) => {
                    // Comparisons are exact over the integer interpretation of
                    // machine values. Bitwise operations use the existing exact
                    // BV bridge; non-machine arithmetic alone retains Int.
                    let (width, signed) = machine.map_or((None, false), |(w, s)| (Some(w), s));
                    try_binop_to_formula(*op, l, r, width, signed)
                }
            }
        }
        Rvalue::CheckedBinaryOp(op, lhs, rhs) => {
            if matches!(
                op,
                BinOp::Add
                    | BinOp::Sub
                    | BinOp::Mul
                    | BinOp::Div
                    | BinOp::Rem
                    | BinOp::Shl
                    | BinOp::Shr
            ) && operation_has_machine_int_family(func, None, lhs, Some(rhs))
            {
                return Err(unsupported_chc_lowering(
                    "Rvalue::CheckedBinaryOp",
                    "the (wrapped value, overflow flag) tuple and success-path assert are not represented by CHC lowering"
                        .to_string(),
                ));
            }
            let l = operand_to_formula_checked(func, lhs)?;
            let r = operand_to_formula_checked(func, rhs)?;
            let machine = operation_machine_int_info(func, None, lhs, Some(rhs));
            let (width, signed) = machine.map_or((None, false), |(w, s)| (Some(w), s));
            try_binop_to_formula(*op, l, r, width, signed)
        }
        Rvalue::UnaryOp(UnOp::Neg, op)
            if operation_has_machine_int_family(func, None, op, None) =>
        {
            // Wrap-exact machine negation: `0 -w x` through the same
            // `IntToBv`/`BvToInt` bridge as the machine `Not` arm below and
            // `wrapping_machine_binop_to_formula`. Exact on every execution
            // that reaches the consumer: a checked build panics on `-MIN`
            // before the value can flow (the overflow assert dominates), and
            // a wrapping build produces exactly this pattern. The former
            // blanket refusal here silently DROPPED the `_0 = -x` return pin
            // in the body-aware postcondition lane (the pin loop treats
            // `Err` as "no pin"), leaving the return slot FREE and turning
            // the provable branched-`ensures` row into a satisfiable — and
            // then refutation-demoted — query.
            match operation_machine_int_info(func, None, op, None) {
                Some((width, signed)) => {
                    let value = operand_to_formula_checked(func, op)?;
                    Ok(Formula::BvToInt(
                        Box::new(Formula::BvSub(
                            Box::new(Formula::IntToBv(Box::new(Formula::Int(0)), width)),
                            Box::new(Formula::IntToBv(Box::new(value), width)),
                            width,
                        )),
                        width,
                        signed,
                    ))
                }
                None => Err(unsupported_chc_lowering(
                    "Rvalue::UnaryOp(Neg)",
                    "machine negation without a resolvable width/signedness".to_string(),
                )),
            }
        }
        Rvalue::UnaryOp(UnOp::Neg, op) => {
            Ok(Formula::Neg(Box::new(operand_to_formula_checked(func, op)?)))
        }
        Rvalue::UnaryOp(UnOp::Not, op) => {
            let value = operand_to_formula_checked(func, op)?;
            let ty = crate::operand_ty_cow(func, op);
            match ty.as_deref() {
                Some(Ty::Bool) => Ok(Formula::Not(Box::new(value))),
                Some(ty) if machine_int_info(ty).is_some() => {
                    let (width, signed) = machine_int_info(ty)
                        .expect("guard established a supported machine-integer carrier");
                    Ok(Formula::BvToInt(
                        Box::new(Formula::BvNot(
                            Box::new(Formula::IntToBv(Box::new(value), width)),
                            width,
                        )),
                        width,
                        signed,
                    ))
                }
                Some(ty) if is_machine_int_family(ty) => Err(unsupported_chc_lowering(
                    "Rvalue::UnaryOp(Not)",
                    "bitwise not has an unsupported or unavailable machine width; unsigned mathematical-Int fallback is forbidden"
                        .to_string(),
                )),
                Some(other) => Err(unsupported_chc_lowering(
                    "Rvalue::UnaryOp(Not)",
                    format!("bitwise/logical not is not modeled for type {other:?}"),
                )),
                None => Err(unsupported_chc_lowering(
                    "Rvalue::UnaryOp(Not)",
                    "operand type is unknown".to_string(),
                )),
            }
        }
        Rvalue::UnaryOp(UnOp::PtrMetadata, _) => Err(unsupported_chc_lowering(
            "Rvalue::UnaryOp(PtrMetadata)",
            "pointer metadata extraction requires fat-pointer metadata semantics".to_string(),
        )),
        Rvalue::Cast(op, to_ty) => cast_to_formula_checked(func, op, to_ty, dest),
        Rvalue::Ref { place, .. } => {
            // Model a reference as a fresh symbolic variable representing the
            // address/pointer.  The variable name encodes the place so that
            // two references to the same place unify.
            validate_place_supported(place, "Rvalue::Ref place")?;
            let place_name = crate::place_to_var_name(func, place);
            Ok(Formula::Var(generated_chc_symbol(&format!("ref_{place_name}")), Sort::Int))
        }
        Rvalue::Aggregate(AggregateKind::RawPtr { pointee_ty, mutable }, operands) => {
            let data_operand =
                raw_ptr_aggregate_data_operand(func, pointee_ty, *mutable, operands)?;
            operand_to_formula_checked(func, data_operand)
        }
        Rvalue::Aggregate(kind, operands) => {
            // For single-element aggregates (common: newtype wrappers, single-variant
            // enums), propagate the inner value. Multi-element aggregates require
            // field-sensitive value semantics and must fail closed.
            validate_aggregate_kind_supported(kind)?;
            if operands.len() == 1 {
                operand_to_formula_checked(func, &operands[0])
            } else {
                Err(unsupported_chc_lowering(
                    "Rvalue::Aggregate",
                    format!(
                        "multi-element aggregate with {} operands is not modeled",
                        operands.len()
                    ),
                ))
            }
        }
        Rvalue::Discriminant(place) => {
            // The discriminant is an integer tag for the enum variant.
            validate_place_supported(place, "Rvalue::Discriminant place")?;
            let place_name = crate::place_to_var_name(func, place);
            Ok(Formula::Var(crate::discriminant_formula_var_name(&place_name), Sort::Int))
        }
        Rvalue::Len(place) => {
            // Length is a non-negative integer property of the place.
            validate_place_supported(place, "Rvalue::Len place")?;
            let place_name = crate::place_to_var_name(func, place);
            Ok(Formula::Var(generated_chc_symbol(&format!("len_{place_name}")), Sort::Int))
        }
        Rvalue::Repeat(op, _) => operand_to_formula_checked(func, op),
        Rvalue::AddressOf(_, _) => Err(unsupported_chc_lowering(
            "Rvalue::AddressOf",
            "raw pointer creation requires provenance/address semantics".to_string(),
        )),
        Rvalue::CopyForDeref(place) => {
            validate_place_supported(place, "Rvalue::CopyForDeref place")?;
            let place_name = crate::place_to_var_name(func, place);
            Ok(Formula::Var(place_name, Sort::Int))
        }
        Rvalue::Unsupported { kind, detail, .. } => {
            Err(unsupported_chc_lowering(kind.clone(), detail.clone()))
        }
        _ => Err(unsupported_chc_lowering(
            "Rvalue::<unknown>",
            "non-exhaustive rvalue variant is not modeled by CHC lowering".to_string(),
        )),
    }
}

pub(crate) fn operand_to_formula_checked(
    func: &VerifiableFunction,
    op: &Operand,
) -> Result<Formula, ChcError> {
    match op {
        Operand::Copy(place) | Operand::Move(place) => {
            validate_place_supported(place, "operand place")?;
            Ok(crate::operand_to_formula(func, op))
        }
        Operand::Constant(cv) => const_value_to_formula_checked(cv),
        Operand::Symbolic(formula) => Ok(formula.clone()),
        Operand::Unsupported { kind, detail } => {
            Err(unsupported_chc_lowering(kind.clone(), detail.clone()))
        }
        _ => Err(unsupported_chc_lowering(
            "Operand::<unknown>",
            "non-exhaustive operand variant is not modeled by CHC lowering".to_string(),
        )),
    }
}

fn const_value_to_formula_checked(cv: &ConstValue) -> Result<Formula, ChcError> {
    match cv {
        ConstValue::Bool(b) => Ok(Formula::Bool(*b)),
        ConstValue::Int(n) => Ok(Formula::Int(*n)),
        ConstValue::Uint(n, _) => Ok(match i128::try_from(*n) {
            Ok(n) => Formula::Int(n),
            Err(_) => Formula::UInt(*n),
        }),
        ConstValue::Float(f) => Ok(Formula::BitVec { value: i128::from(f.to_bits()), width: 64 }),
        ConstValue::FloatBits { bits, width } => match i128::try_from(*bits) {
            Ok(value) => Ok(Formula::BitVec { value, width: *width }),
            Err(_) => Err(unsupported_chc_lowering(
                "ConstValue::FloatBits",
                format!("bit pattern 0x{bits:x} does not fit Formula::BitVec i128 storage"),
            )),
        },
        ConstValue::Unit => Ok(Formula::Int(0)),
        ConstValue::CallableItem { def_path, kind, def_path_hash } => Ok(Formula::var_owned(
            ConstValue::callable_smt_var_name(def_path, *kind, *def_path_hash),
            Sort::Int,
        )),
        ConstValue::Str { bytes } => {
            Ok(Formula::var_owned(ConstValue::str_smt_var_name(bytes), Sort::Int))
        }
        // A typed opaque integer constant: a fresh integer-sorted symbol asserting
        // no value (sound over-approximation). Lowering to a CHC ERROR instead would
        // poison via the shared ERROR relation (the GEP lesson), so emit the
        // unconstrained symbol — value/div/index obligations over it stay unknown.
        ConstValue::OpaqueScalar { width, signed } => Ok(Formula::var_owned(
            format!("__trust_opaque_scalar_{}{}", if *signed { "i" } else { "u" }, width),
            Sort::Int,
        )),
        // Trust: piece #7a — a const-generic PARAM value on the NATIVE (`-full`)
        // path. It MUST mint the SAME per-param symbol `__trust_constparam_*` (via
        // `const_param_symbol`) that the general `operand_to_formula` path and the array
        // length use, so strict verification shares the SMT term between the
        // guard `i < N` and the bounds VC. SOUNDNESS: keyed on the param identity,
        // never on `(width, signed)`; the symbol asserts no value.
        ConstValue::ConstParam { index, name, .. } => {
            Ok(Formula::var_owned(trust_types::const_param_symbol(*index, name), Sort::Int))
        }
        _ => Err(unsupported_chc_lowering(
            "ConstValue::<unknown>",
            "non-exhaustive constant variant is not modeled by CHC lowering".to_string(),
        )),
    }
}

fn cast_to_formula_checked(
    func: &VerifiableFunction,
    op: &Operand,
    to_ty: &Ty,
    dest: Option<(&str, Sort, Option<(u32, bool)>, bool)>,
) -> Result<Formula, ChcError> {
    let from_ty = crate::operand_ty(func, op).ok_or_else(|| {
        unsupported_chc_lowering(
            "Rvalue::Cast",
            format!("source operand type is unavailable for cast to {to_ty:?}"),
        )
    })?;

    if matches!(&from_ty, Ty::Bool) && to_ty.is_integer() {
        let value = operand_to_formula_checked(func, op)?;
        return Ok(Formula::Ite(
            Box::new(value),
            Box::new(Formula::Int(1)),
            Box::new(Formula::Int(0)),
        ));
    }

    if crate::is_callable_reification_cast(&from_ty, to_ty) {
        let Some((dest_name, sort, _, _)) = dest else {
            return Err(unsupported_chc_lowering(
                "Rvalue::Cast",
                "callable reification requires assignment destination for stable opaque token"
                    .to_string(),
            ));
        };
        return Ok(crate::callable_reification_token(dest_name, sort));
    }

    if crate::is_modeled_identity_cast(&from_ty, to_ty) {
        return operand_to_formula_checked(func, op);
    }

    // float `as` casts (int<->float, float->float) are infallible; model the
    // result as a fresh unconstrained value of the destination sort instead of
    // refusing — sound (the value is not asserted, so float-value-dependent
    // obligations stay `unknown`, never falsely proved) and stops the cast from
    // wedging the whole function at Unsupported.
    if crate::is_float_numeric_cast(&from_ty, to_ty) {
        let Some((dest_name, sort, _, _)) = dest else {
            return Err(unsupported_chc_lowering(
                "Rvalue::Cast",
                "float cast requires an assignment destination for a stable fresh value"
                    .to_string(),
            ));
        };
        return Ok(Formula::Var(format!("__trust_float_cast_{dest_name}"), sort));
    }

    // A pointer→integer cast (the `*const _ -> usize` address-exposure leg of the
    // `vec!`/box-machinery alignment & null checks) exposes a pointer's address as an
    // arbitrary integer. Model the result as a fresh unconstrained value of the
    // destination sort — sound (the address is not asserted, so any derived
    // obligation on it stays `unknown`, never falsely proved) — instead of refusing,
    // which wedged the whole function at Unsupported. Mirrors the float-cast case.
    if from_ty.is_pointer_like() && to_ty.is_integer() {
        let Some((dest_name, sort, _, _)) = dest else {
            return Err(unsupported_chc_lowering(
                "Rvalue::Cast",
                "pointer-to-integer cast requires an assignment destination for a stable fresh value"
                    .to_string(),
            ));
        };
        return Ok(Formula::Var(format!("__trust_ptr_addr_{dest_name}"), sort));
    }

    // `&[T; N] -> &[T]` unsize is a metadata-only coercion: the reference value
    // flows through identically (slice len is the array's static N), so it lowers
    // to the source operand's formula and introduces no new obligation. Checked
    // before the type-lost fallback below so well-typed casts keep this precision.
    if crate::is_array_to_slice_ref_cast(&from_ty, to_ty) {
        return operand_to_formula_checked(func, op);
    }

    // array→slice unsize whose source lost its `&[T;N]` type (a promoted array
    // constant, or a fat-pointer-element array): metadata-only, no obligation.
    // Model the result as a fresh opaque slice (length unconstrained) instead of
    // refusing — sound, and keeps the function's other obligations decidable.
    //
    // Restricted to REFERENCE targets (`&[T]`): `cast_target_is_slice_ref` also
    // matches `*const [T]` raw pointers, but a thin→fat *raw pointer* cast
    // fabricates slice metadata from a bare pointer (provenance/UB-adjacent), a
    // genuinely-unsupported operation that must stay fail-closed below — distinct
    // from a value-preserving reference unsize.
    if crate::cast_target_is_slice_ref(to_ty) && matches!(to_ty, Ty::Ref { .. }) {
        let Some((dest_name, sort, _, _)) = dest else {
            return Err(unsupported_chc_lowering(
                "Rvalue::Cast",
                "array→slice cast requires an assignment destination for a stable fresh value"
                    .to_string(),
            ));
        };
        return Ok(Formula::Var(format!("__trust_slice_cast_{dest_name}"), sort));
    }

    Err(unsupported_chc_lowering(
        "Rvalue::Cast",
        format!(
            "unsupported cast {from_ty:?} -> {to_ty:?}; {}",
            crate::unsupported_cast_reason(&from_ty, to_ty)
        ),
    ))
}

fn validate_place_supported(place: &Place, context: &str) -> Result<(), ChcError> {
    for projection in &place.projections {
        match projection {
            Projection::Field(_)
            | Projection::Index(_)
            | Projection::Deref
            | Projection::Downcast(_)
            | Projection::OpaqueCast(_)
            | Projection::UnwrapUnsafeBinder(_)
            | Projection::ConstantIndex { .. }
            | Projection::Subslice { .. } => {}
            _ => {
                return Err(unsupported_chc_lowering(
                    "Projection::<unknown>",
                    format!("{context} contains a projection not modeled by CHC lowering"),
                ));
            }
        }
    }
    Ok(())
}

fn validate_aggregate_kind_supported(kind: &AggregateKind) -> Result<(), ChcError> {
    match kind {
        AggregateKind::Tuple
        | AggregateKind::Array
        | AggregateKind::Adt { active_field: None, .. } => Ok(()),
        AggregateKind::Adt { name, variant, active_field: Some(active_field), .. } => {
            Err(unsupported_chc_lowering(
                "AggregateKind::Adt(active_field)",
                format!(
                    "union-like aggregate {name} variant {variant} active_field {active_field} is not modeled"
                ),
            ))
        }
        AggregateKind::Closure { name, .. } => Err(unsupported_chc_lowering(
            "AggregateKind::Closure",
            format!("closure aggregate {name} requires captured-environment semantics"),
        )),
        AggregateKind::Coroutine { name } => Err(unsupported_chc_lowering(
            "AggregateKind::Coroutine",
            format!("coroutine aggregate {name} requires generator-state semantics"),
        )),
        AggregateKind::CoroutineClosure { name } => Err(unsupported_chc_lowering(
            "AggregateKind::CoroutineClosure",
            format!("coroutine-closure aggregate {name} requires async closure semantics"),
        )),
        AggregateKind::RawPtr { .. } => Err(unsupported_chc_lowering(
            "AggregateKind::RawPtr",
            "raw pointer aggregate requires data-pointer/metadata semantics".to_string(),
        )),
        _ => Err(unsupported_chc_lowering(
            "AggregateKind::<unknown>",
            "non-exhaustive aggregate kind is not modeled by CHC lowering".to_string(),
        )),
    }
}

fn raw_ptr_aggregate_data_operand<'a>(
    func: &VerifiableFunction,
    pointee_ty: &Ty,
    mutable: bool,
    operands: &'a [Operand],
) -> Result<&'a Operand, ChcError> {
    if let Some(detail) =
        crate::raw_ptr_aggregate_support_error(func, pointee_ty, mutable, operands)
    {
        return Err(unsupported_chc_lowering("AggregateKind::RawPtr", detail));
    }

    Ok(&operands[0])
}

fn unsupported_chc_lowering(kind: impl Into<String>, detail: impl Into<String>) -> ChcError {
    ChcError::UnsupportedMir { kind: kind.into(), detail: detail.into() }
}

/// A non-negative integer literal, if `f` is one.
fn nonneg_int_literal(f: &Formula) -> Option<u128> {
    match f {
        Formula::Int(v) if *v >= 0 => Some(*v as u128),
        Formula::UInt(v) => Some(*v),
        _ => None,
    }
}

/// `2^k` as a Formula (Int when it fits, UInt for the 2^127 top case).
fn pow2_formula(k: u32) -> Formula {
    let pow = 1u128 << k;
    match i128::try_from(pow) {
        Ok(v) => Formula::Int(v),
        Err(_) => Formula::UInt(pow),
    }
}

/// Lower a shift by a CONSTANT in-range amount to pure linear arithmetic,
/// bypassing the Int→BV→Int bridge. Returns `None` (caller keeps the sound BV
/// encoding) for every case not covered.
///
/// Covered cases, each an EXACT machine-semantics identity:
///
/// * fully-constant UNSIGNED `x >> k` / `x << k` — folded to the literal
///   result (`<<` with the w-bit wrap Rust release semantics has; a shift
///   whose amount is out of range stays on the BV path — the checked-shift
///   obligation owns that case).
/// * UNSIGNED `x >> k` (variable `x`) — `x div 2^k`. `Formula::Div` lowers to
///   Rust TRUNCATED division (see smtlib.rs); for the non-negative values an
///   unsigned operand takes in every real execution, truncated == floor ==
///   logical shift, so `dest = x div 2^k` is true of every execution.
///   Conjoined as a definition hypothesis it is therefore monotone-sound: a
///   real counterexample still satisfies it (never masked), and it can only
///   prune UNREAL models (the same argument as `shift_result_range`).
///
/// NOT covered (deliberately):
/// * SIGNED `>>` — arithmetic shift rounds toward -inf, truncated division
///   rounds toward zero; they disagree on negative values.
/// * variable-lhs `<<` — the w-bit wrap needs a mod, whose truncated-`Rem`
///   rendering differs from the always-nonneg machine wrap on signed types.
/// * variable shift amounts — nothing linear to say.
fn const_shift_to_linear(
    op: BinOp,
    lhs: &Formula,
    rhs: &Formula,
    w: u32,
    signed: bool,
) -> Option<Formula> {
    if !matches!(op, BinOp::Shl | BinOp::Shr) || signed {
        return None;
    }
    let k = nonneg_int_literal(rhs)?;
    if k >= u128::from(w) || k >= 128 {
        return None;
    }
    let k = k as u32;
    if let Some(x) = nonneg_int_literal(lhs) {
        // Fully-constant fold with exact w-bit machine semantics.
        let mask = if w >= 128 { u128::MAX } else { (1u128 << w) - 1 };
        let value = match op {
            BinOp::Shl => (x << k) & mask,
            BinOp::Shr => (x & mask) >> k,
            _ => unreachable!("gated to Shl|Shr above"),
        };
        return Some(match i128::try_from(value) {
            Ok(v) => Formula::Int(v),
            Err(_) => Formula::UInt(value),
        });
    }
    match op {
        BinOp::Shr => Some(Formula::Div(Box::new(lhs.clone()), Box::new(pow2_formula(k)))),
        _ => None,
    }
}

/// Exact wrapping value of an ordinary fixed-width MIR arithmetic operation.
/// CHC state remains Int-sorted at the predicate boundary, so convert the
/// operands to their w-bit representation, perform the machine operation, then
/// reinterpret the result in the source type's signed/unsigned domain.
fn wrapping_machine_binop_to_formula(
    op: BinOp,
    lhs: Formula,
    rhs: Formula,
    width: u32,
    signed: bool,
) -> Result<Formula, ChcError> {
    let lhs_bv = Box::new(Formula::IntToBv(Box::new(lhs), width));
    let rhs_bv = Box::new(Formula::IntToBv(Box::new(rhs), width));
    let value = match op {
        BinOp::Add => Formula::BvAdd(lhs_bv, rhs_bv, width),
        BinOp::Sub => Formula::BvSub(lhs_bv, rhs_bv, width),
        BinOp::Mul => Formula::BvMul(lhs_bv, rhs_bv, width),
        _ => {
            return Err(unsupported_chc_lowering(
                "Rvalue::BinaryOp",
                format!("{op:?} has no exact wrapping CHC lowering"),
            ));
        }
    };
    Ok(Formula::BvToInt(Box::new(value), width, signed))
}

/// Fallible binary operation lowering used by CHC encoding — the only entry
/// point, so an op outside the encodable fragment surfaces as a `ChcError` the
/// caller turns into an unsupported-MIR obligation rather than a crash.
///
/// `width` is the bit width of the integer operands (from `Ty::int_width()`).
/// When provided, bitwise operations (BitAnd, BitOr, BitXor, Shl, Shr) are
/// translated to proper bitvector formulas (BvAnd, BvOr, BvXor, BvShl, BvLShr)
/// with IntToBv/BvToInt bridges. When `None`, defaults to 64 bits.
pub fn try_binop_to_formula(
    op: BinOp,
    lhs: Formula,
    rhs: Formula,
    width: Option<u32>,
    signed: bool,
) -> Result<Formula, ChcError> {
    match op {
        BinOp::Add => Ok(Formula::Add(Box::new(lhs), Box::new(rhs))),
        BinOp::Sub => Ok(Formula::Sub(Box::new(lhs), Box::new(rhs))),
        BinOp::Mul => Ok(Formula::Mul(Box::new(lhs), Box::new(rhs))),
        BinOp::Div => Ok(Formula::Div(Box::new(lhs), Box::new(rhs))),
        BinOp::Rem => Ok(Formula::Rem(Box::new(lhs), Box::new(rhs))),
        BinOp::Eq => Ok(Formula::Eq(Box::new(lhs), Box::new(rhs))),
        BinOp::Ne => Ok(Formula::Not(Box::new(Formula::Eq(Box::new(lhs), Box::new(rhs))))),
        BinOp::Lt => Ok(Formula::Lt(Box::new(lhs), Box::new(rhs))),
        BinOp::Le => Ok(Formula::Le(Box::new(lhs), Box::new(rhs))),
        BinOp::Gt => Ok(Formula::Gt(Box::new(lhs), Box::new(rhs))),
        BinOp::Ge => Ok(Formula::Ge(Box::new(lhs), Box::new(rhs))),
        // Three-way comparison: ITE(a < b, -1, ITE(a == b, 0, 1))
        BinOp::Cmp => Ok(Formula::Ite(
            Box::new(Formula::Lt(Box::new(lhs.clone()), Box::new(rhs.clone()))),
            Box::new(Formula::Int(-1)),
            Box::new(Formula::Ite(
                Box::new(Formula::Eq(Box::new(lhs), Box::new(rhs))),
                Box::new(Formula::Int(0)),
                Box::new(Formula::Int(1)),
            )),
        )),
        BinOp::BitAnd | BinOp::BitOr | BinOp::BitXor | BinOp::Shl | BinOp::Shr => {
            let w = width.unwrap_or(64);
            // A shift by a CONSTANT in-range amount lowers to PURE LINEAR
            // ARITHMETIC instead of the IntToBv/BvToInt bridge below. The
            // mixed Int/BV round-trip (`bv2nat(zero_extend(extract(int2bv x)))`
            // after solver-side elaboration) is undecidable for ay's LRA/LIA
            // ("simplex=Sat but unsupported") — it is what left every
            // `x >> 5`-shaped VC Unknown in aterm-lz4's compress loop and fed
            // the 2026-07-05 divergence. `x div 2^k` is decidable LIA and is
            // the EXACT machine value on the covered cases (see
            // `const_shift_to_linear` for the case analysis and soundness).
            if let Some(linear) = const_shift_to_linear(op, &lhs, &rhs, w, signed) {
                return Ok(linear);
            }
            // Translate bitwise ops to bitvector formulas.
            // Operands are in integer domain (Sort::Int), so we bridge via
            // IntToBv/BvToInt to maintain sort compatibility with the rest of
            // the formula tree.
            let lhs_bv = Box::new(Formula::IntToBv(Box::new(lhs), w));
            let rhs_bv = Box::new(Formula::IntToBv(Box::new(rhs), w));
            let bv_result = match op {
                BinOp::BitAnd => Formula::BvAnd(lhs_bv, rhs_bv, w),
                BinOp::BitOr => Formula::BvOr(lhs_bv, rhs_bv, w),
                BinOp::BitXor => Formula::BvXor(lhs_bv, rhs_bv, w),
                BinOp::Shl => Formula::BvShl(lhs_bv, rhs_bv, w),
                // Use arithmetic right shift for signed types,
                // logical right shift for unsigned.
                BinOp::Shr if signed => Formula::BvAShr(lhs_bv, rhs_bv, w),
                BinOp::Shr => Formula::BvLShr(lhs_bv, rhs_bv, w),
                _ => unreachable!(
                    "bitvector lowering only handles bitwise and shift BinOp variants selected by the outer match"
                ),
            };
            // Bridge back to integer domain for compatibility with overflow/range checks.
            //
            // soundness-signed-shift: the bridge MUST reinterpret the
            // result bit-pattern in the operand TYPE's domain — signed for a
            // signed type, unsigned for an unsigned one. Hardcoding `false`
            // (bv2nat, range [0, 2^w-1]) is only correct for unsigned types; for
            // a signed type it reads a negative result (sign bit set) as a large
            // positive value. That value then CONTRADICTS the signed
            // `input_range_constraint([-2^(w-1), 2^(w-1)-1])` the overflow VC
            // conjoins on this same operand, making the hypothesis set UNSAT and
            // VACUOUSLY PROVING any overflow whose only witness lies in the
            // negative half of the result. Confirmed false-PROVE: for `i32`,
            // `(x >> 1) - 2_000_000_000` genuinely underflows at `x == i32::MIN`
            // (real Rust panics) yet was reported `proved`. Bridging with the
            // op's actual signedness keeps the def fact in the same value-space
            // as the range constraint, so the negative half is no longer masked.
            // Sound for unsigned (unchanged: `signed == false`).
            Ok(Formula::BvToInt(Box::new(bv_result), w, signed))
        }
        _ => Err(unsupported_chc_lowering(
            "BinOp::<unknown>",
            "non-exhaustive binary operation is not modeled by CHC lowering".to_string(),
        )),
    }
}

/// Build a precondition formula from function contracts and parameter constraints.
fn build_precondition(func: &VerifiableFunction) -> Formula {
    if func.preconditions.is_empty() {
        Formula::Bool(true)
    } else if func.preconditions.len() == 1 {
        func.preconditions[0].clone()
    } else {
        Formula::And(func.preconditions.clone())
    }
}

/// Build a postcondition formula from function contracts.
fn build_postcondition(func: &VerifiableFunction) -> Formula {
    if func.postconditions.is_empty() {
        Formula::Bool(true)
    } else if func.postconditions.len() == 1 {
        func.postconditions[0].clone()
    } else {
        Formula::And(func.postconditions.clone())
    }
}

// ---- Loop-CHC safety-query violation extractor (Step B) ----
// The VIOLATION-FORMULA extractor. Given a loop-carried safety obligation, build
// the tree `Formula` violation (Lt(a,b) for unsigned `a-b`; Ge(i,len) for a
// slice index) and the loop-continuation condition, ready for
// `encode_loop_safety_query(&predicate, loop_cond, violation, header)`.
//
// Uses ONLY: the tree `Formula` constructors, `LoopInfo`, and MIR-lowering that
// already exists — `crate::operand_to_formula` (lib.rs:2401),
// `crate::operand_ty_cow` (lib.rs:820), `rvalue_to_formula` (this file:500),
// `extract_loop_condition` (this file:386), and the two helpers promoted above.
//
// SOUNDNESS mitigation (b) — the violation is the FAITHFUL negation of the
// safety condition and is NEVER vacuous: it is the exact bad-state formula the
// single-formula lane checks (reused, not re-derived), and any syntactically
// trivially-UNSAT violation is REJECTED (returns None => single-formula fallback)
// so a `loop_cond ∧ violation` can never be UNSAT independent of the invariant
// (which would "discharge" the query while proving nothing about the real access).

/// A loop-carried safety obligation whose violation feeds the safety query.
///
/// Operand/place references are borrowed from the MIR the L0 emit site already
/// holds; the extractor phrases the violation over the SAME variable names
/// (`crate::operand_to_formula` names locals by `decl.name`) that
/// `collect_modified_variables` uses for the invariant predicate's pre-state, so
/// the violation binds directly to `predicate.apply_unprimed()`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LoopSafetyPoint {
    /// The obligation is evaluated after the header comparison and before any
    /// non-header body statement executes.
    HeaderEntry,
}

pub enum LoopSafetyObligation<'a> {
    /// Legacy unlocated form. It is retained for source compatibility but is
    /// never proof-producing: a body operation cannot safely be assumed to use
    /// header-entry values without an explicit phase.
    /// Unsigned `a - b` subtraction: underflows (panics) exactly when `a < b`.
    /// Violation = `Lt(a, b)` — the faithful negation of the safety cond `a >= b`.
    UnsignedSub { a: &'a Operand, b: &'a Operand },
    /// Located unsigned subtraction. The current narrow lane supports only
    /// [`LoopSafetyPoint::HeaderEntry`].
    UnsignedSubAt { a: &'a Operand, b: &'a Operand, point: LoopSafetyPoint },
    /// Legacy unlocated form; retained but deliberately inapplicable.
    /// `collection[index]` load/store: out-of-bounds exactly when
    /// `index >= len` (unsigned index) or `index < 0 ∨ index >= len` (signed).
    /// Violation is built by the shared `index_bounds_violation`.
    Index { collection: &'a Place, collection_ty: &'a Ty, index: &'a Operand },
    /// Located index obligation. The current narrow lane supports only header
    /// entry; statement-prefix state needs a phased transition relation.
    IndexAt {
        collection: &'a Place,
        collection_ty: &'a Ty,
        index: &'a Operand,
        point: LoopSafetyPoint,
    },
}

/// Build the `(loop_cond, violation)` pair for a loop-carried safety obligation.
///
/// Returns `None` — the caller MUST then fall back to the single-formula lane,
/// never silently drop the obligation — when the violation cannot be faithfully
/// lowered (unresolved collection length) or would be vacuously UNSAT.
pub(crate) fn extract_loop_safety_query_inputs(
    func: &VerifiableFunction,
    loop_info: &LoopInfo,
    obligation: &LoopSafetyObligation<'_>,
) -> Option<(Formula, Formula)> {
    let violation = build_loop_violation(func, obligation)?;
    // `extract_loop_condition` is fail-closed by construction (Bool(true) when
    // the header is unrecognized); an Err only on unsupported discriminant
    // lowering, in which case we fall back rather than emit a partial query.
    let loop_cond = build_loop_cond_with_arithmetic(func, loop_info).ok()?;
    Some((loop_cond, violation))
}

/// Build the faithful violation `Formula`, phrased over pre-state variable names.
pub(crate) fn build_loop_violation(
    func: &VerifiableFunction,
    obligation: &LoopSafetyObligation<'_>,
) -> Option<Formula> {
    let violation = match obligation {
        LoopSafetyObligation::UnsignedSub { .. } | LoopSafetyObligation::Index { .. } => {
            return None;
        }
        LoopSafetyObligation::UnsignedSubAt { a, b, point: LoopSafetyPoint::HeaderEntry } => {
            // `a < b` is the exact underflow condition only for same-width
            // unsigned machine subtraction. Int-sorted signed, symbolic, or
            // mixed-width operands need a different overflow predicate and
            // must not borrow this obligation tag.
            let a_ty = crate::operand_ty_cow(func, a)?;
            let b_ty = crate::operand_ty_cow(func, b)?;
            let unsigned_machine = |ty: &Ty| match ty {
                Ty::Int { width, signed: false } if (1..=128).contains(width) => Some(*width),
                Ty::PtrSizedInt { signed: false } => Some(64),
                _ => None,
            };
            let width = unsigned_machine(a_ty.as_ref())?;
            if unsigned_machine(b_ty.as_ref()) != Some(width) {
                return None;
            }
            // Equivalent to `Lt(Sub(a,b), Int(0))` used at generate.rs:18013, but
            // the bare `Lt(a,b)` is the simpler faithful negation in the Int theory.
            let a_f = operand_to_formula_checked(func, a).ok()?;
            let b_f = operand_to_formula_checked(func, b).ok()?;
            Formula::Lt(Box::new(a_f), Box::new(b_f))
        }
        LoopSafetyObligation::IndexAt {
            collection,
            collection_ty,
            index,
            point: LoopSafetyPoint::HeaderEntry,
        } => {
            // The public obligation carries a type for convenience, but that
            // caller-owned field cannot override the function's actual place
            // type. Likewise, unknown/BV-only index provenance must not default
            // to unsigned and silently omit the negative-index arm.
            let actual_collection_ty = crate::place_ty_cow(func, collection)?;
            if actual_collection_ty.as_ref() != *collection_ty {
                return None;
            }
            let index_ty = crate::operand_ty_cow(func, index)?;
            match index_ty.as_ref() {
                Ty::Int { width, .. } if (1..=128).contains(width) => {}
                Ty::PtrSizedInt { .. } => {}
                _ => return None,
            }
            // Reuse the EXACT length + violation lowering of the L0 bounds lane.
            let len =
                crate::rvalue_safety::collection_len_formula(func, collection, collection_ty)?;
            let index_f = operand_to_formula_checked(func, index).ok()?;
            crate::rvalue_safety::index_bounds_violation(index_f, Some(index_ty.as_ref()), len)
        }
    };

    // Mitigation (b): a trivially-UNSAT violation would discharge VACUOUSLY.
    if violation_is_trivially_unsat(&violation) {
        return None;
    }
    Some(violation)
}

/// Exact loop-continuation condition for the safety query.
///
/// The header's comparison temporary is recomputed before every switch and is
/// deliberately *not* invariant state.  Reusing that temporary after the body
/// update creates a stale-header transition and can admit one extra iteration.
/// This proof-producing lane therefore requires and lowers the comparison itself;
/// unrecognized headers are inapplicable rather than approximated.
pub(crate) fn build_loop_cond_with_arithmetic(
    func: &VerifiableFunction,
    loop_info: &LoopInfo,
) -> Result<Formula, ChcError> {
    exact_header_loop_condition(func, loop_info).ok_or_else(|| ChcError::EncodingFailed {
        reason: format!(
            "loop header {} is outside the exact comparison fragment",
            loop_info.header.0
        ),
    })
}

/// Lower the header block's `cond = (i <cmp> n)` assignment to a `Formula`, with
/// the polarity matching the sole explicit edge that enters the body.  The
/// supported header contains exactly that one assignment: accepting additional
/// header effects would omit them from the body transition.
fn exact_header_loop_condition(func: &VerifiableFunction, loop_info: &LoopInfo) -> Option<Formula> {
    let header = chc_block(func, loop_info.header.0)?;
    let Terminator::SwitchInt { discr, targets, otherwise, .. } = &header.terminator else {
        return None;
    };

    let body_set: FxHashSet<usize> = loop_info
        .body_blocks
        .iter()
        .map(|b| b.0)
        .filter(|block| *block != loop_info.header.0)
        .collect();
    if body_set.contains(&otherwise.0) {
        return None;
    }
    let mut body_edges = targets.iter().filter(|(_, target)| body_set.contains(&target.0));
    let (body_value, _) = body_edges.next()?;
    if body_edges.next().is_some() {
        return None;
    }

    // The discriminant must be a bare local we can trace to a comparison assign.
    let discr_local = match discr {
        Operand::Copy(p) | Operand::Move(p) if p.projections.is_empty() => p.local,
        _ => return None,
    };
    if !matches!(chc_local_decl(func, discr_local).map(|decl| &decl.ty), Some(Ty::Bool))
        || crate::operand_sort(func, discr) != Some(Sort::Bool)
    {
        return None;
    }

    let [Statement::Assign { place, rvalue, .. }] = header.stmts.as_slice() else {
        return None;
    };
    if place.local != discr_local || !place.projections.is_empty() || !is_comparison_rvalue(rvalue)
    {
        return None;
    }

    // Reuse the shared rvalue lowering so comparison semantics are identical to
    // the transition. Only boolean switch values have a meaningful polarity.
    let cmp = rvalue_to_formula(func, rvalue).ok()?;
    if trust_types::check_formula_sort(&cmp).ok() != Some(Sort::Bool) {
        return None;
    }
    match *body_value {
        1 => Some(cmp),
        0 => Some(Formula::Not(Box::new(cmp))),
        _ => None,
    }
}

fn is_comparison_rvalue(rvalue: &Rvalue) -> bool {
    matches!(
        rvalue,
        Rvalue::BinaryOp(
            BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge | BinOp::Eq | BinOp::Ne,
            _,
            _,
        ) | Rvalue::CheckedBinaryOp(
            BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge | BinOp::Eq | BinOp::Ne,
            _,
            _,
        )
    )
}

/// Conservative SYNTACTIC screen for a violation that is always false. Such a
/// violation makes `loop_cond ∧ violation` UNSAT independent of the invariant,
/// so the safety query would discharge without proving anything about the real
/// access. This is the encoder-boundary half of mitigation (b); the full
/// theory-level non-vacuity check is independently re-enforced downstream
/// (trust-bmc `validate_non_vacuous_mir_rule_binding`).
///
/// Note: a trivially-TRUE violation (e.g. `Ge(x, x)`) is deliberately NOT
/// rejected — it only makes the query MORE satisfiable (fail-closed), never a
/// false-PROVE.
fn violation_is_trivially_unsat(f: &Formula) -> bool {
    match f {
        Formula::Bool(false) => true,
        // `x < x` and `x > x` are unsatisfiable for a well-formed strict order.
        // This catches the aliased-operand bug (e.g. `Lt(i, i)` from `a == b`
        // name collision) that mitigation (b) calls out.
        Formula::Lt(a, b) | Formula::Gt(a, b) => a == b,
        // A disjunction is unsat only if EVERY arm is; a conjunction if ANY arm is.
        Formula::Or(arms) => !arms.is_empty() && arms.iter().all(violation_is_trivially_unsat),
        Formula::And(arms) => arms.iter().any(violation_is_trivially_unsat),
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn header_unsigned_sub<'a>(a: &'a Operand, b: &'a Operand) -> LoopSafetyObligation<'a> {
        LoopSafetyObligation::UnsignedSubAt { a, b, point: LoopSafetyPoint::HeaderEntry }
    }

    #[test]
    fn generated_theory_symbols_cannot_alias_source_variables() {
        // Every unqualified spelling below is a legal Rust source identifier.
        // The actual CHC-owned symbol must therefore live in the reserved `__`
        // namespace when it cohabits a Formula with source locals.
        let func = counting_loop_function();
        let place = Place::local(2); // source name `i`
        let formulas = [
            rvalue_to_formula(&func, &Rvalue::Ref { mutable: false, place: place.clone() })
                .expect("reference should lower"),
            rvalue_to_formula(&func, &Rvalue::Discriminant(place.clone()))
                .expect("discriminant should lower"),
            rvalue_to_formula(&func, &Rvalue::Len(place)).expect("length should lower"),
        ];
        let expected = [
            generated_chc_symbol("ref_i"),
            crate::discriminant_formula_var_name("i"),
            generated_chc_symbol("len_i"),
        ];
        for (formula, expected_name) in formulas.iter().zip(expected) {
            let Formula::Var(name, Sort::Int) = formula else {
                panic!("generated CHC leaf should be an integer variable, got {formula:?}")
            };
            assert_eq!(name, &expected_name);
            assert!(name.contains("__"));
        }

        let loop_info = LoopInfo {
            header: BlockId(0),
            _latch: BlockId(0),
            body_blocks: vec![],
            _exit_blocks: vec![],
            induction_vars: vec![],
        };
        let init = build_init_args(&func, &loop_info, &[("i".into(), Sort::Int)]);
        assert_eq!(init, vec![Formula::Var(generated_chc_symbol("init_i"), Sort::Int)]);
        assert_ne!(init[0].var_name(), Some("i_init"));
    }

    // ---- Loop-CHC extractor tests (Step B) ----
    #[test]
    fn test_violation_trivially_unsat_screen() {
        let x = || Formula::Var("x".into(), Sort::Int);
        let y = || Formula::Var("y".into(), Sort::Int);
        // Vacuous (always false) => rejected.
        assert!(violation_is_trivially_unsat(&Formula::Bool(false)));
        assert!(violation_is_trivially_unsat(&Formula::Lt(Box::new(x()), Box::new(x()))));
        assert!(violation_is_trivially_unsat(&Formula::Gt(Box::new(x()), Box::new(x()))));
        assert!(violation_is_trivially_unsat(&Formula::And(vec![
            Formula::Lt(Box::new(x()), Box::new(y())),
            Formula::Lt(Box::new(x()), Box::new(x())), // one unsat arm poisons the And
        ])));
        assert!(violation_is_trivially_unsat(&Formula::Or(vec![
            Formula::Lt(Box::new(x()), Box::new(x())),
            Formula::Gt(Box::new(y()), Box::new(y())),
        ])));
        // Genuine, satisfiable violations => accepted.
        assert!(!violation_is_trivially_unsat(&Formula::Lt(Box::new(x()), Box::new(y()))));
        assert!(!violation_is_trivially_unsat(&Formula::Ge(Box::new(x()), Box::new(y()))));
        // `Ge(x,x)` is trivially TRUE, not unsat => NOT rejected (fail-closed, fine).
        assert!(!violation_is_trivially_unsat(&Formula::Ge(Box::new(x()), Box::new(x()))));
    }

    #[test]
    fn test_unsigned_sub_violation_is_faithful_negation() {
        // In counting_loop_function: local 1 = "n", local 2 = "i".
        let func = counting_loop_function();
        let a = Operand::Copy(Place::local(1)); // n
        let b = Operand::Copy(Place::local(2)); // i
        let ob = header_unsigned_sub(&a, &b);
        let v = build_loop_violation(&func, &ob).expect("n - i has a faithful Lt(n, i) violation");
        match v {
            Formula::Lt(lhs, rhs) => {
                assert!(matches!(lhs.as_ref(), Formula::Var(name, _) if name == "n"));
                assert!(matches!(rhs.as_ref(), Formula::Var(name, _) if name == "i"));
            }
            other => panic!("expected Lt(n, i), got {other:?}"),
        }
    }

    #[test]
    fn test_unlocated_loop_safety_obligation_is_never_proof_producing() {
        let func = counting_loop_function();
        let loops = detect_loops(&func);
        let a = Operand::Copy(Place::local(1));
        let b = Operand::Copy(Place::local(2));
        let legacy = LoopSafetyObligation::UnsignedSub { a: &a, b: &b };

        assert!(build_loop_violation(&func, &legacy).is_none());
        assert!(
            try_build_loop_safety_chc_system(&func, &loops[0], &legacy)
                .expect("legacy location ambiguity is an applicability fallback")
                .is_none()
        );
    }

    #[test]
    fn test_unsigned_sub_aliased_operands_are_rejected_as_vacuous() {
        // `a - a` would lower to the always-false `Lt(i, i)` => must NOT become a
        // (vacuously discharging) safety query. Mitigation (b).
        let func = counting_loop_function();
        let same = Operand::Copy(Place::local(2)); // i
        let ob = header_unsigned_sub(&same, &same);
        assert!(build_loop_violation(&func, &ob).is_none());
    }

    #[test]
    fn test_unsigned_sub_rejects_signed_and_mixed_width_operands() {
        let mut func = counting_loop_function();
        let a = Operand::Copy(Place::local(1));
        let b = Operand::Copy(Place::local(2));
        let obligation = header_unsigned_sub(&a, &b);

        func.body.locals[1].ty = Ty::i32();
        func.body.locals[2].ty = Ty::i32();
        assert!(
            build_loop_violation(&func, &obligation).is_none(),
            "signed overflow must not use the unsigned a<b predicate"
        );

        func.body.locals[1].ty = Ty::u16();
        func.body.locals[2].ty = Ty::u32();
        assert!(
            build_loop_violation(&func, &obligation).is_none(),
            "mixed-width subtraction is not this exact MIR obligation"
        );
    }

    #[test]
    fn test_index_violation_requires_actual_collection_and_known_index_types() {
        let mut func = counting_loop_function();
        func.body.locals.push(LocalDecl {
            index: 4,
            ty: Ty::Array { elem: Box::new(Ty::u8()), len: 4 },
            name: Some("items".into()),
        });
        let collection = Place::local(4);
        let index = Operand::Copy(Place::local(2));
        let actual_ty = func.body.locals[4].ty.clone();
        let exact = LoopSafetyObligation::IndexAt {
            collection: &collection,
            collection_ty: &actual_ty,
            index: &index,
            point: LoopSafetyPoint::HeaderEntry,
        };
        assert!(matches!(build_loop_violation(&func, &exact), Some(Formula::Ge(_, _))));

        let forged_ty = Ty::Slice { elem: Box::new(Ty::u8()) };
        let mismatched = LoopSafetyObligation::IndexAt {
            collection: &collection,
            collection_ty: &forged_ty,
            index: &index,
            point: LoopSafetyPoint::HeaderEntry,
        };
        assert!(build_loop_violation(&func, &mismatched).is_none());

        func.body.locals[2].ty = Ty::Bool;
        assert!(
            build_loop_violation(&func, &exact).is_none(),
            "unknown/non-integer index provenance must not default to unsigned"
        );
    }

    #[test]
    fn test_loop_cond_carries_polarized_arithmetic() {
        // Header bb1 is `cond = i < n; switchInt(cond) -> [1: body]`. The exact
        // lane lowers `i < n` directly and does not carry the recomputed `cond`
        // temporary as stale invariant state.
        let func = counting_loop_function();
        let loops = detect_loops(&func);
        let loop_cond = build_loop_cond_with_arithmetic(&func, &loops[0]).expect("cond encodes");
        assert!(matches!(
            loop_cond,
            Formula::Lt(l, r)
                if matches!(l.as_ref(), Formula::Var(n, _) if n == "i")
                    && matches!(r.as_ref(), Formula::Var(n, _) if n == "n")
        ));
    }

    #[test]
    fn test_query_inputs_wire_into_encode_loop_safety_query() {
        // End-to-end at the encoder boundary: the extracted (loop_cond, violation)
        // pair feeds the existing `encode_loop_safety_query` and yields an additive
        // Safety query clause with one invariant premise.
        let func = counting_loop_function();
        let loops = detect_loops(&func);
        let a = Operand::Copy(Place::local(1)); // n
        let b = Operand::Copy(Place::local(2)); // i
        let ob = header_unsigned_sub(&a, &b);
        let (loop_cond, violation) =
            extract_loop_safety_query_inputs(&func, &loops[0], &ob).expect("inputs build");

        let pred = ChcPredicate { name: "inv_bb1".into(), params: vec![("i".into(), Sort::Int)] };
        let (clause, role) =
            encode_loop_safety_query(&pred, loop_cond, violation, loops[0].header.0);
        assert!(clause.head.is_none(), "safety query has head = false");
        assert_eq!(clause.body_atoms.len(), 1);
        assert!(matches!(role, ClauseRole::Safety));
        // The query constraint is `loop_cond ∧ violation` (And of both).
        assert!(matches!(&clause.constraint, Formula::And(v) if v.len() == 2));
    }

    #[test]
    fn test_build_loop_safety_chc_system_assembles_entry_inductive_safety() {
        // Step 4: the full assembled system has exactly {Entry, Inductive, Safety}
        // — the faithful loop semantics plus the additive safety query, and NO
        // functional exit-post query.
        let func = counting_loop_function();
        let loops = detect_loops(&func);
        let a = Operand::Copy(Place::local(1)); // n
        let b = Operand::Copy(Place::local(2)); // i
        let ob = header_unsigned_sub(&a, &b);

        let sys = try_build_loop_safety_chc_system(&func, &loops[0], &ob)
            .expect("contract-free input should not fail encoding")
            .expect("counting loop + unsigned-sub obligation assembles a system");

        assert_eq!(sys.predicates.len(), 1, "one invariant predicate");
        assert_eq!(sys.clauses.len(), 3, "entry + inductive + safety, no exit-post");
        assert_eq!(sys.roles, vec![ClauseRole::Entry, ClauseRole::Inductive, ClauseRole::Safety]);
        // No exit-post query snuck in: the only head-false clause is the safety query.
        let head_false: Vec<_> =
            sys.clauses.iter().zip(&sys.roles).filter(|(c, _)| c.head.is_none()).collect();
        assert_eq!(head_false.len(), 1, "exactly one query clause");
        assert!(matches!(head_false[0].1, ClauseRole::Safety), "and it is the Safety query");
    }

    #[test]
    fn test_build_loop_safety_chc_system_serializes_to_error_query() {
        // The assembled system round-trips through the transport serializer and
        // yields a well-formed typed-CHC obligation whose query targets the
        // synthetic `error` relation (head-false convention).
        let func = counting_loop_function();
        let loops = detect_loops(&func);
        let a = Operand::Copy(Place::local(1)); // n
        let b = Operand::Copy(Place::local(2)); // i
        let ob = header_unsigned_sub(&a, &b);

        let sys = try_build_loop_safety_chc_system(&func, &loops[0], &ob)
            .expect("contract-free input should not fail encoding")
            .expect("assembles");
        let json = chc_system_to_typed_chc_json(&sys).expect("serializes");

        assert_eq!(json["query"]["target"], "error", "query targets the synthetic error relation");
        // The safety query became a rule deriving `error`; the invariant predicate
        // plus `error` are both declared as relations.
        let relations = json["relations"].as_array().expect("relations array");
        assert!(
            relations.iter().any(|r| r["name"] == "error"),
            "error relation is declared, got {relations:?}"
        );
        assert!(relations.iter().any(|r| r["name"] == "inv_bb1"), "invariant relation is declared");
        // Three source clauses => three rules (entry, inductive, safety→error).
        assert_eq!(json["rules"].as_array().map(Vec::len), Some(3), "one rule per clause");
        let wire = json.to_string();
        assert!(
            wire.contains("\"op\":\"int_to_bv\"")
                && wire.contains("\"width\":32")
                && wire.contains("\"op\":\"bv_add\"")
                && wire.contains("\"op\":\"bv_to_int\"")
                && wire.contains("\"signed\":false"),
            "typed CHC transport must preserve the complete unsigned wrapping transition: {wire}"
        );
    }

    #[test]
    fn test_typed_chc_transport_preserves_signed_bv_reinterpretation() {
        let formula = Formula::BvToInt(
            Box::new(Formula::BvSub(
                Box::new(Formula::IntToBv(Box::new(Formula::Var("x".into(), Sort::Int)), 8)),
                Box::new(Formula::IntToBv(Box::new(Formula::Int(1)), 8)),
                8,
            )),
            8,
            true,
        );
        let mut vars = std::collections::BTreeMap::new();
        let json = chc_formula_to_typed_expr(&formula, &mut vars)
            .expect("signed wrapping expressions are in the typed CHC fragment");
        assert_eq!(json["op"], "bv_to_int");
        assert_eq!(json["signed"], true);
        assert_eq!(json["expr"]["op"], "bv_sub");
        assert_eq!(json["expr"]["lhs"]["op"], "int_to_bv");
        assert_eq!(json["expr"]["lhs"]["width"], 8);
    }

    /// Loop whose body BRANCHES: `while i<n { if cond { i += 1 } }`. `i` is written
    /// once but CONDITIONALLY, so `build_body_transition` would assert the too-strong
    /// unconditional `i' = i+1`. The faithfulness gate must reject it (rule b).
    fn branching_body_loop() -> VerifiableFunction {
        VerifiableFunction {
            name: "branch_loop".to_string(),
            def_path: "test::branch_loop".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::Unit, name: None },
                    LocalDecl { index: 1, ty: Ty::u32(), name: Some("n".into()) },
                    LocalDecl { index: 2, ty: Ty::u32(), name: Some("i".into()) },
                    LocalDecl { index: 3, ty: Ty::Bool, name: Some("cond".into()) },
                ],
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![Statement::Assign {
                            place: Place::local(2),
                            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(0, 64))),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Goto(BlockId(1)),
                    },
                    // header bb1: cond = i < n; switchInt(cond) -> [1: bb2], else bb4
                    BasicBlock {
                        id: BlockId(1),
                        stmts: vec![Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Lt,
                                Operand::Copy(Place::local(2)),
                                Operand::Copy(Place::local(1)),
                            ),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::SwitchInt {
                            discr: Operand::Copy(Place::local(3)),
                            targets: vec![(1, BlockId(2))],
                            otherwise: BlockId(4),
                            exhaustive_enum_unreachable: false,
                            span: SourceSpan::default(),
                        },
                    },
                    // bb2 (INTERNAL BRANCH): switchInt(cond) -> [1: bb3], else bb1
                    BasicBlock {
                        id: BlockId(2),
                        stmts: vec![],
                        terminator: Terminator::SwitchInt {
                            discr: Operand::Copy(Place::local(3)),
                            targets: vec![(1, BlockId(3))],
                            otherwise: BlockId(1),
                            exhaustive_enum_unreachable: false,
                            span: SourceSpan::default(),
                        },
                    },
                    // bb3: i += 1; goto bb1  (the conditional write)
                    BasicBlock {
                        id: BlockId(3),
                        stmts: vec![Statement::Assign {
                            place: Place::local(2),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Add,
                                Operand::Copy(Place::local(2)),
                                Operand::Constant(ConstValue::Uint(1, 64)),
                            ),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Goto(BlockId(1)),
                    },
                    BasicBlock { id: BlockId(4), stmts: vec![], terminator: Terminator::Return },
                ],
                arg_count: 1,
                return_ty: Ty::Unit,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    /// Loop whose body writes `i` TWICE: `while i<n { i += 1; i += 2 }`.
    /// `build_body_transition` would model only the first write. Gate rejects (rule c).
    fn double_assign_loop() -> VerifiableFunction {
        let mut func = counting_loop_function();
        func.name = "double_assign".to_string();
        // bb2 is the single body block `i += 1; goto bb1`; append a second write to i.
        let bb2 = &mut func.body.blocks[2];
        bb2.stmts.push(Statement::Assign {
            place: Place::local(2),
            rvalue: Rvalue::BinaryOp(
                BinOp::Add,
                Operand::Copy(Place::local(2)),
                Operand::Constant(ConstValue::Uint(2, 64)),
            ),
            span: SourceSpan::default(),
        });
        func
    }

    #[test]
    fn test_faithfulness_gate_rejects_branching_body() {
        let func = branching_body_loop();
        let loops = detect_loops(&func);
        assert!(!loops.is_empty(), "the loop must be detected");
        let a = Operand::Copy(Place::local(1));
        let b = Operand::Copy(Place::local(2));
        let ob = header_unsigned_sub(&a, &b);
        // Every detected loop over this body is unfaithful => no CHC system.
        for l in &loops {
            assert!(
                try_build_loop_safety_chc_system(&func, l, &ob)
                    .expect("contract-free input should not fail encoding")
                    .is_none(),
                "a branching-body loop must fall back to the single-formula lane"
            );
        }
    }

    #[test]
    fn test_function_chc_rejects_branching_body_before_exit_query() {
        let func = branching_body_loop();
        let error = encode_function_loops(&func)
            .expect_err("the functional exit-query lane needs the same transition gate");
        assert!(matches!(
            error,
            ChcError::UnfaithfulLoopTransition { function, .. }
                if function == "test::branch_loop"
        ));
    }

    #[test]
    fn test_function_chc_rejects_otherwise_body_edge() {
        let mut func = counting_loop_function();
        func.name = "otherwise_body".into();
        func.def_path = "test::otherwise_body".into();
        let Terminator::SwitchInt { targets, otherwise, .. } = &mut func.body.blocks[1].terminator
        else {
            unreachable!("counting fixture has a switch header")
        };
        *targets = vec![(1, BlockId(3))];
        *otherwise = BlockId(2);

        let loops = detect_loops(&func);
        assert!(!loops.is_empty());
        assert!(matches!(
            encode_function_loops(&func),
            Err(ChcError::UnfaithfulLoopTransition { .. })
        ));
    }

    #[test]
    fn test_out_of_shape_safety_loop_ignores_arithmetic_contract_gap() {
        let mut func = branching_body_loop();
        func.preconditions = vec![Formula::Eq(
            Box::new(Formula::Add(
                Box::new(Formula::Var("n".into(), Sort::Int)),
                Box::new(Formula::Int(1)),
            )),
            Box::new(Formula::Int(0)),
        )];
        let loops = detect_loops(&func);
        let a = Operand::Copy(Place::local(1));
        let b = Operand::Copy(Place::local(2));
        let obligation = header_unsigned_sub(&a, &b);
        assert!(
            try_build_loop_safety_chc_system(&func, &loops[0], &obligation)
                .expect("out-of-shape is not a semantic lowering error")
                .is_none(),
            "an arithmetic contract must not make an unfaithful loop appear lane-owned"
        );
    }

    #[test]
    fn test_faithfulness_gate_rejects_double_assign() {
        let func = double_assign_loop();
        let loops = detect_loops(&func);
        assert!(!loops.is_empty(), "the loop must be detected");
        let a = Operand::Copy(Place::local(1));
        let b = Operand::Copy(Place::local(2));
        let ob = header_unsigned_sub(&a, &b);
        for l in &loops {
            assert!(
                try_build_loop_safety_chc_system(&func, l, &ob)
                    .expect("contract-free input should not fail encoding")
                    .is_none(),
                "a variable written twice must fall back to the single-formula lane"
            );
        }
    }

    #[test]
    fn test_faithfulness_gate_rejects_read_after_write() {
        // Reorder the exact sum-loop body to `i += 1; sum += i`. The current
        // simultaneous pre-state transition would otherwise encode the second
        // statement as `sum' = sum + old(i)` and strengthen the real relation.
        let mut func = sum_loop_function();
        func.body.blocks[2].stmts.swap(0, 1);
        let loops = detect_loops(&func);
        let modified = collect_modified_variables(&func, &loops[0]);
        assert!(!loop_transition_is_faithful(&func, &loops[0], &modified));
        assert!(matches!(
            encode_function_loops(&func),
            Err(ChcError::UnfaithfulLoopTransition { .. })
        ));
    }

    #[test]
    fn test_faithfulness_gate_rejects_unmodeled_body_statement() {
        let mut func = counting_loop_function();
        func.body.blocks[2].stmts.insert(
            0,
            Statement::Intrinsic {
                name: "unmodeled_write".into(),
                args: vec![Operand::Copy(Place::local(2))],
            },
        );
        assert!(matches!(
            encode_function_loops(&func),
            Err(ChcError::UnfaithfulLoopTransition { .. })
        ));
    }

    #[test]
    fn test_faithfulness_gate_accepts_counting_loop() {
        // Positive control: the canonical single-path, single-write loop passes the
        // gate (otherwise the gate would be trivially sound by rejecting everything).
        let func = counting_loop_function();
        let loops = detect_loops(&func);
        let modified = collect_modified_variables(&func, &loops[0]);
        assert!(loop_transition_is_faithful(&func, &loops[0], &modified));
    }

    #[test]
    fn test_public_chc_rejects_reordered_mir_layout() {
        let mut func = counting_loop_function();
        func.body.locals.swap(1, 2);
        let loops = detect_loops(&func);
        assert!(!loops.is_empty());
        assert!(matches!(
            encode_function_loops(&func),
            Err(ChcError::UnsupportedMir { kind, .. }) if kind == "MalformedTrustIr"
        ));
    }

    #[test]
    fn test_public_chc_shares_complete_trust_mir_admission() {
        let valid = counting_loop_function();
        let loop_info = detect_loops(&valid).remove(0);
        let n = Operand::Copy(Place::local(1));
        let i = Operand::Copy(Place::local(2));
        let obligation = header_unsigned_sub(&n, &i);

        let mut return_drift = valid.clone();
        return_drift.body.return_ty = Ty::Bool;
        assert!(matches!(
            encode_function_loops(&return_drift),
            Err(ChcError::UnsupportedMir { kind, .. }) if kind == "MalformedTrustIr"
        ));
        assert!(matches!(
            try_build_loop_safety_chc_system(&return_drift, &loop_info, &obligation),
            Err(ChcError::UnsupportedMir { kind, .. }) if kind == "MalformedTrustIr"
        ));

        let mut duplicate_switch = valid.clone();
        let Terminator::SwitchInt { targets, .. } = &mut duplicate_switch.body.blocks[1].terminator
        else {
            unreachable!("counting fixture has a switch header")
        };
        targets.push((1, BlockId(3)));
        assert!(matches!(
            encode_function_loops(&duplicate_switch),
            Err(ChcError::UnsupportedMir { kind, .. }) if kind == "MalformedTrustIr"
        ));

        let mut bad_reference = valid;
        let Statement::Assign { place, .. } = &mut bad_reference.body.blocks[2].stmts[0] else {
            unreachable!("counting fixture body owns one assignment")
        };
        place.local = 99;
        assert!(matches!(
            encode_function_loops(&bad_reference),
            Err(ChcError::UnsupportedMir { kind, .. }) if kind == "MalformedTrustIr"
        ));
    }

    #[test]
    fn test_chc_system_to_smtlib2_horn_shape() {
        let func = counting_loop_function();
        let loops = detect_loops(&func);
        let n = Operand::Copy(Place::local(1));
        let i = Operand::Copy(Place::local(2));

        // SAFE: `n - i` underflows iff n < i; the loop `while i < n` guarantees i < n,
        // so the typed reachability query is unreachable. The raw assertion-only
        // script remains logically consistent and therefore returns SAT.
        let safe_ob = header_unsigned_sub(&n, &i);
        let safe = try_build_loop_safety_chc_system(&func, &loops[0], &safe_ob)
            .expect("contract-free input should not fail encoding")
            .expect("safe");
        let horn = chc_system_to_smtlib2_horn(&safe);
        assert!(horn.starts_with("(set-logic HORN)"));
        assert!(horn.contains("(declare-fun inv_bb1"));
        assert!(horn.trim_end().ends_with("(check-sat)"));
        assert!(!horn.contains('\''), "primed vars must be sanitized: {horn}");
        assert!(horn.contains("false"), "safety query implies false");
        eprintln!("=====SAFE_HORN_BEGIN=====\n{horn}\n=====SAFE_HORN_END=====");

        // UNSAFE: `i - n` underflows iff i < n, which the loop body reaches (i=0,n>0).
        // A typed reachability query reports that counterexample; the raw script's
        // reachable implication-to-false instead makes its assertions UNSAT.
        let unsafe_ob = header_unsigned_sub(&i, &n);
        let bad = try_build_loop_safety_chc_system(&func, &loops[0], &unsafe_ob)
            .expect("contract-free input should not fail encoding")
            .expect("unsafe");
        let horn2 = chc_system_to_smtlib2_horn(&bad);
        eprintln!("=====UNSAFE_HORN_BEGIN=====\n{horn2}\n=====UNSAFE_HORN_END=====");
    }

    // Add to the existing `#[cfg(test)] mod tests { use super::*; ... }` block in
    // crates/trust-vcgen/src/chc.rs (Formula/Sort/ChcPredicate/ChcClause/ChcAtom/
    // ChcSystem/ClauseRole/encode_loop_safety_query are all in `super` scope).

    /// Build the ascending-index loop system `for i in 0..n { a[i] }`:
    ///   entry:      true                        => inv(0, n)
    ///   inductive:  inv(i,n) /\ i<n /\ i'=i+1 /\ n'=n => inv(i', n')
    ///   safety:     inv(i,n) /\ i<n /\ i>=n     => false   (bounds violation Ge(i,n))
    fn ascending_bounds_system() -> ChcSystem {
        let ivar = || Formula::Var("i".to_string(), Sort::Int);
        let nvar = || Formula::Var("n".to_string(), Sort::Int);
        let pred = ChcPredicate {
            name: "inv_bb1".to_string(),
            params: vec![("i".to_string(), Sort::Int), ("n".to_string(), Sort::Int)],
        };
        let entry = ChcClause {
            head: Some(pred.apply(&[Formula::Int(0), nvar()])),
            body_atoms: vec![],
            constraint: Formula::Bool(true),
            label: "entry_bb1".to_string(),
        };
        let cond = Formula::Lt(Box::new(ivar()), Box::new(nvar()));
        let step_i = Formula::Eq(
            Box::new(Formula::Var("i'".to_string(), Sort::Int)),
            Box::new(Formula::Add(Box::new(ivar()), Box::new(Formula::Int(1)))),
        );
        let carry_n =
            Formula::Eq(Box::new(Formula::Var("n'".to_string(), Sort::Int)), Box::new(nvar()));
        let inductive = ChcClause {
            head: Some(pred.apply_primed()),
            body_atoms: vec![pred.apply_unprimed()],
            constraint: Formula::And(vec![cond.clone(), step_i, carry_n]),
            label: "inductive_bb1".to_string(),
        };
        let violation = Formula::Ge(Box::new(ivar()), Box::new(nvar()));
        let (safety, role) = encode_loop_safety_query(&pred, cond, violation, 1);
        ChcSystem {
            predicates: vec![pred],
            clauses: vec![entry, inductive, safety],
            roles: vec![ClauseRole::Entry, ClauseRole::Inductive, role],
            function_name: "f".to_string(),
        }
    }

    #[test]
    fn test_chc_system_to_typed_chc_json_shape() {
        let sys = ascending_bounds_system();
        let json = chc_system_to_typed_chc_json(&sys).expect("representable");

        // query.target is the synthetic error relation.
        assert_eq!(json["query"]["target"], serde_json::json!("error"));
        assert_eq!(json["function_name"], serde_json::json!("f"));

        // relations: one invariant predicate + the nullary error target.
        let relations = json["relations"].as_array().unwrap();
        assert_eq!(relations.len(), 2);
        let rel_names: Vec<&str> = relations.iter().map(|r| r["name"].as_str().unwrap()).collect();
        assert!(rel_names.contains(&"inv_bb1"));
        assert!(rel_names.contains(&"error"));
        let inv = relations.iter().find(|r| r["name"] == serde_json::json!("inv_bb1")).unwrap();
        assert_eq!(inv["arg_sorts"], serde_json::json!([{ "kind": "int" }, { "kind": "int" }]));
        let err = relations.iter().find(|r| r["name"] == serde_json::json!("error")).unwrap();
        assert_eq!(err["arg_sorts"], serde_json::json!([]));

        // vars: unprimed params + primed post-state names.
        let var_names: Vec<&str> =
            json["vars"].as_array().unwrap().iter().map(|v| v["name"].as_str().unwrap()).collect();
        for expected in ["i", "n", "i'", "n'"] {
            assert!(var_names.contains(&expected), "missing var {expected}");
        }
        // every var is Int-sorted here
        for v in json["vars"].as_array().unwrap() {
            assert_eq!(v["sort"], serde_json::json!({ "kind": "int" }));
        }

        // rules: one per clause.
        let rules = json["rules"].as_array().unwrap();
        assert_eq!(rules.len(), 3);

        // entry rule: head=inv(0,n), NO body relation, EMPTY constraints (true dropped)
        // so it is not a rejected "generic Bool-true fact".
        let entry = &rules[0];
        assert_eq!(entry["head"]["name"], serde_json::json!("inv_bb1"));
        assert_eq!(
            entry["head"]["args"][0],
            serde_json::json!({ "kind": "int_const", "value": 0 })
        );
        assert_eq!(entry["head"]["args"][1]["kind"], serde_json::json!("var"));
        assert!(entry["body"].get("relation").is_none());
        assert_eq!(entry["body"]["constraints"], serde_json::json!([]));

        // inductive rule: head=inv(i',n'), body.relation=inv(i,n), 3 flat constraints.
        let ind = &rules[1];
        assert_eq!(ind["head"]["name"], serde_json::json!("inv_bb1"));
        assert_eq!(ind["body"]["relation"]["name"], serde_json::json!("inv_bb1"));
        assert_eq!(ind["body"]["constraints"].as_array().unwrap().len(), 3);

        // safety/query rule: head=error, body.relation=inv(i,n), 2 constraints
        // (loop_cond i<n, violation i>=n).
        let safety = &rules[2];
        assert_eq!(safety["head"]["name"], serde_json::json!("error"));
        assert_eq!(safety["head"].get("args"), None);
        assert_eq!(safety["body"]["relation"]["name"], serde_json::json!("inv_bb1"));
        let cons = safety["body"]["constraints"].as_array().unwrap();
        assert_eq!(cons.len(), 2);
        assert_eq!(cons[0]["op"], serde_json::json!("lt"));
        assert_eq!(cons[1]["op"], serde_json::json!("ge"));
    }

    #[test]
    fn test_multi_atom_body_is_rejected() {
        // A clause with two body predicate atoms is not representable
        // (RuleBody.relation is a single Option) -> hard error, single-formula fallback.
        let pred = ChcPredicate {
            name: "inv_bb1".to_string(),
            params: vec![("i".to_string(), Sort::Int)],
        };
        let bad = ChcClause {
            head: None,
            body_atoms: vec![pred.apply_unprimed(), pred.apply_unprimed()],
            constraint: Formula::Bool(true),
            label: "safety_bb1".to_string(),
        };
        let sys = ChcSystem {
            predicates: vec![pred],
            clauses: vec![bad],
            roles: vec![ClauseRole::Safety],
            function_name: "f".to_string(),
        };
        let err = chc_system_to_typed_chc_json(&sys).unwrap_err();
        assert!(matches!(err, ChcError::EncodingFailed { .. }));
    }

    #[test]
    fn test_no_query_clause_is_rejected() {
        // No head-false clause => no reachability target => not proof-grade.
        let pred = ChcPredicate {
            name: "inv_bb1".to_string(),
            params: vec![("i".to_string(), Sort::Int)],
        };
        let entry = ChcClause {
            head: Some(pred.apply(&[Formula::Int(0)])),
            body_atoms: vec![],
            constraint: Formula::Bool(true),
            label: "entry_bb1".to_string(),
        };
        let sys = ChcSystem {
            predicates: vec![pred],
            clauses: vec![entry],
            roles: vec![ClauseRole::Entry],
            function_name: "f".to_string(),
        };
        assert!(matches!(
            chc_system_to_typed_chc_json(&sys).unwrap_err(),
            ChcError::EncodingFailed { .. }
        ));
    }

    #[test]
    fn test_unsupported_formula_node_is_rejected() {
        // An ITE constraint is outside the typed-CHC fragment -> fail closed.
        let pred = ChcPredicate {
            name: "inv_bb1".to_string(),
            params: vec![("i".to_string(), Sort::Int)],
        };
        let ite = Formula::Ite(
            Box::new(Formula::Bool(true)),
            Box::new(Formula::Var("i".to_string(), Sort::Int)),
            Box::new(Formula::Int(0)),
        );
        let bad = ChcClause {
            head: None,
            body_atoms: vec![pred.apply_unprimed()],
            constraint: ite,
            label: "safety_bb1".to_string(),
        };
        let sys = ChcSystem {
            predicates: vec![pred],
            clauses: vec![bad],
            roles: vec![ClauseRole::Safety],
            function_name: "f".to_string(),
        };
        assert!(matches!(
            chc_system_to_typed_chc_json(&sys).unwrap_err(),
            ChcError::UnsupportedMir { .. }
        ));
    }

    fn formula_contains(formula: &Formula, pred: &impl Fn(&Formula) -> bool) -> bool {
        pred(formula) || formula.children().into_iter().any(|child| formula_contains(child, pred))
    }

    fn assert_named_var_sort(formula: &Formula, name: &str, expected: &Sort) {
        if let Formula::Var(var, sort) = formula {
            if var == name {
                assert_eq!(sort, expected, "{name} should use sort {expected:?}, got {sort:?}");
            }
        }
        for child in formula.children() {
            assert_named_var_sort(child, name, expected);
        }
    }

    /// Build a simple counting loop: while i < n { i += 1; }
    fn counting_loop_function() -> VerifiableFunction {
        VerifiableFunction {
            name: "count_to_n".to_string(),
            def_path: "test::count_to_n".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::Unit, name: None },
                    LocalDecl { index: 1, ty: Ty::u32(), name: Some("n".into()) },
                    LocalDecl { index: 2, ty: Ty::u32(), name: Some("i".into()) },
                    LocalDecl { index: 3, ty: Ty::Bool, name: Some("cond".into()) },
                ],
                blocks: vec![
                    // bb0: i = 0; goto bb1
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![Statement::Assign {
                            place: Place::local(2),
                            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(0, 64))),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Goto(BlockId(1)),
                    },
                    // bb1 (header): cond = i < n; SwitchInt -> [1: bb2, else: bb3]
                    BasicBlock {
                        id: BlockId(1),
                        stmts: vec![Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Lt,
                                Operand::Copy(Place::local(2)),
                                Operand::Copy(Place::local(1)),
                            ),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::SwitchInt {
                            discr: Operand::Copy(Place::local(3)),
                            targets: vec![(1, BlockId(2))],
                            otherwise: BlockId(3),
                            exhaustive_enum_unreachable: false,
                            span: SourceSpan::default(),
                        },
                    },
                    // bb2 (body): i += 1; goto bb1
                    BasicBlock {
                        id: BlockId(2),
                        stmts: vec![Statement::Assign {
                            place: Place::local(2),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Add,
                                Operand::Copy(Place::local(2)),
                                Operand::Constant(ConstValue::Uint(1, 64)),
                            ),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Goto(BlockId(1)),
                    },
                    // bb3 (exit): return
                    BasicBlock { id: BlockId(3), stmts: vec![], terminator: Terminator::Return },
                ],
                arg_count: 1,
                return_ty: Ty::Unit,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    /// A source-level `u8` contract whose mathematical-Int interpretation is
    /// observably wrong: `n + 1 == 0` holds at `n == u8::MAX` under wrapping
    /// evaluation, but never holds over the CHC lane's non-negative integers.
    fn u8_wrapping_contract_loop() -> VerifiableFunction {
        let mut func = counting_loop_function();
        func.name = "u8_wrapping_contract_loop".to_string();
        func.def_path = "test::u8_wrapping_contract_loop".to_string();
        func.body.locals[1].ty = Ty::u8();
        func.body.locals[2].ty = Ty::u8();
        func.preconditions = vec![Formula::Eq(
            Box::new(Formula::Add(
                Box::new(Formula::Var("n".into(), Sort::Int)),
                Box::new(Formula::Int(1)),
            )),
            Box::new(Formula::Int(0)),
        )];
        func
    }

    fn loop_with_body_op(op: BinOp, checked: bool) -> VerifiableFunction {
        let mut func = counting_loop_function();
        let update = Rvalue::BinaryOp(
            op,
            Operand::Copy(Place::local(2)),
            Operand::Constant(ConstValue::Uint(1, 32)),
        );
        let checked_update = Rvalue::CheckedBinaryOp(
            op,
            Operand::Copy(Place::local(2)),
            Operand::Constant(ConstValue::Uint(1, 32)),
        );
        let Statement::Assign { rvalue, .. } = &mut func.body.blocks[2].stmts[0] else {
            unreachable!("counting fixture body owns one assignment")
        };
        *rvalue = if checked { checked_update } else { update };
        func
    }

    /// Build a sum loop: while i < n { sum += i; i += 1; }
    fn sum_loop_function() -> VerifiableFunction {
        VerifiableFunction {
            name: "sum_to_n".to_string(),
            def_path: "test::sum_to_n".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::u32(), name: None },
                    LocalDecl { index: 1, ty: Ty::u32(), name: Some("n".into()) },
                    LocalDecl { index: 2, ty: Ty::u32(), name: Some("i".into()) },
                    LocalDecl { index: 3, ty: Ty::u32(), name: Some("sum".into()) },
                    LocalDecl { index: 4, ty: Ty::Bool, name: Some("cond".into()) },
                ],
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![
                            Statement::Assign {
                                place: Place::local(2),
                                rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(0, 64))),
                                span: SourceSpan::default(),
                            },
                            Statement::Assign {
                                place: Place::local(3),
                                rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(0, 64))),
                                span: SourceSpan::default(),
                            },
                        ],
                        terminator: Terminator::Goto(BlockId(1)),
                    },
                    BasicBlock {
                        id: BlockId(1),
                        stmts: vec![Statement::Assign {
                            place: Place::local(4),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Lt,
                                Operand::Copy(Place::local(2)),
                                Operand::Copy(Place::local(1)),
                            ),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::SwitchInt {
                            discr: Operand::Copy(Place::local(4)),
                            targets: vec![(1, BlockId(2))],
                            otherwise: BlockId(3),
                            exhaustive_enum_unreachable: false,
                            span: SourceSpan::default(),
                        },
                    },
                    BasicBlock {
                        id: BlockId(2),
                        stmts: vec![
                            Statement::Assign {
                                place: Place::local(3),
                                rvalue: Rvalue::BinaryOp(
                                    BinOp::Add,
                                    Operand::Copy(Place::local(3)),
                                    Operand::Copy(Place::local(2)),
                                ),
                                span: SourceSpan::default(),
                            },
                            Statement::Assign {
                                place: Place::local(2),
                                rvalue: Rvalue::BinaryOp(
                                    BinOp::Add,
                                    Operand::Copy(Place::local(2)),
                                    Operand::Constant(ConstValue::Uint(1, 64)),
                                ),
                                span: SourceSpan::default(),
                            },
                        ],
                        terminator: Terminator::Goto(BlockId(1)),
                    },
                    BasicBlock {
                        id: BlockId(3),
                        stmts: vec![Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::Use(Operand::Copy(Place::local(3))),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Return,
                    },
                ],
                arg_count: 1,
                return_ty: Ty::u32(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    fn no_loop_function() -> VerifiableFunction {
        VerifiableFunction {
            name: "identity".to_string(),
            def_path: "test::identity".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::u32(), name: None },
                    LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                }],
                arg_count: 1,
                return_ty: Ty::u32(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    fn loop_with_contracts() -> VerifiableFunction {
        let mut func = counting_loop_function();
        func.preconditions = vec![Formula::Ge(
            Box::new(Formula::Var("n".into(), Sort::Int)),
            Box::new(Formula::Int(0)),
        )];
        func.postconditions = vec![Formula::Eq(
            Box::new(Formula::Var("i".into(), Sort::Int)),
            Box::new(Formula::Var("n".into(), Sort::Int)),
        )];
        func
    }

    fn loop_with_unsupported_update() -> VerifiableFunction {
        let mut func = counting_loop_function();
        let Statement::Assign { rvalue, .. } = &mut func.body.blocks[2].stmts[0] else {
            panic!("counting loop body should start with an assignment");
        };
        *rvalue = Rvalue::Unsupported {
            kind: "Rvalue::ThreadLocalRef".into(),
            detail: "thread-local address semantics are not modeled".into(),
            operands: vec![],
        };
        func
    }

    #[test]
    fn test_encode_no_loops_returns_error() {
        let func = no_loop_function();
        let result = encode_function_loops(&func);
        assert!(result.is_err());
        match result.unwrap_err() {
            ChcError::NoLoops { function } => assert_eq!(function, "identity"),
            other => panic!("expected NoLoops error, got: {other:?}"),
        }
    }

    #[test]
    fn test_encode_no_loops_precedes_arithmetic_contract_gap() {
        let mut func = no_loop_function();
        func.preconditions = vec![Formula::Eq(
            Box::new(Formula::Add(
                Box::new(Formula::Var("x".into(), Sort::Int)),
                Box::new(Formula::Int(1)),
            )),
            Box::new(Formula::Int(0)),
        )];
        let err = encode_function_loops(&func)
            .expect_err("a function without loops is outside the CHC lane");
        assert!(matches!(err, ChcError::NoLoops { .. }));
    }

    #[test]
    fn test_encode_function_loops_rejects_u8_wrapping_contract_arithmetic() {
        let func = u8_wrapping_contract_loop();
        let err = encode_function_loops(&func)
            .expect_err("u8 wrapping contract arithmetic must not enter the integer CHC lane");
        assert!(matches!(
            err,
            ChcError::UnsupportedContractArithmetic {
                function,
                contract_kind: "precondition",
                contract_index: 0,
            } if function == "test::u8_wrapping_contract_loop"
        ));
    }

    #[test]
    fn test_loop_safety_chc_rejects_u8_wrapping_contract_arithmetic() {
        let func = u8_wrapping_contract_loop();
        let loops = detect_loops(&func);
        let n = Operand::Copy(Place::local(1));
        let i = Operand::Copy(Place::local(2));
        let obligation = header_unsigned_sub(&n, &i);
        let err = try_build_loop_safety_chc_system(&func, &loops[0], &obligation)
            .expect_err("the safety CHC adapter must expose the contract lowering gap");
        assert!(matches!(
            err,
            ChcError::UnsupportedContractArithmetic {
                contract_kind: "precondition",
                contract_index: 0,
                ..
            }
        ));
    }

    #[test]
    fn test_arithmetic_free_u8_loop_body_add_is_exact_wrapping_bv() {
        let mut func = counting_loop_function();
        func.body.locals[1].ty = Ty::u8();
        func.body.locals[2].ty = Ty::u8();
        let Statement::Assign { rvalue, .. } = &mut func.body.blocks[2].stmts[0] else {
            unreachable!("counting fixture body owns one assignment")
        };
        *rvalue = Rvalue::BinaryOp(
            BinOp::Add,
            Operand::Copy(Place::local(2)),
            Operand::Constant(ConstValue::Uint(1, 8)),
        );

        let system =
            encode_function_loops(&func).expect("ordinary u8 Add has an exact wrapping transition");
        let transition = &system.inductive_clauses()[0].constraint;
        assert!(
            formula_contains(transition, &|f| matches!(f, Formula::BvAdd(_, _, 8))),
            "u8 body Add must retain its width: {transition:?}"
        );
        assert!(
            formula_contains(transition, &|f| matches!(f, Formula::BvToInt(_, 8, false))),
            "u8 body Add must return through the unsigned interpretation: {transition:?}"
        );
        assert!(
            !formula_contains(transition, &|f| matches!(f, Formula::Add(_, _))),
            "machine Add must never survive as mathematical Int: {transition:?}"
        );
    }

    #[test]
    fn test_signed_i8_body_sub_uses_signed_bv_interpretation() {
        let mut func = counting_loop_function();
        func.body.locals[1].ty = Ty::i8();
        func.body.locals[2].ty = Ty::i8();
        let Statement::Assign { rvalue, .. } = &mut func.body.blocks[2].stmts[0] else {
            unreachable!("counting fixture body owns one assignment")
        };
        *rvalue = Rvalue::BinaryOp(
            BinOp::Sub,
            Operand::Copy(Place::local(2)),
            Operand::Constant(ConstValue::Int(1)),
        );

        let system =
            encode_function_loops(&func).expect("ordinary i8 Sub has an exact wrapping transition");
        let transition = &system.inductive_clauses()[0].constraint;
        assert!(
            formula_contains(transition, &|f| matches!(f, Formula::BvSub(_, _, 8))),
            "i8 body Sub must retain its width: {transition:?}"
        );
        assert!(
            formula_contains(transition, &|f| matches!(f, Formula::BvToInt(_, 8, true))),
            "negative i8 results must be reinterpreted as signed: {transition:?}"
        );
    }

    #[test]
    fn test_u32_body_mul_is_exact_wrapping_bv() {
        let func = loop_with_body_op(BinOp::Mul, false);
        let system = encode_function_loops(&func)
            .expect("ordinary u32 Mul has an exact wrapping transition");
        let transition = &system.inductive_clauses()[0].constraint;
        assert!(
            formula_contains(transition, &|f| matches!(f, Formula::BvMul(_, _, 32))),
            "u32 body Mul must retain its width: {transition:?}"
        );
        assert!(
            !formula_contains(transition, &|f| matches!(f, Formula::Mul(_, _))),
            "machine Mul must never survive as mathematical Int: {transition:?}"
        );
    }

    #[test]
    fn test_unknown_machine_width_is_rejected_not_lowered_as_int() {
        let mut func = counting_loop_function();
        func.body.locals[2].ty = Ty::Int { width: 0, signed: false };
        let err = encode_function_loops(&func)
            .expect_err("an invalid machine width must never select mathematical Int");
        assert!(matches!(
            err,
            ChcError::UnsupportedBodyArithmetic { detail, .. }
                if detail.contains("unsupported or unavailable width")
        ));
    }

    #[test]
    fn test_malformed_machine_operand_types_fail_closed() {
        let mut func = counting_loop_function();
        let Statement::Assign { rvalue, .. } = &mut func.body.blocks[2].stmts[0] else {
            unreachable!("counting fixture body owns one assignment")
        };
        *rvalue = Rvalue::BinaryOp(
            BinOp::Add,
            Operand::Copy(Place::local(3)), // Bool, not the u32 destination type.
            Operand::Constant(ConstValue::Uint(1, 32)),
        );
        let err = encode_function_loops(&func)
            .expect_err("malformed MIR must not manufacture an ill-sorted BV transition");
        assert!(matches!(
            err,
            ChcError::UnsupportedBodyArithmetic { detail, .. }
                if detail.contains("operands do not match")
        ));
    }

    #[test]
    fn test_checked_body_arithmetic_is_rejected_before_chc_lowering() {
        let func = loop_with_body_op(BinOp::Add, true);
        let err = encode_function_loops(&func)
            .expect_err("CheckedBinaryOp tuple/overflow semantics are not modeled");
        assert!(matches!(
            err,
            ChcError::UnsupportedBodyArithmetic {
                block: 2,
                statement: 0,
                operation,
                ..
            } if operation == "CheckedBinaryOp"
        ));
    }

    #[test]
    fn test_div_body_arithmetic_is_rejected_without_panic_guards() {
        let func = loop_with_body_op(BinOp::Div, false);
        let loops = detect_loops(&func);
        let err = encode_function_loops(&func)
            .expect_err("Div without zero/MIN guards must not become total Int division");
        assert!(matches!(
            err,
            ChcError::UnsupportedBodyArithmetic { operation, detail, .. }
                if operation == "Div" && detail.contains("division-by-zero")
        ));

        let lhs = Operand::Copy(Place::local(1));
        let rhs = Operand::Copy(Place::local(2));
        let obligation = header_unsigned_sub(&lhs, &rhs);
        let typed = try_build_loop_safety_chc_system(&func, &loops[0], &obligation)
            .expect_err("the typed API must retain the body-arithmetic diagnostic");
        assert!(matches!(typed, ChcError::UnsupportedBodyArithmetic { .. }));
        #[allow(deprecated)]
        let legacy = build_loop_safety_chc_system(&func, &loops[0], &obligation);
        assert!(
            legacy.is_none(),
            "the compatibility API may lose a discharge, but must never bypass the gate"
        );
    }

    #[test]
    fn test_machine_arithmetic_outside_loop_does_not_disable_chc() {
        let mut func = counting_loop_function();
        func.body.blocks[3].stmts.push(Statement::Assign {
            place: Place::local(2),
            rvalue: Rvalue::BinaryOp(
                BinOp::Div,
                Operand::Copy(Place::local(2)),
                Operand::Constant(ConstValue::Uint(0, 32)),
            ),
            span: SourceSpan::default(),
        });
        encode_function_loops(&func)
            .expect("only operations feeding the loop CHC transition are relevant");
    }

    #[test]
    fn test_encode_counting_loop_produces_system() {
        let func = counting_loop_function();
        let system = encode_function_loops(&func).expect("should encode counting loop");
        assert_eq!(system.predicate_count(), 1);
        assert_eq!(system.clause_count(), 3);
        assert_eq!(system.function_name, "count_to_n");
    }

    #[test]
    fn test_predicate_has_correct_name() {
        let func = counting_loop_function();
        let system = encode_function_loops(&func).expect("should encode");
        assert_eq!(system.predicates[0].name, "inv_bb1");
    }

    #[test]
    fn test_predicate_params_are_modified_vars() {
        let func = counting_loop_function();
        let system = encode_function_loops(&func).expect("should encode");
        let params = &system.predicates[0].params;
        assert!(
            params.iter().any(|(name, _)| name == "i"),
            "i should be a predicate parameter, got: {params:?}"
        );
    }

    /// Distinct shadowed MIR locals may share one source spelling.  Collapsing
    /// them into one Horn parameter would conflate two state cells and can
    /// strengthen the transition enough to prove a false property.  The CHC
    /// lane must share vcgen's collision-safe fallback vocabulary end to end.
    #[test]
    fn test_shadowed_modified_locals_get_distinct_chc_state() {
        let mut func = counting_loop_function();
        func.body.locals.push(LocalDecl { index: 4, ty: Ty::u32(), name: Some("i".into()) });
        func.body.blocks[0].stmts.push(Statement::Assign {
            place: Place::local(4),
            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(0, 32))),
            span: SourceSpan::default(),
        });
        func.body.blocks[2].stmts.push(Statement::Assign {
            place: Place::local(4),
            rvalue: Rvalue::BinaryOp(
                BinOp::Add,
                Operand::Copy(Place::local(4)),
                Operand::Constant(ConstValue::Uint(1, 32)),
            ),
            span: SourceSpan::default(),
        });

        let system = encode_function_loops(&func).expect("shadowing is representable exactly");
        let params = &system.predicates[0].params;
        assert!(params.iter().any(|(name, _)| name == "_2"), "missing first i: {params:?}");
        assert!(params.iter().any(|(name, _)| name == "_4"), "missing shadow i: {params:?}");
        assert!(!params.iter().any(|(name, _)| name == "i"), "ambiguous name survived: {params:?}");
        assert_eq!(params.len(), 2, "the two state cells must remain distinct: {params:?}");
    }

    #[test]
    fn test_clause_roles_are_correct() {
        let func = counting_loop_function();
        let system = encode_function_loops(&func).expect("should encode");
        assert_eq!(system.entry_clauses().len(), 1);
        assert_eq!(system.inductive_clauses().len(), 1);
        assert_eq!(system.exit_clauses().len(), 1);
    }

    #[test]
    fn test_safety_query_is_an_additive_query_clause() {
        // The first code step of the loop-CHC safety integration: a loop-carried
        // safety obligation becomes an ADDITIONAL query on the same invariant
        // predicate. This checks the clause SHAPE (query, one invariant premise,
        // Safety role) and that it does not mutate the base entry/inductive/exit
        // system — it is additive-only, which is what makes it sound by itself.
        let func = counting_loop_function();
        let system = encode_function_loops(&func).expect("should encode");
        let pred = &system.predicates[0];
        let (clause, role) =
            encode_loop_safety_query(pred, Formula::Bool(true), Formula::Bool(true), 1);
        assert!(clause.head.is_none(), "safety query has head = false");
        assert_eq!(clause.body_atoms.len(), 1, "one invariant premise inv(vars)");
        assert!(matches!(role, ClauseRole::Safety));
        assert!(clause.label.starts_with("safety_bb"));
        // Additive: the base system is untouched.
        assert_eq!(system.entry_clauses().len(), 1);
        assert_eq!(system.inductive_clauses().len(), 1);
        assert_eq!(system.exit_clauses().len(), 1);
    }

    #[test]
    fn test_entry_clause_has_no_body_atoms() {
        let func = counting_loop_function();
        let system = encode_function_loops(&func).expect("should encode");
        let entry = &system.entry_clauses()[0];
        assert!(entry.body_atoms.is_empty());
        assert!(entry.head.is_some());
    }

    #[test]
    fn test_inductive_clause_has_body_atom() {
        let func = counting_loop_function();
        let system = encode_function_loops(&func).expect("should encode");
        let inductive = &system.inductive_clauses()[0];
        assert_eq!(inductive.body_atoms.len(), 1);
        assert_eq!(inductive.body_atoms[0].predicate, "inv_bb1");
        assert!(inductive.head.is_some());
    }

    #[test]
    fn test_exit_clause_is_query() {
        let func = counting_loop_function();
        let system = encode_function_loops(&func).expect("should encode");
        let exit = &system.exit_clauses()[0];
        assert!(exit.head.is_none());
        assert_eq!(exit.body_atoms.len(), 1);
    }

    #[test]
    fn test_sum_loop_has_multiple_modified_vars() {
        let func = sum_loop_function();
        let system = encode_function_loops(&func).expect("should encode sum loop");
        let param_names: Vec<&str> =
            system.predicates[0].params.iter().map(|(n, _)| n.as_str()).collect();
        assert!(param_names.contains(&"i"));
        assert!(param_names.contains(&"sum"));
    }

    #[test]
    fn test_predicate_apply_creates_correct_atom() {
        let pred = ChcPredicate {
            name: "inv".to_string(),
            params: vec![("x".into(), Sort::Int), ("y".into(), Sort::Int)],
        };
        let atom = pred.apply(&[Formula::Int(0), Formula::Int(1)]);
        assert_eq!(atom.predicate, "inv");
        assert_eq!(atom.args.len(), 2);
    }

    #[test]
    fn test_predicate_apply_primed() {
        let pred = ChcPredicate {
            name: "inv".to_string(),
            params: vec![("x".into(), Sort::Int), ("y".into(), Sort::Bool)],
        };
        let atom = pred.apply_primed();
        assert_eq!(atom.args.len(), 2);
        assert!(matches!(&atom.args[0], Formula::Var(name, Sort::Int) if name == "x'"));
        assert!(matches!(&atom.args[1], Formula::Var(name, Sort::Bool) if name == "y'"));
    }

    #[test]
    fn test_predicate_apply_unprimed() {
        let pred = ChcPredicate { name: "inv".to_string(), params: vec![("x".into(), Sort::Int)] };
        let atom = pred.apply_unprimed();
        assert!(matches!(&atom.args[0], Formula::Var(name, Sort::Int) if name == "x"));
    }

    #[test]
    fn test_loop_condition_extraction() {
        let func = counting_loop_function();
        let loops = detect_loops(&func);
        let cond = extract_loop_condition(&func, &loops[0]).expect("condition should encode");
        // The header discriminant `cond` is Bool, entered on switch value 1, so the
        // well-typed loop condition is the boolean variable itself (NOT `(= cond 1)`,
        // which would be ill-typed Bool-vs-Int SMT).
        assert!(
            matches!(&cond, Formula::Var(name, sort) if name == "cond" && *sort == Sort::Bool),
            "loop condition should be the boolean `cond`, got: {cond:?}"
        );
    }

    #[test]
    fn test_exit_condition_is_negated() {
        let func = counting_loop_function();
        let loops = detect_loops(&func);
        let exit_cond = extract_exit_condition(&func, &loops[0]).expect("exit should encode");
        assert!(matches!(&exit_cond, Formula::Not(_)));
    }

    #[test]
    fn test_body_transition_captures_increment() {
        let func = counting_loop_function();
        let loops = detect_loops(&func);
        let modified = collect_modified_variables(&func, &loops[0]);
        let transition =
            build_body_transition(&func, &loops[0], &modified).expect("transition should encode");
        match &transition {
            Formula::Eq(lhs, _) => {
                assert!(matches!(lhs.as_ref(), Formula::Var(name, _) if name == "i'"));
            }
            Formula::And(clauses) => {
                let has_i_prime = clauses.iter().any(|c| {
                    matches!(c, Formula::Eq(lhs, _) if matches!(lhs.as_ref(), Formula::Var(name, _) if name == "i'"))
                });
                assert!(has_i_prime);
            }
            other => panic!("expected Eq or And, got: {other:?}"),
        }
    }

    #[test]
    fn test_precondition_from_contracts() {
        let func = loop_with_contracts();
        let system = encode_function_loops(&func).expect("should encode");
        let entry = &system.entry_clauses()[0];
        assert!(matches!(&entry.constraint, Formula::Ge(_, _)));
    }

    #[test]
    fn test_postcondition_in_exit_clause() {
        let func = loop_with_contracts();
        let system = encode_function_loops(&func).expect("should encode");
        let exit = &system.exit_clauses()[0];
        match &exit.constraint {
            Formula::And(clauses) => {
                let has_negated_post = clauses.iter().any(|c| matches!(c, Formula::Not(_)));
                assert!(has_negated_post);
            }
            other => panic!("expected And, got: {other:?}"),
        }
    }

    #[test]
    fn test_function_exit_uses_recomputed_comparison_not_stale_header_temp() {
        let mut func = counting_loop_function();
        func.postconditions = vec![Formula::Eq(
            Box::new(Formula::Var("i".into(), Sort::Int)),
            Box::new(Formula::Var("n".into(), Sort::Int)),
        )];
        let system = encode_function_loops(&func).expect("exact counting loop should encode");
        let exit = system.exit_clauses()[0];

        assert!(
            !formula_contains(&exit.constraint, &|formula| formula.var_name() == Some("cond")),
            "the recomputed header temporary must not survive into the exit state: {:?}",
            exit.constraint
        );
        assert!(
            formula_contains(&exit.constraint, &|formula| matches!(
                formula,
                Formula::Lt(lhs, rhs)
                    if lhs.var_name() == Some("i") && rhs.var_name() == Some("n")
            )),
            "exit must negate the current-state comparison: {:?}",
            exit.constraint
        );
    }

    #[test]
    fn test_clause_labels_contain_block_id() {
        let func = counting_loop_function();
        let system = encode_function_loops(&func).expect("should encode");
        for clause in &system.clauses {
            assert!(clause.label.contains("bb1"), "label: {}", clause.label);
        }
    }

    #[test]
    fn test_chc_error_display() {
        let e = ChcError::NoLoops { function: "foo".into() };
        assert_eq!(e.to_string(), "no loops found in function `foo`");
        let e = ChcError::NoInductionVars { header: 3 };
        assert_eq!(e.to_string(), "loop at block 3 has no induction variables");
        let e = ChcError::EncodingFailed { reason: "bad loop".to_string() };
        assert_eq!(e.to_string(), "failed to encode loop body: bad loop");
        let e = ChcError::UnsupportedMir { kind: "Rvalue::Foo".into(), detail: "bar".into() };
        assert_eq!(e.to_string(), "unsupported MIR in CHC lowering: Rvalue::Foo: bar");
    }

    #[test]
    fn test_collect_modified_variables_sorted() {
        let func = sum_loop_function();
        let loops = detect_loops(&func);
        let modified = collect_modified_variables(&func, &loops[0]);
        for i in 1..modified.len() {
            assert!(modified[i - 1].0 <= modified[i].0, "not sorted: {modified:?}");
        }
    }

    #[test]
    fn test_collect_modified_variables_uses_vcgen_integer_sort() {
        let func = counting_loop_function();
        let loops = detect_loops(&func);
        let modified = collect_modified_variables(&func, &loops[0]);

        assert_eq!(
            modified.iter().find(|(name, _)| name == "i").map(|(_, sort)| sort),
            Some(&Sort::Int),
            "CHC integer loop params must use vcgen integer sort"
        );
    }

    #[test]
    fn test_chc_counting_loop_does_not_mix_integer_sorts() {
        let func = counting_loop_function();
        let system = encode_function_loops(&func).expect("counting loop should encode");
        let predicate = &system.predicates[0];

        assert_eq!(
            predicate.params.iter().find(|(name, _)| name == "i").map(|(_, sort)| sort),
            Some(&Sort::Int),
            "CHC predicate param must match vcgen arithmetic lowering"
        );

        let inductive = system.inductive_clauses()[0];
        for atom in &inductive.body_atoms {
            for arg in &atom.args {
                assert_named_var_sort(arg, "i", &Sort::Int);
                assert_named_var_sort(arg, "i'", &Sort::Int);
            }
        }
        if let Some(head) = &inductive.head {
            for arg in &head.args {
                assert_named_var_sort(arg, "i", &Sort::Int);
                assert_named_var_sort(arg, "i'", &Sort::Int);
            }
        }
        assert_named_var_sort(&inductive.constraint, "i", &Sort::Int);
        assert_named_var_sort(&inductive.constraint, "i'", &Sort::Int);
    }

    #[test]
    fn test_binop_to_formula_arithmetic() {
        let x = Formula::Var("x".into(), Sort::Int);
        let y = Formula::Var("y".into(), Sort::Int);
        assert!(matches!(
            try_binop_to_formula(BinOp::Add, x.clone(), y.clone(), None, false).unwrap(),
            Formula::Add(_, _)
        ));
        assert!(matches!(
            try_binop_to_formula(BinOp::Sub, x.clone(), y.clone(), None, false).unwrap(),
            Formula::Sub(_, _)
        ));
        assert!(matches!(try_binop_to_formula(BinOp::Mul, x, y, None, false).unwrap(), Formula::Mul(_, _)));
    }

    #[test]
    fn test_binop_to_formula_comparison() {
        let x = Formula::Var("x".into(), Sort::Int);
        let y = Formula::Var("y".into(), Sort::Int);
        assert!(matches!(
            try_binop_to_formula(BinOp::Lt, x.clone(), y.clone(), None, false).unwrap(),
            Formula::Lt(_, _)
        ));
        assert!(matches!(
            try_binop_to_formula(BinOp::Eq, x.clone(), y.clone(), None, false).unwrap(),
            Formula::Eq(_, _)
        ));
        assert!(matches!(try_binop_to_formula(BinOp::Ne, x, y, None, false).unwrap(), Formula::Not(_)));
    }

    // Bitwise ops now emit proper bitvector formulas.
    #[test]
    fn test_binop_to_formula_bitwise_emits_bv() {
        let x = Formula::Var("x".into(), Sort::Int);
        let y = Formula::Var("y".into(), Sort::Int);
        let result = try_binop_to_formula(BinOp::BitAnd, x.clone(), y.clone(), Some(32), false).unwrap();
        // Should be BvToInt(BvAnd(IntToBv(x, 32), IntToBv(y, 32), 32), 32, false)
        assert!(matches!(result, Formula::BvToInt(_, 32, false)));

        let result = try_binop_to_formula(BinOp::BitOr, x.clone(), y.clone(), Some(64), false).unwrap();
        assert!(matches!(result, Formula::BvToInt(_, 64, false)));

        let result = try_binop_to_formula(BinOp::BitXor, x.clone(), y.clone(), Some(8), false).unwrap();
        assert!(matches!(result, Formula::BvToInt(_, 8, false)));

        let result = try_binop_to_formula(BinOp::Shl, x.clone(), y.clone(), Some(32), false).unwrap();
        assert!(matches!(result, Formula::BvToInt(_, 32, false)));

        // Unsigned Shr uses BvLShr.
        let result = try_binop_to_formula(BinOp::Shr, x.clone(), y.clone(), Some(32), false).unwrap();
        assert!(matches!(result, Formula::BvToInt(_, 32, false)));

        // Signed Shr uses BvAShr.
        // soundness-signed-shift: a SIGNED op must bridge back to the
        // integer domain with `signed = true` (bv2int_signed), so a negative
        // arithmetic-shift result reads as its true negative value rather than a
        // huge unsigned one that would contradict the signed range constraint and
        // vacuously prove real overflows. See the bridge at the BitAnd|..|Shr arm.
        let result = try_binop_to_formula(BinOp::Shr, x, y, Some(32), true).unwrap();
        assert!(matches!(result, Formula::BvToInt(_, 32, true)));
    }

    #[test]
    fn test_binop_to_formula_bitwise_default_width() {
        let x = Formula::Var("x".into(), Sort::Int);
        let y = Formula::Var("y".into(), Sort::Int);
        // When width is None, should default to 64 bits.
        let result = try_binop_to_formula(BinOp::BitAnd, x, y, None, false).unwrap();
        assert!(matches!(result, Formula::BvToInt(_, 64, false)));
    }

    #[test]
    fn test_rvalue_to_formula_use() {
        let func = counting_loop_function();
        let rvalue = Rvalue::Use(Operand::Constant(ConstValue::Int(42)));
        let formula = rvalue_to_formula(&func, &rvalue).expect("constant should encode");
        assert!(matches!(formula, Formula::Int(42)));
    }

    #[test]
    fn test_rvalue_to_formula_str_constant_uses_injective_symbol() {
        let func = counting_loop_function();
        let bytes = b"panic: bounds check".to_vec();
        let rvalue = Rvalue::Use(Operand::Constant(ConstValue::Str { bytes: bytes.clone() }));

        let formula = rvalue_to_formula(&func, &rvalue).expect("string constant should encode");

        assert!(matches!(
            formula,
            Formula::Var(name, Sort::Int) if name == ConstValue::str_smt_var_name(&bytes)
        ));
    }

    #[test]
    fn test_rvalue_to_formula_binary_op() {
        let mut func = counting_loop_function();
        func.body.locals[2].ty = Ty::u8();
        let rvalue = Rvalue::BinaryOp(
            BinOp::Add,
            Operand::Copy(Place::local(2)),
            Operand::Constant(ConstValue::Uint(2, 8)),
        );
        let formula = rvalue_to_formula(&func, &rvalue).expect("add should encode");
        assert!(matches!(
            formula,
            Formula::BvToInt(inner, 8, false)
                if matches!(inner.as_ref(), Formula::BvAdd(_, _, 8))
        ));
    }

    #[test]
    fn test_rvalue_to_formula_signed_not_retains_signed_interpretation() {
        let mut func = counting_loop_function();
        func.body.locals[2].ty = Ty::i8();
        let rvalue = Rvalue::UnaryOp(UnOp::Not, Operand::Copy(Place::local(2)));
        let formula = rvalue_to_formula(&func, &rvalue).expect("signed bitwise not should encode");
        assert!(matches!(
            formula,
            Formula::BvToInt(inner, 8, true)
                if matches!(inner.as_ref(), Formula::BvNot(_, 8))
        ));
    }

    #[test]
    fn test_rvalue_to_formula_unsupported_operand_fails_closed() {
        let func = counting_loop_function();
        let rvalue = Rvalue::Use(Operand::Unsupported {
            kind: "Operand::Opaque".into(),
            detail: "opaque operand must not become an unconstrained CHC symbol".into(),
        });
        let err = rvalue_to_formula(&func, &rvalue).expect_err("unsupported operand should fail");
        assert!(matches!(
            err,
            ChcError::UnsupportedMir { kind, .. } if kind == "Operand::Opaque"
        ));
    }

    #[test]
    fn test_rvalue_to_formula_unsupported_rvalue_fails_closed() {
        let func = counting_loop_function();
        let rvalue = Rvalue::Unsupported {
            kind: "Rvalue::ShallowInitBox".into(),
            detail: "box allocation semantics are not modeled".into(),
            operands: vec![],
        };
        let err = rvalue_to_formula(&func, &rvalue).expect_err("unsupported rvalue should fail");
        assert!(matches!(
            err,
            ChcError::UnsupportedMir { kind, .. } if kind == "Rvalue::ShallowInitBox"
        ));
    }

    #[test]
    fn test_rvalue_to_formula_multi_element_aggregate_fails_closed() {
        let func = counting_loop_function();
        let rvalue = Rvalue::Aggregate(
            AggregateKind::Tuple,
            vec![Operand::Constant(ConstValue::Int(1)), Operand::Constant(ConstValue::Int(2))],
        );
        let err = rvalue_to_formula(&func, &rvalue).expect_err("aggregate should fail closed");
        assert!(matches!(
            err,
            ChcError::UnsupportedMir { kind, .. } if kind == "Rvalue::Aggregate"
        ));
    }

    #[test]
    fn test_rvalue_to_formula_thin_raw_ptr_aggregate_uses_data_pointer() {
        let mut func = counting_loop_function();
        let ptr_ty = Ty::RawPtr { mutable: false, pointee: Box::new(Ty::i32()) };
        func.body.locals.push(LocalDecl { index: 4, ty: ptr_ty, name: Some("data".into()) });

        let rvalue = Rvalue::Aggregate(
            AggregateKind::RawPtr { pointee_ty: Ty::i32(), mutable: false },
            vec![Operand::Copy(Place::local(4)), Operand::Constant(ConstValue::Unit)],
        );
        let formula = rvalue_to_formula(&func, &rvalue).expect("thin raw ptr should encode");
        assert!(matches!(formula, Formula::Var(name, Sort::Int) if name == "data"));
    }

    #[test]
    fn test_rvalue_to_formula_bool_to_int_cast_uses_ite() {
        let mut func = counting_loop_function();
        func.body.locals.push(LocalDecl { index: 4, ty: Ty::Bool, name: Some("flag".into()) });

        let rvalue = Rvalue::Cast(Operand::Copy(Place::local(4)), Ty::usize());
        let formula = rvalue_to_formula(&func, &rvalue).expect("bool-to-int cast should encode");
        assert!(matches!(
            formula,
            Formula::Ite(cond, then_f, else_f)
                if cond.as_ref().var_name() == Some("flag")
                    && then_f.as_ref() == &Formula::Int(1)
                    && else_f.as_ref() == &Formula::Int(0)
        ));
    }

    #[test]
    fn test_rvalue_to_formula_callable_reification_without_dest_fails_closed() {
        let func = counting_loop_function();
        let fn_ptr_ty =
            Ty::FnPtr { sig: Box::new(FnSig { params: vec![], ret: Box::new(Ty::i32()) }) };

        let rvalue = Rvalue::Cast(Operand::Constant(ConstValue::Unit), fn_ptr_ty);
        let err = rvalue_to_formula(&func, &rvalue)
            .expect_err("callable reification without destination should fail closed");
        assert!(matches!(
            err,
            ChcError::UnsupportedMir { kind, detail }
                if kind == "Rvalue::Cast" && detail.contains("assignment destination")
        ));
    }

    #[test]
    fn test_chc_callable_reification_uses_destination_opaque_token() {
        let fn_ptr_ty =
            Ty::FnPtr { sig: Box::new(FnSig { params: vec![], ret: Box::new(Ty::i32()) }) };
        let func = VerifiableFunction {
            name: "callable_reification_loop".to_string(),
            def_path: "test::callable_reification_loop".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::Unit, name: None },
                    LocalDecl { index: 1, ty: fn_ptr_ty.clone(), name: Some("fp".into()) },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(1),
                        rvalue: Rvalue::Cast(Operand::Constant(ConstValue::Unit), fn_ptr_ty),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                }],
                arg_count: 0,
                return_ty: Ty::Unit,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };
        let Statement::Assign { rvalue, .. } = &func.body.blocks[0].stmts[0] else {
            unreachable!("fixture has one assignment")
        };
        let update =
            rvalue_to_formula_with_dest(&func, rvalue, Some(("fp", Sort::Int, None, false)))
                .expect("callable reification should encode with destination context");
        let transition =
            Formula::Eq(Box::new(Formula::Var("fp'".into(), Sort::Int)), Box::new(update));

        assert!(
            formula_contains(&transition, &|f| f.var_name() == Some("__trust_callable_reify_fp")),
            "CHC callable reification should use the shared opaque token, got {transition:?}"
        );
        assert!(
            !formula_contains(&transition, &|f| {
                matches!(
                    f,
                    Formula::Eq(lhs, rhs)
                        if lhs.as_ref().var_name() == Some("fp'")
                            && matches!(rhs.as_ref(), Formula::Int(0))
                )
            }),
            "CHC callable reification must not collapse to fp' == 0, got {transition:?}"
        );
    }

    #[test]
    fn test_rvalue_to_formula_fn_def_reification_without_dest_fails_closed() {
        let mut func = counting_loop_function();
        let sig = Box::new(FnSig { params: vec![Ty::i32()], ret: Box::new(Ty::i32()) });
        let fn_def_ty = Ty::FnDef { name: "test::helper_i32".into(), sig: sig.clone() };
        let fn_ptr_ty = Ty::FnPtr { sig };
        func.body.locals.push(LocalDecl { index: 4, ty: fn_def_ty, name: Some("helper".into()) });

        let rvalue = Rvalue::Cast(Operand::Copy(Place::local(4)), fn_ptr_ty);
        let err = rvalue_to_formula(&func, &rvalue)
            .expect_err("FnDef reification without destination should fail closed");
        assert!(matches!(
            err,
            ChcError::UnsupportedMir { kind, detail }
                if kind == "Rvalue::Cast" && detail.contains("assignment destination")
        ));
    }

    #[test]
    fn test_chc_fn_def_reification_uses_destination_opaque_token() {
        let sig = Box::new(FnSig { params: vec![Ty::i32()], ret: Box::new(Ty::i32()) });
        let fn_def_ty = Ty::FnDef { name: "test::helper_i32".into(), sig: sig.clone() };
        let fn_ptr_ty = Ty::FnPtr { sig };
        let func = VerifiableFunction {
            name: "fn_def_reification_loop".to_string(),
            def_path: "test::fn_def_reification_loop".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::Unit, name: None },
                    LocalDecl { index: 1, ty: fn_def_ty, name: Some("helper".into()) },
                    LocalDecl { index: 2, ty: fn_ptr_ty.clone(), name: Some("fp".into()) },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::Cast(Operand::Copy(Place::local(1)), fn_ptr_ty),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                }],
                arg_count: 0,
                return_ty: Ty::Unit,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };
        let Statement::Assign { rvalue, .. } = &func.body.blocks[0].stmts[0] else {
            unreachable!("fixture has one assignment")
        };
        let update =
            rvalue_to_formula_with_dest(&func, rvalue, Some(("fp", Sort::Int, None, false)))
                .expect("FnDef reification should encode with destination context");
        let transition =
            Formula::Eq(Box::new(Formula::Var("fp'".into(), Sort::Int)), Box::new(update));

        assert!(
            formula_contains(&transition, &|f| f.var_name() == Some("__trust_callable_reify_fp")),
            "CHC FnDef reification should use the shared opaque token, got {transition:?}"
        );
    }

    #[test]
    fn test_rvalue_to_formula_fn_pointer_mismatched_signature_fails_closed() {
        let mut func = counting_loop_function();
        let src_ty = Ty::FnPtr {
            sig: Box::new(FnSig { params: vec![Ty::i32()], ret: Box::new(Ty::i32()) }),
        };
        let dst_ty = Ty::FnPtr {
            sig: Box::new(FnSig { params: vec![Ty::u64()], ret: Box::new(Ty::u64()) }),
        };
        func.body.locals.push(LocalDecl { index: 4, ty: src_ty, name: Some("src_fp".into()) });

        let rvalue = Rvalue::Cast(Operand::Copy(Place::local(4)), dst_ty);
        let err = rvalue_to_formula(&func, &rvalue)
            .expect_err("mismatched function pointer signatures should fail closed");
        assert!(matches!(
            err,
            ChcError::UnsupportedMir { kind, detail }
                if kind == "Rvalue::Cast" && detail.contains("signature")
        ));
    }

    #[test]
    fn test_rvalue_to_formula_thin_pointer_cast_is_identity() {
        let mut func = counting_loop_function();
        let src_ty = Ty::RawPtr { mutable: false, pointee: Box::new(Ty::u8()) };
        let dst_ty = Ty::RawPtr { mutable: false, pointee: Box::new(Ty::u32()) };
        func.body.locals.push(LocalDecl { index: 4, ty: src_ty, name: Some("data".into()) });

        let rvalue = Rvalue::Cast(Operand::Copy(Place::local(4)), dst_ty);
        let formula = rvalue_to_formula(&func, &rvalue).expect("thin pointer cast should encode");
        assert!(matches!(formula, Formula::Var(name, Sort::Int) if name == "data"));
    }

    #[test]
    fn test_rvalue_to_formula_fat_pointer_cast_fails_closed() {
        let mut func = counting_loop_function();
        let src_ty = Ty::RawPtr { mutable: false, pointee: Box::new(Ty::u8()) };
        let dst_ty = Ty::RawPtr {
            mutable: false,
            pointee: Box::new(Ty::Slice { elem: Box::new(Ty::u8()) }),
        };
        func.body.locals.push(LocalDecl { index: 4, ty: src_ty, name: Some("data".into()) });

        let rvalue = Rvalue::Cast(Operand::Copy(Place::local(4)), dst_ty);
        let err = rvalue_to_formula(&func, &rvalue).expect_err("fat pointer cast should fail");
        assert!(matches!(
            err,
            ChcError::UnsupportedMir { kind, detail }
                if kind == "Rvalue::Cast"
                    && detail.contains("fat-pointer metadata/provenance")
        ));
    }

    #[test]
    fn test_rvalue_to_formula_fat_raw_ptr_aggregate_fails_closed() {
        let mut func = counting_loop_function();
        let data_ptr_ty = Ty::RawPtr { mutable: false, pointee: Box::new(Ty::u8()) };
        func.body.locals.push(LocalDecl { index: 4, ty: data_ptr_ty, name: Some("data".into()) });

        let rvalue = Rvalue::Aggregate(
            AggregateKind::RawPtr {
                pointee_ty: Ty::Slice { elem: Box::new(Ty::u8()) },
                mutable: false,
            },
            vec![Operand::Copy(Place::local(4)), Operand::Constant(ConstValue::Uint(4, 64))],
        );
        let err = rvalue_to_formula(&func, &rvalue).expect_err("fat raw ptr should fail closed");
        assert!(matches!(
            err,
            ChcError::UnsupportedMir { kind, detail }
                if kind == "AggregateKind::RawPtr" && detail.contains("fat-pointer metadata")
        ));
    }

    #[test]
    fn test_encode_loop_with_unsupported_update_fails_closed() {
        let func = loop_with_unsupported_update();
        let err = encode_function_loops(&func).expect_err("unsupported loop update should fail");
        assert!(matches!(
            err,
            ChcError::UnsupportedMir { kind, .. } if kind == "Rvalue::ThreadLocalRef"
        ));
    }

    // ── BV128 Int↔BV bridge encoding (Task #57) ──────────────────────────────
    // A faithful width-128 wrapping body-def is `BvToInt(BvAdd(IntToBv(a,128),
    // IntToBv(b,128), 128), 128, signed)`. Before this fix the `IntToBv`/`BvToInt`
    // bridges had no typed-CHC payload, so the whole postcondition CHC fell back
    // to the single-formula lane (Lcg::range_i128 / range_usize UNKNOWN). These
    // tests pin the emitted payload to the exact `TrustMcTypedChcUnaryOpInput`
    // contract the consumer (`trust-bmc verifier_api.rs`) parses: `int_to_bv`
    // carries ONLY `width`; `bv_to_int` carries ONLY `signed`.
    #[test]
    fn test_typed_chc_int_to_bv_encodes_width_only() {
        let mut vars = std::collections::BTreeMap::new();
        let f = Formula::IntToBv(Box::new(Formula::Var("x".into(), Sort::Int)), 128);
        let json = chc_formula_to_typed_expr(&f, &mut vars).expect("int_to_bv must encode");
        assert_eq!(json["kind"], "unary");
        assert_eq!(json["op"], "int_to_bv");
        assert_eq!(json["width"], 128);
        // The consumer rejects int_to_bv carrying a `signed` param.
        assert!(json.get("signed").is_none(), "int_to_bv must not carry `signed`: {json}");
        assert_eq!(json["expr"]["kind"], "var");
    }

    #[test]
    fn test_typed_chc_bv_to_int_encodes_signed_only() {
        let mut vars = std::collections::BTreeMap::new();
        let inner = Formula::IntToBv(Box::new(Formula::Var("x".into(), Sort::Int)), 128);
        let f = Formula::BvToInt(Box::new(inner), 128, true);
        let json = chc_formula_to_typed_expr(&f, &mut vars).expect("bv_to_int must encode");
        assert_eq!(json["kind"], "unary");
        assert_eq!(json["op"], "bv_to_int");
        assert_eq!(json["signed"], true);
        // The consumer rejects bv_to_int carrying a `width` param (it recovers the
        // width from the inner BV's sort).
        assert!(json.get("width").is_none(), "bv_to_int must not carry `width`: {json}");
    }

    #[test]
    fn test_typed_chc_width_128_wrapping_add_bridge_encodes() {
        // The full faithful two's-complement wrapping-add body-def at width 128.
        let mut vars = std::collections::BTreeMap::new();
        let a = Formula::IntToBv(Box::new(Formula::Var("a".into(), Sort::Int)), 128);
        let b = Formula::IntToBv(Box::new(Formula::Var("b".into(), Sort::Int)), 128);
        let wrap = Formula::BvToInt(Box::new(Formula::BvAdd(Box::new(a), Box::new(b), 128)), 128, true);
        let json = chc_formula_to_typed_expr(&wrap, &mut vars)
            .expect("width-128 wrapping-add bridge must encode end-to-end");
        assert_eq!(json["op"], "bv_to_int");
        assert_eq!(json["expr"]["op"], "bv_add");
        assert_eq!(json["expr"]["lhs"]["op"], "int_to_bv");
        assert_eq!(json["expr"]["lhs"]["width"], 128);
    }

    #[test]
    fn test_typed_chc_bitvec_128_high_bit_constant_encodes_faithfully() {
        // A high-bit u128 pattern (u128::MAX) is stored as `-1i128` (two's-complement
        // reinterpret) and encoded as a `bit_vec_const`; the consumer parses i128
        // then reinterprets u128 and masks to `width`, so the pattern round-trips.
        let mut vars = std::collections::BTreeMap::new();
        let f = Formula::BitVec { value: u128::MAX as i128, width: 128 };
        let json = chc_formula_to_typed_expr(&f, &mut vars).expect("bit_vec_const must encode");
        assert_eq!(json["kind"], "bit_vec_const");
        assert_eq!(json["width"], 128);
        // -1i128 renders as a bare number the consumer's i128 parse accepts (then
        // masks to all-ones-128 = u128::MAX). No high-bit value is try_from-rejected.
        assert_eq!(json["value"], -1);
    }
}
