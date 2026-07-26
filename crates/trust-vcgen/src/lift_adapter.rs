//, #565: Adapter bridging trust-lift output to trust_vcgen for binary verification.
//
// Converts LiftedFunction (binary -> CFG -> SSA -> TrustIr) into VerificationConditions
// by wrapping the TrustIr body as a VerifiableFunction and running the standard VC
// generation pipeline, plus binary-specific safety VCs (memory model, stack discipline).
//
// Also provides lifted_to_legacy() to convert LiftedFunction into the
// legacy LiftedProgram format, enabling the security analysis pipeline (buffer
// overflow, UAF, format string, etc.) to consume output from the canonical
// disassembler chain.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::{BTreeMap, BTreeSet};

use trust_lift::cfg::{CfgEdgeKind, CfgEdgeTarget};
use trust_lift::{LiftedFunction, LocalLayout};
use trust_types::{
    Aarch64AtomicSemanticFact, Aarch64ExclusiveMonitorSemantics, BinaryAbiFact, BinaryAbiFactKind,
    BinaryFactConfidence, BinaryFactEvidence, BinaryFactSubject, BinaryOrigin, BinaryStorageFact,
    BinaryStorageLocation, ConstValue, Formula, MemoryAccessFact, MemoryAccessKind,
    MemoryOrderingSemantics, MemoryRegionKind, Operand, Projection, Rvalue, Sort, SourceSpan,
    Statement, Terminator, TrustLevel, Ty, UnsupportedRecord, VcKind, VerifiableFunction,
    VerificationCondition, stable_sha256_hex,
};

use crate::binary_analysis::lifter::{
    AbstractInsn, AbstractOp, AbstractRegister, AbstractValue, LiftedProgram, MemoryAccess,
};
use crate::data_race::{AccessKind, MemoryOrdering};
use crate::ffi_summary::printf_family_format_index;
use crate::ffi_vcgen::unsafe_format_argument_evidence;
use crate::memory_ordering::{
    Aarch64ExclusiveMonitorWitness, Aarch64ProofObligationConsumption,
    Aarch64ReleaseAcquireWitness, AtomicAccessEntry, AtomicAccessLog, HappensBefore,
    MemoryModelChecker,
};

fn generated_lift_symbol(unqualified: &str) -> String {
    crate::generated_formula_symbol("lift", unqualified)
}

/// Convert a `LiftedFunction` into a `VerifiableFunction` suitable for VC generation.
///
/// The lifted function already carries a `trust_ir_body` (`VerifiableBody`) produced by
/// the semantic lifter. We wrap it with the metadata needed by the VC generator.
#[must_use]
pub fn lift_to_verifiable(lifted: &LiftedFunction) -> VerifiableFunction {
    VerifiableFunction {
        name: lifted.name.clone(),
        def_path: format!("binary::{}", lifted.name),
        span: SourceSpan {
            file: format!("binary:0x{:x}", lifted.entry_point),
            line_start: 0,
            col_start: 0,
            line_end: 0,
            col_end: 0,
        },
        body: lifted.trust_ir_body.clone(),
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

// ────────────────────────────────────────────────────────────────────────────
// LiftedFunction -> LiftedProgram adapter
// ────────────────────────────────────────────────────────────────────────────

/// Convert a `trust_lift::LiftedFunction` into the legacy `LiftedProgram` format.
///
/// This adapter enables the legacy security analysis pipeline (buffer overflow,
/// UAF, format string, control-flow hijack detection) to consume output from
/// the canonical disassembler chain (trust-binary-parse -> trust-disasm ->
/// trust-machine-sem -> trust-lift).
///
/// The conversion walks the TrustIr body and synthesizes `AbstractInsn` values
/// with synthetic addresses derived from block ID and statement index.
#[must_use]
pub fn lifted_to_legacy(lifted: &LiftedFunction) -> LiftedProgram {
    let mut instructions = Vec::new();

    for block in &lifted.trust_ir_body.blocks {
        let block_base = synthetic_block_address(lifted.entry_point, block.id.0);

        // Convert statements
        for (stmt_idx, stmt) in block.stmts.iter().enumerate() {
            let addr = block_base.saturating_add((stmt_idx as u64) * 4);
            if let Some(insn) = stmt_to_abstract_insn(stmt, addr) {
                instructions.push(insn);
            }
        }

        // Convert terminator
        let term_addr = block_base.saturating_add((block.stmts.len() as u64) * 4);
        if let Some(insn) =
            terminator_to_abstract_insn(&block.terminator, term_addr, lifted.entry_point)
        {
            instructions.push(insn);
        }
    }

    // Build registers from locals
    let registers: Vec<AbstractRegister> = lifted
        .trust_ir_body
        .locals
        .iter()
        .map(|local| {
            let width = ty_to_width(&local.ty);
            AbstractRegister {
                id: local.index as u16,
                name: local.name.clone().unwrap_or_else(|| format!("_{}", local.index)),
                width,
            }
        })
        .collect();

    // Ensure instructions are sorted by address and the entry point is present
    instructions.sort_by_key(|insn| insn.address);

    LiftedProgram { instructions, entry_point: lifted.entry_point, registers }
}

/// Convert a TrustIr statement to an abstract instruction.
fn stmt_to_abstract_insn(stmt: &Statement, addr: u64) -> Option<AbstractInsn> {
    match stmt {
        Statement::Assign { place, rvalue, .. } => {
            let dst = place.local as u16;

            // Check for memory store (place has Deref projection)
            if place.projections.iter().any(|p| matches!(p, Projection::Deref)) {
                let value = rvalue_to_formula(rvalue);
                let store_addr = Formula::Var(
                    generated_lift_symbol(&format!("store_addr_local{}", place.local)),
                    Sort::BitVec(64),
                );
                return Some(AbstractInsn {
                    address: addr,
                    op: AbstractOp::Store {
                        access: MemoryAccess::Write { addr: store_addr, size: 8, value },
                    },
                    size: 4,
                });
            }

            let op = match rvalue {
                Rvalue::BinaryOp(bin_op, lhs, rhs) => AbstractOp::BinArith {
                    dst,
                    op: *bin_op,
                    lhs: operand_to_abstract_value(lhs),
                    rhs: operand_to_abstract_value(rhs),
                },
                Rvalue::CheckedBinaryOp(bin_op, lhs, rhs) => AbstractOp::BinArith {
                    dst,
                    op: *bin_op,
                    lhs: operand_to_abstract_value(lhs),
                    rhs: operand_to_abstract_value(rhs),
                },
                Rvalue::UnaryOp(un_op, operand) => AbstractOp::UnaryOp {
                    dst,
                    op: *un_op,
                    operand: operand_to_abstract_value(operand),
                },
                Rvalue::Use(operand) => {
                    // Check if operand is a deref (memory load)
                    if let Operand::Copy(src_place) | Operand::Move(src_place) = operand
                        && src_place.projections.iter().any(|p| matches!(p, Projection::Deref))
                    {
                        let load_addr = Formula::Var(
                            generated_lift_symbol(&format!("load_addr_local{}", src_place.local)),
                            Sort::BitVec(64),
                        );
                        return Some(AbstractInsn {
                            address: addr,
                            op: AbstractOp::Load {
                                dst,
                                access: MemoryAccess::Read { addr: load_addr, size: 8 },
                            },
                            size: 4,
                        });
                    }
                    AbstractOp::Assign { dst, src: operand_to_abstract_value(operand) }
                }
                Rvalue::Cast(operand, _) => {
                    AbstractOp::Assign { dst, src: operand_to_abstract_value(operand) }
                }
                _ => AbstractOp::Nop,
            };

            Some(AbstractInsn { address: addr, op, size: 4 })
        }
        _ => None,
    }
}

/// Convert a TrustIr terminator to an abstract instruction.
fn terminator_to_abstract_insn(
    term: &Terminator,
    addr: u64,
    entry_point: u64,
) -> Option<AbstractInsn> {
    let op = match term {
        Terminator::Return => AbstractOp::Return { value: None },
        Terminator::Goto(target) => {
            AbstractOp::Branch { target: synthetic_block_address(entry_point, target.0) }
        }
        Terminator::Call { func: callee, args, target, .. } => AbstractOp::Call {
            func: callee.clone(),
            args: args.iter().map(operand_to_abstract_value).collect(),
            dest: None,
            next: target.map(|t| synthetic_block_address(entry_point, t.0)),
        },
        Terminator::SwitchInt { discr, targets, otherwise, .. } => {
            if let Some((_, true_target)) = targets.first() {
                AbstractOp::CondBranch {
                    cond: operand_to_abstract_value(discr),
                    true_target: synthetic_block_address(entry_point, true_target.0),
                    false_target: synthetic_block_address(entry_point, otherwise.0),
                }
            } else {
                AbstractOp::Branch { target: synthetic_block_address(entry_point, otherwise.0) }
            }
        }
        Terminator::Drop { target, .. } => {
            AbstractOp::Branch { target: synthetic_block_address(entry_point, target.0) }
        }
        Terminator::Opaque { .. } => {
            // The legacy adapter has no unsupported-obligation channel, so keep
            // opaque control flow unresolved instead of pretending it is precise.
            AbstractOp::IndirectBranch {
                target: AbstractValue::Formula(Formula::var_owned(
                    generated_lift_symbol("opaque_control_flow_target"),
                    Sort::BitVec(64),
                )),
            }
        }
        _ => return None,
    };

    Some(AbstractInsn { address: addr, op, size: 4 })
}

/// Convert an operand to an AbstractValue.
fn operand_to_abstract_value(op: &Operand) -> AbstractValue {
    match op {
        Operand::Copy(place) | Operand::Move(place) => AbstractValue::Register(place.local as u16),
        Operand::Symbolic(formula) => AbstractValue::Formula(formula.clone()),
        Operand::Constant(cv) => {
            let formula = match cv {
                ConstValue::Bool(b) => Formula::Bool(*b),
                ConstValue::Int(n) => Formula::Int(*n),
                ConstValue::Uint(n, _) => match i128::try_from(*n) {
                    Ok(n) => Formula::Int(n),
                    Err(_) => Formula::UInt(*n),
                },
                ConstValue::Float(f) => {
                    Formula::Var(generated_lift_symbol(&format!("float_{f}")), Sort::BitVec(64))
                }
                ConstValue::Unit => Formula::Int(0),
                ConstValue::CallableItem { def_path, kind, def_path_hash } => Formula::var_owned(
                    ConstValue::callable_smt_var_name(def_path, *kind, *def_path_hash),
                    Sort::Int,
                ),
                // opaque, injectively-named term for a `&str` literal.
                // A shared name would alias distinct strings into one abstract
                // value and let a lifted-binary VC "prove" a false disequality.
                ConstValue::Str { bytes } => {
                    Formula::Var(ConstValue::str_smt_var_name(bytes), Sort::Int)
                }
                _ => Formula::Var(generated_lift_symbol("unknown_constant"), Sort::Int),
            };
            AbstractValue::Formula(formula)
        }
        _ => AbstractValue::Formula(Formula::Var(
            generated_lift_symbol("unknown_operand"),
            Sort::Int,
        )),
    }
}

/// Extract a formula from an rvalue (for memory store values).
fn rvalue_to_formula(rvalue: &Rvalue) -> Formula {
    match rvalue {
        Rvalue::Use(op) => match op {
            Operand::Constant(ConstValue::Int(n)) => Formula::Int(*n),
            Operand::Constant(ConstValue::Uint(n, _)) => match i128::try_from(*n) {
                Ok(n) => Formula::Int(n),
                Err(_) => Formula::UInt(*n),
            },
            Operand::Constant(ConstValue::Bool(b)) => Formula::Bool(*b),
            Operand::Symbolic(formula) => formula.clone(),
            Operand::Copy(p) | Operand::Move(p) => Formula::Var(format!("_{}", p.local), Sort::Int),
            _ => Formula::Var(generated_lift_symbol("unknown_store_value"), Sort::Int),
        },
        _ => Formula::Var(generated_lift_symbol("unknown_store_value"), Sort::Int),
    }
}

/// Compute synthetic address for a block.
fn synthetic_block_address(entry_point: u64, block_id: usize) -> u64 {
    entry_point.saturating_add((block_id as u64) * 0x100)
}

/// Convert a Ty to a register width in bits.
fn ty_to_width(ty: &Ty) -> u32 {
    match ty {
        Ty::Bool => 1,
        Ty::Int { width, .. } => *width,
        Ty::Float { width } => *width,
        _ => 64, // default width for unknown types
    }
}

// ────────────────────────────────────────────────────────────────────────────
// VC generation
// ────────────────────────────────────────────────────────────────────────────

/// Synthetic allocator lifetime event used by focused binary allocator VC tests.
///
/// This intentionally stays local to the lift adapter until binary allocator
/// events are promoted into the shared decompilation model. The helper below is
/// pure and fail-closed: incomplete lifetime evidence becomes a typed bad-state
/// VC instead of being silently ignored.
#[derive(Debug, Clone)]
pub struct AllocatorLifetimeFact {
    pub kind: AllocatorLifetimeFactKind,
    pub allocation_id: Option<String>,
    pub pointer: Option<Formula>,
    pub location: SourceSpan,
    pub evidence: String,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AllocatorLifetimeFactKind {
    Allocate,
    Free,
}

#[derive(Debug, Clone)]
pub struct AllocatorLifetimeAccessFact {
    pub kind: AllocatorLifetimeAccessKind,
    pub allocation_id: Option<String>,
    pub pointer: Option<Formula>,
    pub location: SourceSpan,
    pub evidence: String,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AllocatorLifetimeAccessKind {
    Read,
    Write,
}

/// Synthetic copy-sink fact used by binary security VC generation.
///
/// Binary lifters commonly recover calls such as `memcpy(dst, src, n)` before
/// they recover a proof-grade destination extent. This fact keeps the copy-sink
/// length family explicit: known `length > capacity` becomes a solver-facing
/// bad-state formula, while missing evidence stays fail-closed.
#[derive(Debug, Clone)]
pub struct BinaryCopySinkLengthFact {
    pub callee: String,
    pub dest: Option<Formula>,
    pub copy_length: Option<Formula>,
    pub dest_capacity: Option<Formula>,
    pub location: SourceSpan,
    pub evidence: String,
}

/// Stable binary-security VC families surfaced by vcgen.
///
/// These IDs intentionally mirror report JSON keys where a typed `VcKind`
/// already exists. Keeping the classifier in vcgen lets binary-mode generation
/// tests assert family identity before router/report aggregation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[non_exhaustive]
pub enum BinarySecurityVcFamily {
    UseAfterFree,
    DoubleFree,
    SavedReturnAddressOverwrite,
    FormatStringViolation,
    TaintedIndirectBranch,
    BinaryAbiContradiction,
    BinaryCopySinkLengthViolation,
}

impl BinarySecurityVcFamily {
    #[must_use]
    pub fn stable_id(self) -> &'static str {
        match self {
            Self::UseAfterFree => "use_after_free",
            Self::DoubleFree => "double_free",
            Self::SavedReturnAddressOverwrite => "saved_return_address_overwrite",
            Self::FormatStringViolation => "format_string_violation",
            Self::TaintedIndirectBranch => "tainted_indirect_branch",
            Self::BinaryAbiContradiction => "binary_abi_contradiction",
            Self::BinaryCopySinkLengthViolation => VcKind::BINARY_COPY_SINK_LENGTH_FAMILY,
        }
    }
}

/// Structured evidence explaining why a binary-security VC blocks proof-grade
/// acceptance until the named fact is proved, replayed, or discharged.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BinarySecurityBlockingEvidence {
    pub code: String,
    pub detail: String,
}

impl BinarySecurityBlockingEvidence {
    fn new(code: impl Into<String>, detail: impl Into<String>) -> Self {
        Self { code: code.into(), detail: detail.into() }
    }
}

/// Vcgen-local security-family classification for a generated VC.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BinarySecurityVcClassification {
    pub family: BinarySecurityVcFamily,
    pub family_id: &'static str,
    pub proof_grade_blockers: Vec<BinarySecurityBlockingEvidence>,
}

const BINARY_ALLOCATOR_BLOCKER_PREFIX: &str = "__trust_lift__allocator_blocker__";
const BLOCKER_ALLOCATION_ALREADY_FREED: &str = "allocation_already_freed";
const BLOCKER_ACCESS_AFTER_FREE: &str = "access_after_free";
const BLOCKER_MISSING_ALLOCATION_IDENTITY: &str = "missing_allocation_identity";
const BLOCKER_MISSING_POINTER_FORMULA: &str = "missing_pointer_formula";
const BLOCKER_UNRESOLVED_FREED_ALLOCATION_ALIAS: &str = "unresolved_freed_allocation_alias";
const BLOCKER_UNKNOWN_ALLOCATOR_LIFETIME: &str = "unknown_allocator_lifetime";
const BLOCKER_UNKNOWN_STACK_RETURN_SLOT: &str = "unknown_stack_return_slot";
const BLOCKER_SAVED_RETURN_ADDRESS_ALIAS: &str = "saved_return_address_alias";
const BLOCKER_MISSING_INDIRECT_TARGET_TAINT: &str = "missing_indirect_target_taint";
const BLOCKER_UNRESOLVED_INDIRECT_CONTROL_TARGET: &str = "unresolved_indirect_control_target";

/// Classify a VC into a stable binary-security family, if it is one.
#[must_use]
pub fn classify_binary_security_vc(
    vc: &VerificationCondition,
) -> Option<BinarySecurityVcClassification> {
    let family = match &vc.kind {
        VcKind::UseAfterFree => BinarySecurityVcFamily::UseAfterFree,
        VcKind::DoubleFree => BinarySecurityVcFamily::DoubleFree,
        VcKind::SavedReturnAddressOverwrite { .. } => {
            BinarySecurityVcFamily::SavedReturnAddressOverwrite
        }
        VcKind::FormatStringViolation { .. } => BinarySecurityVcFamily::FormatStringViolation,
        VcKind::TaintedIndirectBranch { .. } => BinarySecurityVcFamily::TaintedIndirectBranch,
        VcKind::BinaryAbiContradiction { .. } => BinarySecurityVcFamily::BinaryAbiContradiction,
        kind if kind.is_binary_copy_sink_length_violation() => {
            BinarySecurityVcFamily::BinaryCopySinkLengthViolation
        }
        _ => return None,
    };

    Some(BinarySecurityVcClassification {
        family,
        family_id: family.stable_id(),
        proof_grade_blockers: binary_security_blockers(vc),
    })
}

/// Count generated binary-security VC families at the vcgen boundary.
#[must_use]
pub fn binary_security_family_counts(vcs: &[VerificationCondition]) -> BTreeMap<String, usize> {
    let mut counts = BTreeMap::new();
    for vc in vcs {
        if let Some(classification) = classify_binary_security_vc(vc) {
            *counts.entry(classification.family_id.to_string()).or_insert(0) += 1;
        }
    }
    counts
}

fn binary_security_blockers(vc: &VerificationCondition) -> Vec<BinarySecurityBlockingEvidence> {
    let mut blockers = Vec::new();
    collect_allocator_blockers(&vc.formula, &mut blockers);
    if !blockers.is_empty() {
        return blockers;
    }

    match &vc.kind {
        VcKind::SavedReturnAddressOverwrite { access_width_bytes, slot } => {
            saved_return_address_blockers(slot, *access_width_bytes)
        }
        VcKind::FormatStringViolation { evidence, .. } => {
            vec![BinarySecurityBlockingEvidence::new("tainted_format_argument", evidence.clone())]
        }
        VcKind::TaintedIndirectBranch { sink_kind, target, evidence } => {
            tainted_indirect_branch_blockers(sink_kind, target, evidence)
        }
        VcKind::BinaryAbiContradiction { evidence, .. } => {
            vec![BinarySecurityBlockingEvidence::new(
                "contradictory_proof_grade_binary_facts",
                evidence.clone(),
            )]
        }
        VcKind::BinaryCopySinkLengthViolation { desc, .. }
        | VcKind::FfiBoundaryViolation { desc, .. }
            if vc.kind.is_binary_copy_sink_length_violation() =>
        {
            copy_sink_blockers(desc)
        }
        VcKind::UseAfterFree | VcKind::DoubleFree => {
            vec![BinarySecurityBlockingEvidence::new(
                BLOCKER_UNKNOWN_ALLOCATOR_LIFETIME,
                "allocator lifetime VC lacks structured blocker atoms",
            )]
        }
        _ => Vec::new(),
    }
}

fn saved_return_address_blockers(
    slot: &str,
    access_width_bytes: u32,
) -> Vec<BinarySecurityBlockingEvidence> {
    let code = if slot.contains("unknown") {
        BLOCKER_UNKNOWN_STACK_RETURN_SLOT
    } else {
        BLOCKER_SAVED_RETURN_ADDRESS_ALIAS
    };

    vec![BinarySecurityBlockingEvidence::new(
        code,
        format!("slot={slot}; access_width_bytes={access_width_bytes}"),
    )]
}

fn tainted_indirect_branch_blockers(
    sink_kind: &str,
    target: &str,
    evidence: &str,
) -> Vec<BinarySecurityBlockingEvidence> {
    let detail = format!("{sink_kind} target={target}; evidence={evidence}");
    let mut blockers = vec![BinarySecurityBlockingEvidence::new(
        BLOCKER_MISSING_INDIRECT_TARGET_TAINT,
        detail.clone(),
    )];

    if target.contains("unresolved") || evidence.contains("unresolved") {
        blockers.push(BinarySecurityBlockingEvidence::new(
            BLOCKER_UNRESOLVED_INDIRECT_CONTROL_TARGET,
            detail,
        ));
    }

    blockers
}

fn copy_sink_blockers(desc: &str) -> Vec<BinarySecurityBlockingEvidence> {
    let mut blockers = Vec::new();
    if desc.contains("destination pointer") {
        blockers.push(BinarySecurityBlockingEvidence::new("missing_destination_pointer", desc));
    }
    if desc.contains("copy length") {
        blockers.push(BinarySecurityBlockingEvidence::new("missing_copy_length", desc));
    }
    if desc.contains("destination capacity") {
        blockers.push(BinarySecurityBlockingEvidence::new("missing_destination_capacity", desc));
    }
    if blockers.is_empty() {
        blockers.push(BinarySecurityBlockingEvidence::new(
            "copy_length_exceeds_destination_capacity",
            desc,
        ));
    }
    blockers
}

fn collect_allocator_blockers(
    formula: &Formula,
    blockers: &mut Vec<BinarySecurityBlockingEvidence>,
) {
    if let Some(name) = formula.var_name()
        && let Some(blocker) = allocator_blocker_from_var_name(name)
        && !blockers.contains(&blocker)
    {
        blockers.push(blocker);
    }

    for child in formula.children() {
        collect_allocator_blockers(child, blockers);
    }
}

fn allocator_blocker_from_var_name(name: &str) -> Option<BinarySecurityBlockingEvidence> {
    let remainder = name.strip_prefix(BINARY_ALLOCATOR_BLOCKER_PREFIX)?;
    let (code, detail) = remainder.split_once("__").unwrap_or((remainder, "unknown"));
    Some(BinarySecurityBlockingEvidence::new(code, detail))
}

/// Generate fail-closed allocator lifetime VCs from synthetic binary facts.
///
/// The formula convention is bad-state reachability. Each emitted formula is a
/// conjunction of named blocker atoms that record the missing or already-bad
/// allocator facts preventing proof-grade acceptance. Later allocator modeling
/// can replace those atoms with path-sensitive alias and reachability
/// constraints without changing the typed VC family.
#[must_use]
pub fn generate_allocator_lifetime_vcs(
    func_name: &str,
    events: &[AllocatorLifetimeFact],
    accesses: &[AllocatorLifetimeAccessFact],
) -> Vec<VerificationCondition> {
    let mut vcs = Vec::new();
    let mut freed_allocations: Vec<String> = Vec::new();

    for event in events {
        match event.kind {
            AllocatorLifetimeFactKind::Allocate => {
                if let Some(allocation_id) = &event.allocation_id {
                    freed_allocations.retain(|freed| freed != allocation_id);
                }
            }
            AllocatorLifetimeFactKind::Free => {
                if event.pointer.is_none() || event.allocation_id.is_none() {
                    let mut blockers = Vec::new();
                    if event.allocation_id.is_none() {
                        push_allocator_blocker(
                            &mut blockers,
                            BLOCKER_MISSING_ALLOCATION_IDENTITY,
                            allocator_evidence_detail("free", &event.location, &event.evidence),
                        );
                    }
                    if event.pointer.is_none() {
                        push_allocator_blocker(
                            &mut blockers,
                            BLOCKER_MISSING_POINTER_FORMULA,
                            allocator_evidence_detail("free", &event.location, &event.evidence),
                        );
                    }
                    vcs.push(allocator_lifetime_vc(
                        VcKind::DoubleFree,
                        func_name,
                        event.location.clone(),
                        blockers,
                    ));
                }

                let Some(allocation_id) = &event.allocation_id else {
                    continue;
                };

                if freed_allocations.iter().any(|freed| freed == allocation_id) {
                    let mut blockers = Vec::new();
                    push_allocator_blocker(
                        &mut blockers,
                        BLOCKER_ALLOCATION_ALREADY_FREED,
                        format!(
                            "{}; allocation_id={allocation_id}; {}",
                            allocator_evidence_detail(
                                "second free",
                                &event.location,
                                &event.evidence
                            ),
                            pointer_evidence_label(&event.pointer)
                        ),
                    );
                    if event.pointer.is_none() {
                        push_allocator_blocker(
                            &mut blockers,
                            BLOCKER_MISSING_POINTER_FORMULA,
                            allocator_evidence_detail(
                                "second free",
                                &event.location,
                                &event.evidence,
                            ),
                        );
                    }
                    vcs.push(allocator_lifetime_vc(
                        VcKind::DoubleFree,
                        func_name,
                        event.location.clone(),
                        blockers,
                    ));
                } else {
                    freed_allocations.push(allocation_id.clone());
                }
            }
        }
    }

    if !events.is_empty() {
        for access in accesses {
            let may_alias_freed_allocation = match &access.allocation_id {
                Some(allocation_id) => freed_allocations.iter().any(|freed| freed == allocation_id),
                None => true,
            };

            if access.pointer.is_none() || may_alias_freed_allocation {
                let mut blockers = Vec::new();
                if access.pointer.is_none() {
                    push_allocator_blocker(
                        &mut blockers,
                        BLOCKER_MISSING_POINTER_FORMULA,
                        allocator_evidence_detail(
                            allocator_access_label(access.kind),
                            &access.location,
                            &access.evidence,
                        ),
                    );
                }

                match &access.allocation_id {
                    Some(allocation_id)
                        if freed_allocations.iter().any(|freed| freed == allocation_id) =>
                    {
                        push_allocator_blocker(
                            &mut blockers,
                            BLOCKER_ACCESS_AFTER_FREE,
                            format!(
                                "{}; allocation_id={allocation_id}; {}",
                                allocator_evidence_detail(
                                    allocator_access_label(access.kind),
                                    &access.location,
                                    &access.evidence,
                                ),
                                pointer_evidence_label(&access.pointer)
                            ),
                        );
                    }
                    Some(_) => {}
                    None => {
                        push_allocator_blocker(
                            &mut blockers,
                            BLOCKER_MISSING_ALLOCATION_IDENTITY,
                            allocator_evidence_detail(
                                allocator_access_label(access.kind),
                                &access.location,
                                &access.evidence,
                            ),
                        );
                        push_allocator_blocker(
                            &mut blockers,
                            BLOCKER_UNRESOLVED_FREED_ALLOCATION_ALIAS,
                            allocator_evidence_detail(
                                allocator_access_label(access.kind),
                                &access.location,
                                &access.evidence,
                            ),
                        );
                    }
                }

                if blockers.is_empty() {
                    push_allocator_blocker(
                        &mut blockers,
                        BLOCKER_UNKNOWN_ALLOCATOR_LIFETIME,
                        allocator_evidence_detail(
                            allocator_access_label(access.kind),
                            &access.location,
                            &access.evidence,
                        ),
                    );
                }
                vcs.push(allocator_lifetime_vc(
                    VcKind::UseAfterFree,
                    func_name,
                    access.location.clone(),
                    blockers,
                ));
            }
        }
    }

    vcs
}

fn allocator_lifetime_vc(
    kind: VcKind,
    func_name: &str,
    location: SourceSpan,
    blockers: Vec<BinarySecurityBlockingEvidence>,
) -> VerificationCondition {
    VerificationCondition {
        kind,
        function: func_name.to_string().into(),
        location,
        formula: allocator_blocker_formula(&blockers),
        contract_metadata: None,
    }
}

fn allocator_blocker_formula(blockers: &[BinarySecurityBlockingEvidence]) -> Formula {
    let atoms: Vec<_> = blockers.iter().map(allocator_blocker_atom).collect();
    match atoms.as_slice() {
        [] => Formula::Var(
            allocator_blocker_var_name(&BinarySecurityBlockingEvidence::new(
                BLOCKER_UNKNOWN_ALLOCATOR_LIFETIME,
                "missing_allocator_blockers",
            )),
            Sort::Bool,
        ),
        [single] => (*single).clone(),
        _ => Formula::And(atoms),
    }
}

fn allocator_blocker_atom(blocker: &BinarySecurityBlockingEvidence) -> Formula {
    Formula::Var(allocator_blocker_var_name(blocker), Sort::Bool)
}

fn allocator_blocker_var_name(blocker: &BinarySecurityBlockingEvidence) -> String {
    format!(
        "{BINARY_ALLOCATOR_BLOCKER_PREFIX}{}__{}",
        sanitize_evidence_part(&blocker.code),
        sanitize_evidence_part(&blocker.detail)
    )
}

fn push_allocator_blocker(
    blockers: &mut Vec<BinarySecurityBlockingEvidence>,
    code: &'static str,
    detail: String,
) {
    let blocker = BinarySecurityBlockingEvidence::new(code, detail);
    if !blockers.contains(&blocker) {
        blockers.push(blocker);
    }
}

fn allocator_evidence_detail(kind: &str, location: &SourceSpan, evidence: &str) -> String {
    format!("{kind} at {}; evidence={evidence}", location.file)
}

fn allocator_access_label(kind: AllocatorLifetimeAccessKind) -> &'static str {
    match kind {
        AllocatorLifetimeAccessKind::Read => "heap read",
        AllocatorLifetimeAccessKind::Write => "heap write",
    }
}

fn pointer_evidence_label(pointer: &Option<Formula>) -> String {
    match pointer {
        Some(pointer) => format!("pointer={pointer:?}"),
        None => "pointer=<missing>".to_string(),
    }
}

fn sanitize_evidence_part(input: &str) -> String {
    let mut out = String::with_capacity(input.len());
    let mut previous_was_sep = false;

    for ch in input.chars() {
        if ch.is_ascii_alphanumeric() {
            out.push(ch.to_ascii_lowercase());
            previous_was_sep = false;
        } else if !previous_was_sep && !out.is_empty() {
            out.push('_');
            previous_was_sep = true;
        }
    }

    while out.ends_with('_') {
        out.pop();
    }

    if out.is_empty() { "unknown".to_string() } else { out }
}

/// Generate copy-sink length VCs from recovered binary facts.
///
/// The VC formula is a bad-state formula: SAT means the sink may copy more bytes
/// than the destination capacity. Missing destination, length, or capacity
/// evidence is represented as `true`, preserving fail-closed behavior and the
/// explicit binary copy-sink length family label.
#[must_use]
pub fn generate_copy_sink_length_vcs(
    func_name: &str,
    facts: &[BinaryCopySinkLengthFact],
) -> Vec<VerificationCondition> {
    facts
        .iter()
        .filter(|fact| copy_sink_spec(&fact.callee).is_some())
        .map(|fact| copy_sink_length_vc_from_fact(func_name, fact))
        .collect()
}

fn copy_sink_length_vc_from_fact(
    func_name: &str,
    fact: &BinaryCopySinkLengthFact,
) -> VerificationCondition {
    let formula = match (&fact.copy_length, &fact.dest_capacity) {
        (Some(copy_length), Some(dest_capacity)) => {
            Formula::Gt(Box::new(copy_length.clone()), Box::new(dest_capacity.clone()))
        }
        _ => Formula::Bool(true),
    };
    let desc = copy_sink_length_desc(
        &fact.callee,
        fact.dest.is_some(),
        fact.copy_length.is_some(),
        fact.dest_capacity.is_some(),
        &fact.evidence,
    );

    VerificationCondition {
        kind: VcKind::BinaryCopySinkLengthViolation { callee: fact.callee.clone(), desc },
        function: func_name.to_string().into(),
        location: fact.location.clone(),
        formula,
        contract_metadata: None,
    }
}

fn copy_sink_length_call_vc(
    func_name: &str,
    lifted: &LiftedFunction,
    block: &trust_types::BasicBlock,
) -> Option<VerificationCondition> {
    let Terminator::Call { func: callee, args, span, .. } = &block.terminator else {
        return None;
    };
    let spec = copy_sink_spec(callee)?;
    let dest = args.get(spec.dest_index).map(|arg| format_operand_formula(arg, lifted));
    let copy_length = spec
        .length_index
        .and_then(|length_index| args.get(length_index))
        .map(|arg| format_operand_formula(arg, lifted));

    let fact = BinaryCopySinkLengthFact {
        callee: spec.short_name.to_string(),
        dest,
        copy_length,
        dest_capacity: None,
        location: span.clone(),
        evidence: format!(
            "{} call recovered from lifted binary TrustIr without destination-capacity metadata",
            spec.short_name
        ),
    };

    Some(copy_sink_length_vc_from_fact(func_name, &fact))
}

#[derive(Debug, Clone, Copy)]
struct CopySinkSpec {
    short_name: &'static str,
    dest_index: usize,
    length_index: Option<usize>,
}

fn copy_sink_spec(callee: &str) -> Option<CopySinkSpec> {
    let short = callee.rsplit("::").next().unwrap_or(callee);
    let spec = match short {
        "memcpy" => CopySinkSpec { short_name: "memcpy", dest_index: 0, length_index: Some(2) },
        "memmove" => CopySinkSpec { short_name: "memmove", dest_index: 0, length_index: Some(2) },
        "memset" => CopySinkSpec { short_name: "memset", dest_index: 0, length_index: Some(2) },
        "read" => CopySinkSpec { short_name: "read", dest_index: 1, length_index: Some(2) },
        "fread" => CopySinkSpec { short_name: "fread", dest_index: 0, length_index: None },
        "strncpy" => CopySinkSpec { short_name: "strncpy", dest_index: 0, length_index: Some(2) },
        "strncat" => CopySinkSpec { short_name: "strncat", dest_index: 0, length_index: Some(2) },
        "snprintf" => CopySinkSpec { short_name: "snprintf", dest_index: 0, length_index: Some(1) },
        "strcpy" => CopySinkSpec { short_name: "strcpy", dest_index: 0, length_index: None },
        "strcat" => CopySinkSpec { short_name: "strcat", dest_index: 0, length_index: None },
        "sprintf" => CopySinkSpec { short_name: "sprintf", dest_index: 0, length_index: None },
        _ => return None,
    };
    Some(spec)
}

fn copy_sink_length_desc(
    callee: &str,
    has_dest: bool,
    has_copy_length: bool,
    has_dest_capacity: bool,
    evidence: &str,
) -> String {
    let mut missing = Vec::new();
    if !has_dest {
        missing.push("destination pointer");
    }
    if !has_copy_length {
        missing.push("copy length");
    }
    if !has_dest_capacity {
        missing.push("destination capacity");
    }

    if missing.is_empty() {
        format!("copy sink length may exceed destination capacity for `{callee}`; {evidence}")
    } else {
        format!("copy sink length for `{callee}` lacks {}; {evidence}", missing.join(", "))
    }
}

/// Generate verification conditions from a lifted binary function.
///
/// Produces both:
/// 1. Standard safety VCs (overflow, division by zero, etc.) by running the
///    existing `generate_vcs` pipeline on the TrustIr body.
/// 2. Binary-specific memory model VCs (out-of-bounds access, stack discipline).
/// 3. Unsupported binary ledger records that still require fail-closed review.
///
/// Returns all VCs sorted by location for deterministic output.
#[must_use]
pub fn generate_binary_vcs(lifted: &LiftedFunction) -> Vec<VerificationCondition> {
    let verifiable = lift_to_verifiable(lifted);
    let mut vcs = crate::generate_vcs(&verifiable);

    // binary-lifted integer arithmetic is machine modular
    // arithmetic. Compiled `add`/`sub`/`mul` wraps, and compiled shifts are not
    // Rust source shift-overflow checks. trust-mc-lib owns that lane; strip the
    // source-style obligations `generate_vcs` produces after lowering the lift
    // into Trust IR.
    vcs.retain(|vc| {
        !matches!(vc.kind, VcKind::ArithmeticOverflow { .. } | VcKind::ShiftOverflow { .. })
    });

    // Binary-specific VCs: memory model and stack discipline.
    vcs.extend(generate_memory_model_vcs(lifted));
    vcs.extend(generate_control_flow_vcs(lifted));
    vcs.extend(generate_aarch64_selected_slice_boundary_vcs(lifted));
    vcs.extend(generate_unsupported_ledger_vcs(lifted));

    vcs
}

const AARCH64_ACCEPTED_RELEASE_ACQUIRE_MARKER: &str = "accepted-slice:aarch64.release_acquire";
const AARCH64_RELEASE_ACQUIRE_EVIDENCE_SCHEMA: &str =
    "trust-lift.aarch64.release_acquire_ordering_evidence@1";
const AARCH64_RELEASE_ACQUIRE_EVIDENCE_ID_PREFIX: &str = "aarch64-ra:sha256:";
const AARCH64_ORDERING_MONITOR_EVIDENCE_ROW_SCHEMA: &str =
    "trust-lift.aarch64.ordering_monitor_evidence_row@1";
const AARCH64_ORDERING_MONITOR_EVIDENCE_ROW_TYPE: &str = "aarch64_ordering_monitor_evidence";
const AARCH64_REVIEWED_UNSUPPORTED_ABSENCE: &str = "[barrier absent-reviewed, exclusive-monitor absent-reviewed, store-conditional-status absent-reviewed, system-register absent-reviewed, FP/SIMD absent-reviewed, trap absent-reviewed, syscall absent-reviewed, unsupported-opcode absent-reviewed]";
const AARCH64_ATOMIC_OBLIGATION_EVIDENCE_SCHEMA: &str =
    "trust_vcgen.aarch64.atomic_obligation_evidence@1";
const AARCH64_ATOMIC_OBLIGATION_EVIDENCE_ID_PREFIX: &str = "aarch64-atomic:sha256:";

/// Check narrow AArch64 accepted-slice provenance carried outside the
/// unsupported ledger.
///
/// The semantic lifter may emit an empty unsupported ledger for the exact
/// STLR/LDAR selected boundary only when the memory facts carry proof-consumed
/// ordering evidence and reviewed absence certificates for facts not claimed by
/// the slice. Any malformed claim becomes an explicit fail-closed VC.
#[must_use]
pub fn generate_aarch64_selected_slice_boundary_vcs(
    lifted: &LiftedFunction,
) -> Vec<VerificationCondition> {
    let accesses = lifted
        .memory_accesses
        .iter()
        .filter(|access| aarch64_access_claims_release_acquire_boundary(access))
        .collect::<Vec<_>>();
    if accesses.is_empty() {
        return Vec::new();
    }

    let mut missing = BTreeSet::new();
    if accesses.len() != 2 {
        missing.insert("exact two-access STLR/LDAR selected slice".to_string());
    }
    if !lifted.unsupported.is_empty() {
        missing.insert("unsupported-ledger-empty boundary".to_string());
        missing.extend(lifted.unsupported.records.iter().enumerate().map(|(index, record)| {
            format!(
                "unsupported-ledger-record[{index}] {}",
                aarch64_unsupported_record_summary(record)
            )
        }));
    }

    let release = aarch64_selected_access_with_role(&accesses, "release");
    let acquire = aarch64_selected_access_with_role(&accesses, "acquire");

    match release {
        Some(access) if access.kind == MemoryAccessKind::Write => {
            aarch64_require_selected_access_witnesses(
                access,
                "release",
                &[
                    "status=proof-consumed",
                    "release ordering event",
                    "same atomic location witness",
                    AARCH64_RELEASE_ACQUIRE_EVIDENCE_SCHEMA,
                    AARCH64_RELEASE_ACQUIRE_EVIDENCE_ID_PREFIX,
                    "artifact_digest=sha256:",
                    "artifact_row_schema=",
                    "artifact_row_type=aarch64_ordering_monitor_evidence",
                    "artifact_row_status=accepted",
                    "selected_image_identity=",
                    "selected_image_digest=sha256:",
                    "instruction_provenance_digest=sha256:",
                    "memory_access_digest=sha256:",
                    "opcode=Stlr",
                    "ordering=Release",
                    "ordering_event=release ordering event",
                    "unsupported_ledger_boundary=explicit-empty",
                    "unsupported_ledger_records=0",
                    "exclusive_monitor=None",
                    "exclusive_monitor_witness=not-applicable-reviewed",
                    "store_conditional_status=not-applicable-reviewed",
                    "synchronization_edge=absent-reviewed",
                    "happens_before_witness=absent-reviewed",
                    "thread_identity=absent-reviewed",
                    "reviewed_unsupported_absence=",
                    "exclusive monitor absent-reviewed",
                    "store-conditional status not-applicable-reviewed",
                    "synchronization edge absent-reviewed",
                    "happens-before witness absent-reviewed",
                    "thread identity absent-reviewed",
                    "aarch64_ordering_monitor_evidence_schema=",
                    "aarch64_ordering_monitor_evidence_status=accepted",
                    "aarch64_ordering_monitor_evidence_opcode=Stlr",
                    "aarch64_ordering_monitor_evidence_ordering=Release",
                    "aarch64_ordering_monitor_evidence_exclusive_monitor=None",
                    "aarch64_ordering_monitor_evidence_digest=sha256:",
                    "aarch64_ordering_monitor_evidence_blockers=[]",
                    "release_transcript_consumed=true",
                    "release_transcript_digest=sha256:",
                    "no FP/SIMD/syscall/trap/exception claim",
                ],
                &mut missing,
            );
        }
        Some(_) => {
            missing.insert("release memory write fact".to_string());
        }
        None => {
            missing.insert("release ordering fact".to_string());
        }
    }

    match acquire {
        Some(access) if access.kind == MemoryAccessKind::Read => {
            aarch64_require_selected_access_witnesses(
                access,
                "acquire",
                &[
                    "status=proof-consumed",
                    "acquire ordering event",
                    "same atomic location witness",
                    AARCH64_RELEASE_ACQUIRE_EVIDENCE_SCHEMA,
                    AARCH64_RELEASE_ACQUIRE_EVIDENCE_ID_PREFIX,
                    "artifact_digest=sha256:",
                    "artifact_row_schema=",
                    "artifact_row_type=aarch64_ordering_monitor_evidence",
                    "artifact_row_status=accepted",
                    "selected_image_identity=",
                    "selected_image_digest=sha256:",
                    "instruction_provenance_digest=sha256:",
                    "memory_access_digest=sha256:",
                    "opcode=Ldar",
                    "ordering=Acquire",
                    "ordering_event=acquire ordering event",
                    "unsupported_ledger_boundary=explicit-empty",
                    "unsupported_ledger_records=0",
                    "exclusive_monitor=None",
                    "exclusive_monitor_witness=not-applicable-reviewed",
                    "store_conditional_status=not-applicable-reviewed",
                    "synchronization_edge=absent-reviewed",
                    "happens_before_witness=absent-reviewed",
                    "thread_identity=absent-reviewed",
                    "reviewed_unsupported_absence=",
                    "exclusive monitor absent-reviewed",
                    "store-conditional status not-applicable-reviewed",
                    "synchronization edge absent-reviewed",
                    "happens-before witness absent-reviewed",
                    "thread identity absent-reviewed",
                    "aarch64_ordering_monitor_evidence_schema=",
                    "aarch64_ordering_monitor_evidence_status=accepted",
                    "aarch64_ordering_monitor_evidence_opcode=Ldar",
                    "aarch64_ordering_monitor_evidence_ordering=Acquire",
                    "aarch64_ordering_monitor_evidence_exclusive_monitor=None",
                    "aarch64_ordering_monitor_evidence_digest=sha256:",
                    "aarch64_ordering_monitor_evidence_blockers=[]",
                    "release_transcript_consumed=true",
                    "release_transcript_digest=sha256:",
                    "no FP/SIMD/syscall/trap/exception claim",
                ],
                &mut missing,
            );
        }
        Some(_) => {
            missing.insert("acquire memory read fact".to_string());
        }
        None => {
            missing.insert("acquire ordering fact".to_string());
        }
    }

    if let (Some(release), Some(acquire)) = (release, acquire) {
        if release.address != acquire.address {
            missing.insert("same atomic location witness".to_string());
        }
        aarch64_require_selected_slice_evidence(lifted, release, acquire, &mut missing);
    }

    if missing.is_empty() {
        return Vec::new();
    }

    let evidence = aarch64_selected_slice_evidence_summary(&accesses);

    let location = accesses.first().map_or_else(
        || SourceSpan::binary_address(lifted.entry_point),
        |access| access.origin.span(),
    );
    vec![VerificationCondition {
        kind: VcKind::UnsupportedMir {
            kind: "AArch64SelectedSliceBoundaryNotProofConsumed".to_string(),
            detail: format!(
                "AArch64 selected release/acquire slice remains fail-closed; evidence_identifiers=[{}]; missing_witnesses=[{}]; unsupported ledger is empty only for proof-consumed ordering facts plus reviewed absence certificates and explicit empty-ledger boundary evidence",
                aarch64_witness_list(&evidence),
                aarch64_witness_list(&missing.into_iter().collect::<Vec<_>>())
            ),
        },
        function: lifted.name.clone().into(),
        location,
        formula: Formula::Bool(true),
        contract_metadata: None,
    }]
}

fn aarch64_access_claims_release_acquire_boundary(access: &MemoryAccessFact) -> bool {
    access
        .provenance
        .as_deref()
        .is_some_and(|provenance| provenance.contains(AARCH64_ACCEPTED_RELEASE_ACQUIRE_MARKER))
}

fn aarch64_selected_access_with_role<'a>(
    accesses: &'a [&'a MemoryAccessFact],
    role: &str,
) -> Option<&'a MemoryAccessFact> {
    let role = format!("role={role}");
    accesses.iter().copied().find(|access| {
        access.provenance.as_deref().is_some_and(|provenance| provenance.contains(&role))
    })
}

fn aarch64_require_selected_access_witnesses(
    access: &MemoryAccessFact,
    role: &str,
    required: &[&str],
    missing: &mut BTreeSet<String>,
) {
    let provenance = access.provenance.as_deref().unwrap_or_default();
    for witness in required {
        if !provenance.contains(witness) {
            missing.insert(format!("{role} {witness}"));
        }
    }
}

fn aarch64_require_selected_slice_evidence(
    lifted: &LiftedFunction,
    release: &MemoryAccessFact,
    acquire: &MemoryAccessFact,
    missing: &mut BTreeSet<String>,
) {
    let selected_image_digest =
        aarch64_release_acquire_selected_image_digest(lifted, release, acquire);
    aarch64_require_selected_access_evidence(release, "release", &selected_image_digest, missing);
    aarch64_require_selected_access_evidence(acquire, "acquire", &selected_image_digest, missing);
}

fn aarch64_require_selected_access_evidence(
    access: &MemoryAccessFact,
    role: &str,
    selected_image_digest: &str,
    missing: &mut BTreeSet<String>,
) {
    let provenance = access.provenance.as_deref().unwrap_or_default();
    let expected_opcode = aarch64_release_acquire_opcode_for_role(role).unwrap_or("<unknown>");
    let expected_ordering = aarch64_release_acquire_ordering_for_role(role).unwrap_or("<unknown>");
    let expected_ordering_event =
        aarch64_release_acquire_ordering_event_for_role(role).unwrap_or("<unknown>");
    let instruction_digest = aarch64_instruction_provenance_digest(&access.origin);
    let memory_digest = aarch64_memory_access_digest(access);
    let evidence_hash = aarch64_release_acquire_evidence_hash(
        role,
        selected_image_digest,
        &instruction_digest,
        &memory_digest,
    );
    let evidence_id = aarch64_release_acquire_evidence_id(
        role,
        selected_image_digest,
        &instruction_digest,
        &memory_digest,
    );

    let expected = [
        ("evidence_schema", AARCH64_RELEASE_ACQUIRE_EVIDENCE_SCHEMA.to_string()),
        ("evidence_id", evidence_id),
        ("artifact_digest", format!("sha256:{evidence_hash}")),
        ("artifact_row_schema", AARCH64_ORDERING_MONITOR_EVIDENCE_ROW_SCHEMA.to_string()),
        ("artifact_row_type", AARCH64_ORDERING_MONITOR_EVIDENCE_ROW_TYPE.to_string()),
        ("artifact_row_status", "accepted".to_string()),
        ("selected_image_digest", format!("sha256:{selected_image_digest}")),
        ("instruction_provenance_digest", format!("sha256:{instruction_digest}")),
        ("memory_access_digest", format!("sha256:{memory_digest}")),
        ("opcode", expected_opcode.to_string()),
        ("ordering", expected_ordering.to_string()),
        ("ordering_event", expected_ordering_event.to_string()),
        ("exclusive_monitor", "None".to_string()),
        ("exclusive_monitor_witness", "not-applicable-reviewed".to_string()),
        ("store_conditional_status", "not-applicable-reviewed".to_string()),
        ("synchronization_edge", "absent-reviewed".to_string()),
        ("happens_before_witness", "absent-reviewed".to_string()),
        ("thread_identity", "absent-reviewed".to_string()),
        ("unsupported_ledger_boundary", "explicit-empty".to_string()),
        ("unsupported_ledger_records", "0".to_string()),
        ("reviewed_unsupported_absence", AARCH64_REVIEWED_UNSUPPORTED_ABSENCE.to_string()),
        (
            "aarch64_ordering_monitor_evidence_schema",
            AARCH64_ORDERING_MONITOR_EVIDENCE_ROW_SCHEMA.to_string(),
        ),
        ("aarch64_ordering_monitor_evidence_status", "accepted".to_string()),
        ("aarch64_ordering_monitor_evidence_opcode", expected_opcode.to_string()),
        ("aarch64_ordering_monitor_evidence_ordering", expected_ordering.to_string()),
        ("aarch64_ordering_monitor_evidence_exclusive_monitor", "None".to_string()),
        ("aarch64_ordering_monitor_evidence_digest", format!("sha256:{evidence_hash}")),
        ("aarch64_ordering_monitor_evidence_blockers", "[]".to_string()),
        ("release_transcript_consumed", "true".to_string()),
        ("release_transcript_digest", format!("sha256:{evidence_hash}")),
    ];

    for (key, expected_value) in expected {
        match aarch64_provenance_value(provenance, key) {
            Some(actual) if actual == expected_value => {}
            Some(actual) => {
                missing.insert(format!("{role} {key}={expected_value} (found {actual})"));
            }
            None => {
                missing.insert(format!("{role} {key}={expected_value}"));
            }
        }
    }

    if aarch64_provenance_value(provenance, "selected_image_identity").is_none_or(str::is_empty) {
        missing.insert(format!("{role} selected_image_identity"));
    }
}

fn aarch64_selected_slice_evidence_summary(accesses: &[&MemoryAccessFact]) -> Vec<String> {
    let mut evidence = Vec::new();
    for access in accesses {
        let provenance = access.provenance.as_deref().unwrap_or_default();
        let role = aarch64_provenance_value(provenance, "role").unwrap_or("unknown");
        for key in [
            "evidence_id",
            "artifact_digest",
            "selected_image_digest",
            "aarch64_ordering_monitor_evidence_digest",
            "release_transcript_digest",
        ] {
            let value = aarch64_provenance_value(provenance, key).unwrap_or("<missing>");
            evidence.push(format!("{role} {key}={value}"));
        }
    }
    evidence.sort();
    evidence.dedup();
    evidence
}

fn aarch64_release_acquire_selected_image_digest(
    lifted: &LiftedFunction,
    release: &MemoryAccessFact,
    acquire: &MemoryAccessFact,
) -> String {
    let function_entry = release
        .origin
        .function_entry
        .or(acquire.origin.function_entry)
        .unwrap_or(lifted.entry_point);
    stable_sha256_hex(
        aarch64_release_acquire_selected_image_material(
            function_entry,
            &release.origin,
            &acquire.origin,
        )
        .as_bytes(),
    )
}

fn aarch64_release_acquire_selected_image_material(
    function_entry: u64,
    release_origin: &BinaryOrigin,
    acquire_origin: &BinaryOrigin,
) -> String {
    format!(
        "schema={AARCH64_RELEASE_ACQUIRE_EVIDENCE_SCHEMA}\n\
         boundary=aarch64.release_acquire\n\
         selected_image_identity=function_entry=0x{function_entry:x},release=0x{:x}/0x{},acquire=0x{:x}/0x{}\n\
         release_origin={}\n\
         acquire_origin={}\n\
         unsupported_ledger_boundary=explicit-empty\n\
         unsupported_ledger_records=0",
        release_origin.instruction_address,
        aarch64_optional_encoding(release_origin.encoding),
        acquire_origin.instruction_address,
        aarch64_optional_encoding(acquire_origin.encoding),
        aarch64_binary_origin_material(release_origin),
        aarch64_binary_origin_material(acquire_origin),
    )
}

fn aarch64_optional_encoding(encoding: Option<u32>) -> String {
    encoding.map_or_else(|| "unavailable".to_string(), |encoding| format!("{encoding:08x}"))
}

fn aarch64_instruction_bytes_display(bytes: &[u8]) -> String {
    let bytes = bytes.iter().map(|byte| format!("0x{byte:02x}")).collect::<Vec<_>>().join(", ");
    format!("[{bytes}]")
}

fn aarch64_binary_origin_material(origin: &BinaryOrigin) -> String {
    format!(
        "binary_path={};function_entry={};instruction_address=0x{:x};instruction_size={};encoding={};instruction_bytes={}",
        origin.binary_path.as_deref().unwrap_or("<unavailable>"),
        origin
            .function_entry
            .map_or_else(|| "<unavailable>".to_string(), |entry| format!("0x{entry:x}")),
        origin.instruction_address,
        origin
            .instruction_size
            .map_or_else(|| "<unavailable>".to_string(), |size| size.to_string()),
        origin
            .encoding
            .map_or_else(|| "<unavailable>".to_string(), |encoding| format!("0x{encoding:08x}")),
        aarch64_instruction_bytes_display(&origin.instruction_bytes),
    )
}

fn aarch64_memory_access_material(access: &MemoryAccessFact) -> String {
    let mut taint = access.taint.clone();
    taint.sort();
    format!(
        "origin={};kind={:?};address={:?};width_bytes={};endianness={:?};region={:?};base_object={};offset={:?};extent={};taint=[{}]",
        aarch64_binary_origin_material(&access.origin),
        access.kind,
        access.address,
        access.width_bytes,
        access.endianness,
        access.region,
        access.base_object.as_deref().unwrap_or("<none>"),
        access.offset,
        access.extent.map_or_else(|| "<none>".to_string(), |extent| extent.to_string()),
        taint.join(","),
    )
}

fn aarch64_instruction_provenance_digest(origin: &BinaryOrigin) -> String {
    stable_sha256_hex(aarch64_binary_origin_material(origin).as_bytes())
}

fn aarch64_memory_access_digest(access: &MemoryAccessFact) -> String {
    stable_sha256_hex(aarch64_memory_access_material(access).as_bytes())
}

fn aarch64_release_acquire_evidence_hash(
    role: &str,
    selected_image_digest: &str,
    instruction_provenance_digest: &str,
    memory_access_digest: &str,
) -> String {
    let opcode = aarch64_release_acquire_opcode_for_role(role).unwrap_or("<unknown>");
    let ordering = aarch64_release_acquire_ordering_for_role(role).unwrap_or("<unknown>");
    let ordering_event =
        aarch64_release_acquire_ordering_event_for_role(role).unwrap_or("<unknown>");
    stable_sha256_hex(
        format!(
            "schema={AARCH64_RELEASE_ACQUIRE_EVIDENCE_SCHEMA}\n\
             boundary=aarch64.release_acquire\n\
             artifact_row_schema={AARCH64_ORDERING_MONITOR_EVIDENCE_ROW_SCHEMA}\n\
             artifact_row_type={AARCH64_ORDERING_MONITOR_EVIDENCE_ROW_TYPE}\n\
             artifact_row_status=accepted\n\
             role={role}\n\
             opcode={opcode}\n\
             ordering={ordering}\n\
             exclusive_monitor=None\n\
             exclusive_monitor_witness=not-applicable-reviewed\n\
             store_conditional_status=not-applicable-reviewed\n\
             ordering_event={ordering_event}\n\
             synchronization_edge=absent-reviewed\n\
             happens_before_witness=absent-reviewed\n\
             thread_identity=absent-reviewed\n\
             selected_image_digest=sha256:{selected_image_digest}\n\
             instruction_provenance_digest=sha256:{instruction_provenance_digest}\n\
             memory_access_digest=sha256:{memory_access_digest}\n\
             unsupported_ledger_boundary=explicit-empty\n\
             unsupported_ledger_records=0\n\
             reviewed_unsupported_absence={AARCH64_REVIEWED_UNSUPPORTED_ABSENCE}\n\
             consumed_witnesses=[{ordering_event}, same atomic location witness]\n\
             aarch64_ordering_monitor_evidence_schema={AARCH64_ORDERING_MONITOR_EVIDENCE_ROW_SCHEMA}\n\
             aarch64_ordering_monitor_evidence_status=accepted\n\
             aarch64_ordering_monitor_evidence_opcode={opcode}\n\
             aarch64_ordering_monitor_evidence_ordering={ordering}\n\
             aarch64_ordering_monitor_evidence_exclusive_monitor=None\n\
             aarch64_ordering_monitor_evidence_blockers=[]\n\
             release_transcript_consumed=true",
        )
        .as_bytes(),
    )
}

fn aarch64_release_acquire_evidence_id(
    role: &str,
    selected_image_digest: &str,
    instruction_provenance_digest: &str,
    memory_access_digest: &str,
) -> String {
    format!(
        "{AARCH64_RELEASE_ACQUIRE_EVIDENCE_ID_PREFIX}{}",
        aarch64_release_acquire_evidence_hash(
            role,
            selected_image_digest,
            instruction_provenance_digest,
            memory_access_digest,
        )
    )
}

fn aarch64_provenance_value<'a>(provenance: &'a str, key: &str) -> Option<&'a str> {
    let prefix = format!("{key}=");
    provenance.split(';').map(str::trim).find_map(|part| part.strip_prefix(&prefix))
}

fn aarch64_release_acquire_opcode_for_role(role: &str) -> Option<&'static str> {
    match role {
        "release" => Some("Stlr"),
        "acquire" => Some("Ldar"),
        _ => None,
    }
}

fn aarch64_release_acquire_ordering_for_role(role: &str) -> Option<&'static str> {
    match role {
        "release" => Some("Release"),
        "acquire" => Some("Acquire"),
        _ => None,
    }
}

fn aarch64_release_acquire_ordering_event_for_role(role: &str) -> Option<&'static str> {
    match role {
        "release" => Some("release ordering event"),
        "acquire" => Some("acquire ordering event"),
        _ => None,
    }
}

fn aarch64_unsupported_record_summary(record: &UnsupportedRecord) -> String {
    format!(
        "stage={}; opcode={}; feature={}",
        record.stage,
        record.opcode.as_deref().unwrap_or("<none>"),
        record.feature
    )
}

/// Convert unsupported lifted-binary ledger records into fail-closed VCs.
///
/// Ledger records are diagnostic evidence, not proofs. Any record still present
/// on a lifted function must become an explicit obligation so unsupported binary
/// facts cannot disappear between lifting and reporting.
#[must_use]
pub fn generate_unsupported_ledger_vcs(lifted: &LiftedFunction) -> Vec<VerificationCondition> {
    let aarch64_consumption = aarch64_atomic_consumption_by_record(lifted);
    lifted
        .unsupported
        .records
        .iter()
        .enumerate()
        .map(|(index, record)| {
            let related_memory_accesses =
                aarch64_related_memory_accesses(record, &lifted.memory_accesses);
            unsupported_record_vc(
                &lifted.name,
                lifted.entry_point,
                record,
                &related_memory_accesses,
                aarch64_consumption.get(&index),
            )
        })
        .collect()
}

fn unsupported_record_vc(
    func_name: &str,
    fallback_entry: u64,
    record: &UnsupportedRecord,
    related_memory_accesses: &[&MemoryAccessFact],
    aarch64_consumption: Option<&Aarch64ProofObligationConsumption>,
) -> VerificationCondition {
    let location = record.origin.as_ref().map_or_else(
        || SourceSpan::binary_address(fallback_entry),
        trust_types::BinaryOrigin::span,
    );
    let detail = unsupported_record_detail(record);
    let kind = if let Some(fact) = record.aarch64_atomic_semantic_fact() {
        VcKind::UnsupportedMir {
            kind: "AArch64AtomicSemanticFactNotProofConsumed".to_string(),
            detail: aarch64_atomic_fact_rejection_detail(
                record,
                &fact,
                related_memory_accesses,
                aarch64_consumption,
            ),
        }
    } else if unsupported_record_is_memory(record) {
        VcKind::UnsafeOperation { desc: format!("unsupported binary memory fact: {detail}") }
    } else {
        VcKind::UnsupportedMir { kind: unsupported_record_kind(record), detail }
    };

    VerificationCondition {
        kind,
        function: func_name.to_string().into(),
        location,
        formula: Formula::Bool(true),
        contract_metadata: None,
    }
}

fn aarch64_atomic_fact_rejection_detail(
    record: &UnsupportedRecord,
    fact: &Aarch64AtomicSemanticFact,
    related_memory_accesses: &[&MemoryAccessFact],
    consumption: Option<&Aarch64ProofObligationConsumption>,
) -> String {
    let rejection = fact
        .proof_grade_rejection_reason()
        .unwrap_or_else(|| "AArch64 atomic semantic fact has no proof consumer".to_string());
    let evidence_hash =
        aarch64_atomic_obligation_evidence_hash(record, fact, related_memory_accesses, consumption);
    let evidence_id =
        aarch64_atomic_obligation_evidence_id(record, fact, related_memory_accesses, consumption);
    let instruction_digest = fact
        .origin
        .as_ref()
        .map(aarch64_instruction_provenance_digest)
        .unwrap_or_else(|| stable_sha256_hex(b"missing-aarch64-atomic-origin"));
    let record_digest = aarch64_unsupported_record_digest(record);
    let fact_digest = aarch64_atomic_fact_digest(fact);
    let memory_accesses_digest = aarch64_memory_accesses_digest(related_memory_accesses);
    let consumption_digest = aarch64_atomic_consumption_digest(consumption);
    let mut detail = format!(
        "{}; evidence_schema={AARCH64_ATOMIC_OBLIGATION_EVIDENCE_SCHEMA}; evidence_id={evidence_id}; artifact_digest=sha256:{evidence_hash}; instruction_provenance_digest=sha256:{instruction_digest}; unsupported_record_digest=sha256:{record_digest}; semantic_fact_digest=sha256:{fact_digest}; memory_access_facts_digest=sha256:{memory_accesses_digest}; proof_consumer_digest=sha256:{consumption_digest}; {}; {}; access={:?}; ordering={:?}; exclusive_monitor={:?}; reports_status={}",
        unsupported_record_detail(record),
        rejection,
        aarch64_atomic_fact_proof_obligation(fact),
        fact.access,
        fact.ordering,
        fact.exclusive_monitor,
        fact.reports_status
    );

    if let Some(consumption) = consumption {
        detail.push_str(&format!(
            "; vcgen proof consumer status={}; consumed_witnesses=[{}]; missing_witnesses=[{}]; {}",
            if consumption.accepted_for_proof_grade { "accepted" } else { "fail-closed" },
            aarch64_witness_list(&consumption.consumed_witnesses),
            aarch64_witness_list(&consumption.missing_witnesses),
            consumption.diagnostic
        ));
    }

    detail
}

fn aarch64_atomic_obligation_evidence_hash(
    record: &UnsupportedRecord,
    fact: &Aarch64AtomicSemanticFact,
    related_memory_accesses: &[&MemoryAccessFact],
    consumption: Option<&Aarch64ProofObligationConsumption>,
) -> String {
    stable_sha256_hex(
        format!(
            "schema={AARCH64_ATOMIC_OBLIGATION_EVIDENCE_SCHEMA}\n\
             record_digest=sha256:{}\n\
             semantic_fact_digest=sha256:{}\n\
             memory_access_facts_digest=sha256:{}\n\
             proof_consumer_digest=sha256:{}\n\
             instruction_provenance_digest=sha256:{}",
            aarch64_unsupported_record_digest(record),
            aarch64_atomic_fact_digest(fact),
            aarch64_memory_accesses_digest(related_memory_accesses),
            aarch64_atomic_consumption_digest(consumption),
            fact.origin
                .as_ref()
                .map(aarch64_instruction_provenance_digest)
                .unwrap_or_else(|| stable_sha256_hex(b"missing-aarch64-atomic-origin")),
        )
        .as_bytes(),
    )
}

fn aarch64_atomic_obligation_evidence_id(
    record: &UnsupportedRecord,
    fact: &Aarch64AtomicSemanticFact,
    related_memory_accesses: &[&MemoryAccessFact],
    consumption: Option<&Aarch64ProofObligationConsumption>,
) -> String {
    format!(
        "{AARCH64_ATOMIC_OBLIGATION_EVIDENCE_ID_PREFIX}{}",
        aarch64_atomic_obligation_evidence_hash(record, fact, related_memory_accesses, consumption)
    )
}

fn aarch64_related_memory_accesses<'a>(
    record: &UnsupportedRecord,
    memory_accesses: &'a [MemoryAccessFact],
) -> Vec<&'a MemoryAccessFact> {
    let Some(origin) = &record.origin else {
        return Vec::new();
    };
    memory_accesses
        .iter()
        .filter(|access| aarch64_binary_origins_match(&access.origin, origin))
        .collect()
}

fn aarch64_binary_origins_match(left: &BinaryOrigin, right: &BinaryOrigin) -> bool {
    left.function_entry == right.function_entry
        && left.instruction_address == right.instruction_address
        && left.instruction_size == right.instruction_size
        && left.encoding == right.encoding
        && left.instruction_bytes == right.instruction_bytes
}

fn aarch64_memory_accesses_digest(accesses: &[&MemoryAccessFact]) -> String {
    stable_sha256_hex(aarch64_memory_accesses_material(accesses).as_bytes())
}

fn aarch64_memory_accesses_material(accesses: &[&MemoryAccessFact]) -> String {
    let mut facts =
        accesses.iter().map(|access| aarch64_memory_access_material(access)).collect::<Vec<_>>();
    facts.sort();
    format!("memory_access_count={};facts=[{}]", facts.len(), facts.join("|"))
}

fn aarch64_unsupported_record_digest(record: &UnsupportedRecord) -> String {
    stable_sha256_hex(aarch64_unsupported_record_material(record).as_bytes())
}

fn aarch64_unsupported_record_material(record: &UnsupportedRecord) -> String {
    format!(
        "stage={};architecture={};origin={};opcode={};operand={};feature={}",
        record.stage,
        record.architecture.as_deref().unwrap_or("<none>"),
        record
            .origin
            .as_ref()
            .map(aarch64_binary_origin_material)
            .unwrap_or_else(|| "<none>".to_string()),
        record.opcode.as_deref().unwrap_or("<none>"),
        record.operand.as_deref().unwrap_or("<none>"),
        record.feature,
    )
}

fn aarch64_atomic_fact_digest(fact: &Aarch64AtomicSemanticFact) -> String {
    stable_sha256_hex(aarch64_atomic_fact_material(fact).as_bytes())
}

fn aarch64_atomic_fact_material(fact: &Aarch64AtomicSemanticFact) -> String {
    let mut missing = fact.missing_witnesses.clone();
    missing.sort();
    format!(
        "origin={};opcode={};operand={};access={:?};ordering={:?};exclusive_monitor={:?};reports_status={};missing_witnesses=[{}];consumed_by_proof_model={}",
        fact.origin
            .as_ref()
            .map(aarch64_binary_origin_material)
            .unwrap_or_else(|| "<none>".to_string()),
        fact.opcode,
        fact.operand.as_deref().unwrap_or("<none>"),
        fact.access,
        fact.ordering,
        fact.exclusive_monitor,
        fact.reports_status,
        missing.join(","),
        fact.consumed_by_proof_model,
    )
}

fn aarch64_atomic_consumption_digest(
    consumption: Option<&Aarch64ProofObligationConsumption>,
) -> String {
    stable_sha256_hex(aarch64_atomic_consumption_material(consumption).as_bytes())
}

fn aarch64_atomic_consumption_material(
    consumption: Option<&Aarch64ProofObligationConsumption>,
) -> String {
    let Some(consumption) = consumption else {
        return "proof_consumer=<absent>".to_string();
    };
    let mut consumed = consumption.consumed_witnesses.clone();
    let mut missing = consumption.missing_witnesses.clone();
    consumed.sort();
    missing.sort();
    format!(
        "accepted_for_proof_grade={};consumed_witnesses=[{}];missing_witnesses=[{}];diagnostic={}",
        consumption.accepted_for_proof_grade,
        consumed.join(","),
        missing.join(","),
        consumption.diagnostic,
    )
}

fn aarch64_atomic_fact_proof_obligation(fact: &Aarch64AtomicSemanticFact) -> &'static str {
    match (fact.ordering, fact.exclusive_monitor) {
        (MemoryOrderingSemantics::Acquire, Aarch64ExclusiveMonitorSemantics::None) => {
            "proof obligation: consume AArch64 acquire ordering event, synchronization edge, thread identity, and happens-before witness before this LDAR-style access can be proof-grade"
        }
        (MemoryOrderingSemantics::Release, Aarch64ExclusiveMonitorSemantics::None) => {
            "proof obligation: consume AArch64 release ordering event, synchronization edge, thread identity, and happens-before witness before this STLR-style access can be proof-grade"
        }
        (_, Aarch64ExclusiveMonitorSemantics::LoadReserve)
        | (_, Aarch64ExclusiveMonitorSemantics::StoreConditional) => {
            "unsupported proof obligation: exclusive-monitor reservation, invalidation, thread identity, and status semantics are not proof-consumed; exclusive forms remain fail-closed"
        }
        (MemoryOrderingSemantics::Relaxed, Aarch64ExclusiveMonitorSemantics::None) => {
            "proof obligation: consume atomic access identity before this relaxed access can be proof-grade"
        }
        (MemoryOrderingSemantics::AcquireRelease, Aarch64ExclusiveMonitorSemantics::None) => {
            "proof obligation: consume AArch64 acquire-release ordering event, synchronization edge, thread identity, and happens-before witness before this access can be proof-grade"
        }
        (MemoryOrderingSemantics::SeqCst, Aarch64ExclusiveMonitorSemantics::None) => {
            "proof obligation: consume AArch64 sequentially-consistent ordering event, synchronization edge, thread identity, and happens-before witness before this access can be proof-grade"
        }
        (MemoryOrderingSemantics::Unknown, _) => {
            "unsupported proof obligation: atomic ordering or exclusive-monitor semantics are unknown and must remain fail-closed"
        }
        _ => {
            "unsupported proof obligation: unrecognized AArch64 atomic semantics are not proof-consumed and must remain fail-closed"
        }
    }
}

fn aarch64_witness_list(witnesses: &[String]) -> String {
    if witnesses.is_empty() { "none".to_string() } else { witnesses.join(", ") }
}

fn aarch64_atomic_consumption_by_record(
    lifted: &LiftedFunction,
) -> BTreeMap<usize, Aarch64ProofObligationConsumption> {
    let facts = lifted
        .unsupported
        .records
        .iter()
        .enumerate()
        .filter_map(|(record_index, record)| {
            record.aarch64_atomic_semantic_fact().map(|fact| Aarch64LedgerFact {
                record_index,
                fact,
                location: aarch64_fact_location(record),
            })
        })
        .collect::<Vec<_>>();

    let mut consumed = BTreeMap::new();
    let mut paired = BTreeSet::new();

    for release in facts.iter().filter(|candidate| aarch64_is_plain_release(&candidate.fact)) {
        if paired.contains(&release.record_index) {
            continue;
        }
        let Some(acquire) = facts.iter().find(|candidate| {
            !paired.contains(&candidate.record_index)
                && candidate.record_index > release.record_index
                && candidate.location == release.location
                && aarch64_is_plain_acquire(&candidate.fact)
        }) else {
            continue;
        };

        let consumption = consume_generated_aarch64_release_acquire(release, acquire);
        consumed.insert(release.record_index, consumption.clone());
        consumed.insert(acquire.record_index, consumption);
        paired.insert(release.record_index);
        paired.insert(acquire.record_index);
    }

    for load_reserve in facts.iter().filter(|candidate| {
        candidate.fact.exclusive_monitor == Aarch64ExclusiveMonitorSemantics::LoadReserve
    }) {
        if paired.contains(&load_reserve.record_index) {
            continue;
        }
        let Some(store_conditional) = facts.iter().find(|candidate| {
            !paired.contains(&candidate.record_index)
                && candidate.record_index > load_reserve.record_index
                && candidate.location == load_reserve.location
                && candidate.fact.exclusive_monitor
                    == Aarch64ExclusiveMonitorSemantics::StoreConditional
        }) else {
            continue;
        };

        let consumption =
            consume_generated_aarch64_exclusive_monitor(load_reserve, store_conditional);
        consumed.insert(load_reserve.record_index, consumption.clone());
        consumed.insert(store_conditional.record_index, consumption);
        paired.insert(load_reserve.record_index);
        paired.insert(store_conditional.record_index);
    }

    for fact in facts {
        consumed
            .entry(fact.record_index)
            .or_insert_with(|| unpaired_aarch64_atomic_consumption(&fact.fact));
    }

    consumed
}

#[derive(Debug)]
struct Aarch64LedgerFact {
    record_index: usize,
    fact: Aarch64AtomicSemanticFact,
    location: String,
}

fn consume_generated_aarch64_release_acquire(
    release: &Aarch64LedgerFact,
    acquire: &Aarch64LedgerFact,
) -> Aarch64ProofObligationConsumption {
    let mut log = AtomicAccessLog::new();
    let release_idx = log.record(aarch64_atomic_access_entry(release, aarch64_thread_id_unknown()));
    let acquire_idx = log.record(aarch64_atomic_access_entry(acquire, aarch64_thread_id_unknown()));

    let checker = MemoryModelChecker::new(log, HappensBefore::new(2));
    checker.consume_aarch64_release_acquire_obligation(
        &release.fact,
        &acquire.fact,
        Aarch64ReleaseAcquireWitness {
            release_access_index: release_idx,
            acquire_access_index: acquire_idx,
        },
    )
}

fn consume_generated_aarch64_exclusive_monitor(
    load_reserve: &Aarch64LedgerFact,
    store_conditional: &Aarch64LedgerFact,
) -> Aarch64ProofObligationConsumption {
    let mut log = AtomicAccessLog::new();
    let thread = "binary-current-thread";
    let load_idx = log.record(aarch64_atomic_access_entry(load_reserve, thread));
    let store_idx = log.record(aarch64_atomic_access_entry(store_conditional, thread));

    let mut hb = HappensBefore::new(2);
    hb.add_edge(load_idx, store_idx);

    let checker = MemoryModelChecker::new(log, hb);
    checker.consume_aarch64_exclusive_monitor_obligation(
        &load_reserve.fact,
        &store_conditional.fact,
        Aarch64ExclusiveMonitorWitness {
            load_reserve_access_index: load_idx,
            store_conditional_access_index: store_idx,
            reservation_observed: false,
            no_intervening_invalidation: false,
            store_status: None,
        },
    )
}

fn unpaired_aarch64_atomic_consumption(
    fact: &Aarch64AtomicSemanticFact,
) -> Aarch64ProofObligationConsumption {
    let mut missing = fact.missing_witnesses.iter().cloned().collect::<BTreeSet<_>>();
    match fact.exclusive_monitor {
        Aarch64ExclusiveMonitorSemantics::None if aarch64_is_plain_release(fact) => {
            missing.insert("matching acquire fact".to_string());
        }
        Aarch64ExclusiveMonitorSemantics::None if aarch64_is_plain_acquire(fact) => {
            missing.insert("matching release fact".to_string());
        }
        Aarch64ExclusiveMonitorSemantics::LoadReserve => {
            missing.insert("matching store-conditional fact".to_string());
        }
        Aarch64ExclusiveMonitorSemantics::StoreConditional => {
            missing.insert("matching load-reserve fact".to_string());
        }
        _ => {
            missing.insert("recognized AArch64 atomic proof-consumer shape".to_string());
        }
    }

    let missing = missing.into_iter().collect::<Vec<_>>();
    Aarch64ProofObligationConsumption {
        accepted_for_proof_grade: false,
        consumed_witnesses: Vec::new(),
        missing_witnesses: missing.clone(),
        diagnostic: format!(
            "AArch64 generated VC proof consumer remains fail-closed; missing witnesses: {}",
            aarch64_witness_list(&missing)
        ),
    }
}

fn aarch64_atomic_access_entry(fact: &Aarch64LedgerFact, thread_id: &str) -> AtomicAccessEntry {
    AtomicAccessEntry {
        location: fact.location.clone(),
        access_kind: match fact.fact.access {
            MemoryAccessKind::Read => {
                AccessKind::AtomicRead(aarch64_memory_ordering(fact.fact.ordering))
            }
            MemoryAccessKind::Write => {
                AccessKind::AtomicWrite(aarch64_memory_ordering(fact.fact.ordering))
            }
            _ => AccessKind::AtomicRead(MemoryOrdering::Relaxed),
        },
        thread_id: thread_id.to_string(),
        span: fact
            .fact
            .origin
            .as_ref()
            .map_or_else(SourceSpan::default, trust_types::BinaryOrigin::span),
    }
}

fn aarch64_fact_location(record: &UnsupportedRecord) -> String {
    record
        .operand
        .as_ref()
        .filter(|operand| !operand.trim().is_empty())
        .cloned()
        .or_else(|| {
            record
                .origin
                .as_ref()
                .map(|origin| format!("binary:0x{:x}", origin.instruction_address))
        })
        .unwrap_or_else(|| "unknown-aarch64-atomic-location".to_string())
}

fn aarch64_memory_ordering(ordering: MemoryOrderingSemantics) -> MemoryOrdering {
    match ordering {
        MemoryOrderingSemantics::Relaxed => MemoryOrdering::Relaxed,
        MemoryOrderingSemantics::Acquire => MemoryOrdering::Acquire,
        MemoryOrderingSemantics::Release => MemoryOrdering::Release,
        MemoryOrderingSemantics::AcquireRelease => MemoryOrdering::AcqRel,
        MemoryOrderingSemantics::SeqCst => MemoryOrdering::SeqCst,
        MemoryOrderingSemantics::Unknown => MemoryOrdering::Relaxed,
        _ => MemoryOrdering::Relaxed,
    }
}

fn aarch64_is_plain_release(fact: &Aarch64AtomicSemanticFact) -> bool {
    fact.access == MemoryAccessKind::Write
        && fact.exclusive_monitor == Aarch64ExclusiveMonitorSemantics::None
        && matches!(
            fact.ordering,
            MemoryOrderingSemantics::Release
                | MemoryOrderingSemantics::AcquireRelease
                | MemoryOrderingSemantics::SeqCst
        )
}

fn aarch64_is_plain_acquire(fact: &Aarch64AtomicSemanticFact) -> bool {
    fact.access == MemoryAccessKind::Read
        && fact.exclusive_monitor == Aarch64ExclusiveMonitorSemantics::None
        && matches!(
            fact.ordering,
            MemoryOrderingSemantics::Acquire
                | MemoryOrderingSemantics::AcquireRelease
                | MemoryOrderingSemantics::SeqCst
        )
}

fn aarch64_thread_id_unknown() -> &'static str {
    ""
}

fn unsupported_record_is_memory(record: &UnsupportedRecord) -> bool {
    record.stage.contains("memory") || record.feature.contains("memory")
}

fn unsupported_record_kind(record: &UnsupportedRecord) -> String {
    match record.stage.as_str() {
        "trust-lift::source-provenance" => "BinarySourceProvenance".to_string(),
        "trust-lift::abi-provenance" => "BinaryAbiProvenance".to_string(),
        "trust-lift::type-provenance" => "BinaryTypeProvenance".to_string(),
        "trust-lift::semantic-lift" => "BinaryInstructionSemantics".to_string(),
        "trust-lift::effect-lift" => "BinaryInstructionEffect".to_string(),
        _ => "UnsupportedBinaryFeature".to_string(),
    }
}

fn unsupported_record_detail(record: &UnsupportedRecord) -> String {
    let mut parts = vec![format!("stage={}", record.stage), format!("feature={}", record.feature)];
    if let Some(architecture) = &record.architecture {
        parts.push(format!("arch={architecture}"));
    }
    if let Some(opcode) = &record.opcode {
        parts.push(format!("opcode={opcode}"));
    }
    if let Some(operand) = &record.operand {
        parts.push(format!("operand={operand}"));
    }
    if let Some(origin) = &record.origin {
        parts.push(format!("address=0x{:x}", origin.instruction_address));
    }

    parts.join("; ")
}

/// Generate binary VCs with proof-grade ABI/storage metadata checks.
#[must_use]
pub fn generate_binary_vcs_with_metadata(
    lifted: &LiftedFunction,
    abi_facts: &[BinaryAbiFact],
    storage_facts: &[BinaryStorageFact],
) -> Vec<VerificationCondition> {
    let mut vcs = generate_binary_vcs(lifted);
    vcs.extend(generate_binary_abi_contradiction_vcs(
        &lifted.name,
        SourceSpan::binary_address(lifted.entry_point),
        abi_facts,
        storage_facts,
    ));
    vcs
}

/// Generate fail-closed bad-state VCs for proof-grade ABI/storage contradictions.
///
/// Unknown, assumption-backed, heuristic, and non-proof-grade facts are ignored:
/// they are not strong enough to prove a binary ABI contradiction. When two
/// proof-grade facts disagree about a parameter or return storage location, the
/// contradiction itself is a proof obligation and the formula is unconditionally
/// true so the bad state cannot be optimized away.
#[must_use]
pub fn generate_binary_abi_contradiction_vcs(
    func_name: &str,
    fallback_location: SourceSpan,
    abi_facts: &[BinaryAbiFact],
    storage_facts: &[BinaryStorageFact],
) -> Vec<VerificationCondition> {
    let proof_grade_storage: Vec<_> =
        storage_facts.iter().filter(|fact| proof_grade_storage_fact(fact)).collect();
    let mut vcs = Vec::new();

    for abi_fact in abi_facts.iter().filter(|fact| proof_grade_abi_fact(fact)) {
        let Some((subject, abi_location, role, index)) = abi_storage_claim(abi_fact) else {
            continue;
        };

        for storage_fact in
            proof_grade_storage.iter().filter(|storage_fact| &storage_fact.subject == subject)
        {
            if storage_fact.location == *abi_location {
                continue;
            }

            let fact = format!(
                "{} {} storage for `{}`",
                role,
                index,
                binary_fact_subject_function(subject).unwrap_or(func_name)
            );
            let evidence = format!(
                "ABI fact location {} conflicts with storage fact location {}; ABI evidence={}, storage evidence={}",
                storage_location_label(abi_location),
                storage_location_label(&storage_fact.location),
                fact_evidence_label(&abi_fact.evidence),
                fact_evidence_label(&storage_fact.evidence)
            );

            vcs.push(VerificationCondition {
                kind: VcKind::BinaryAbiContradiction { fact, evidence },
                function: func_name.to_string().into(),
                location: abi_fact
                    .origin
                    .as_ref()
                    .or(storage_fact.origin.as_ref())
                    .map_or_else(|| fallback_location.clone(), trust_types::BinaryOrigin::span),
                formula: Formula::Bool(true),
                contract_metadata: None,
            });
        }
    }

    vcs
}

fn abi_storage_claim(
    fact: &BinaryAbiFact,
) -> Option<(&BinaryFactSubject, &BinaryStorageLocation, &'static str, usize)> {
    match &fact.kind {
        BinaryAbiFactKind::Parameter { index, location } => {
            Some((&fact.subject, location, "parameter", *index))
        }
        BinaryAbiFactKind::Return { index, location } => {
            Some((&fact.subject, location, "return", *index))
        }
        _ => None,
    }
}

fn proof_grade_abi_fact(fact: &BinaryAbiFact) -> bool {
    proof_grade_fact(fact.trust_level, fact.confidence, &fact.evidence, fact.assumptions.is_empty())
}

fn proof_grade_storage_fact(fact: &BinaryStorageFact) -> bool {
    proof_grade_fact(fact.trust_level, fact.confidence, &fact.evidence, fact.assumptions.is_empty())
}

fn proof_grade_fact(
    trust_level: TrustLevel,
    confidence: BinaryFactConfidence,
    evidence: &BinaryFactEvidence,
    no_assumptions: bool,
) -> bool {
    trust_level == TrustLevel::ProofGrade
        && no_assumptions
        && !matches!(confidence, BinaryFactConfidence::Assumed | BinaryFactConfidence::Unknown)
        && !matches!(
            evidence,
            BinaryFactEvidence::Assumption
                | BinaryFactEvidence::Heuristic { .. }
                | BinaryFactEvidence::Unknown
        )
}

fn binary_fact_subject_function(subject: &BinaryFactSubject) -> Option<&str> {
    match subject {
        BinaryFactSubject::Function { name, .. }
        | BinaryFactSubject::Parameter { function: name, .. }
        | BinaryFactSubject::ReturnValue { function: name, .. }
        | BinaryFactSubject::Local { function: name, .. }
        | BinaryFactSubject::Register { function: name, .. } => Some(name.as_str()),
        _ => None,
    }
}

fn storage_location_label(location: &BinaryStorageLocation) -> String {
    match location {
        BinaryStorageLocation::Register { name, bit_width } => match bit_width {
            Some(width) => format!("register {name}:{width}"),
            None => format!("register {name}"),
        },
        BinaryStorageLocation::RegisterPair { high, low, bit_width } => match bit_width {
            Some(width) => format!("register pair {high}:{low}:{width}"),
            None => format!("register pair {high}:{low}"),
        },
        BinaryStorageLocation::Stack { base, offset, size_bytes } => match size_bytes {
            Some(size) => format!("stack {base:?}{offset:+} ({size} bytes)"),
            None => format!("stack {base:?}{offset:+}"),
        },
        BinaryStorageLocation::Memory { size_bytes, .. } => match size_bytes {
            Some(size) => format!("memory ({size} bytes)"),
            None => "memory".to_string(),
        },
        BinaryStorageLocation::Global { name, address, size_bytes } => {
            format!("global name={name:?} address={address:?} size={size_bytes:?}")
        }
        BinaryStorageLocation::Immediate { value, width_bits } => {
            format!("immediate {value}:{width_bits}")
        }
        BinaryStorageLocation::Split(parts) => format!("split({} parts)", parts.len()),
        BinaryStorageLocation::Unknown => "unknown".to_string(),
        _ => "future-storage-location".to_string(),
    }
}

fn fact_evidence_label(evidence: &BinaryFactEvidence) -> String {
    match evidence {
        BinaryFactEvidence::DebugInfo => "debug-info".to_string(),
        BinaryFactEvidence::AbiDefault => "abi-default".to_string(),
        BinaryFactEvidence::SymbolMetadata => "symbol-metadata".to_string(),
        BinaryFactEvidence::RegisterUse => "register-use".to_string(),
        BinaryFactEvidence::StackUse => "stack-use".to_string(),
        BinaryFactEvidence::DataFlow => "data-flow".to_string(),
        BinaryFactEvidence::LibrarySummary => "library-summary".to_string(),
        BinaryFactEvidence::UserProvided => "user-provided".to_string(),
        BinaryFactEvidence::Validation => "validation".to_string(),
        BinaryFactEvidence::Assumption => "assumption".to_string(),
        BinaryFactEvidence::Heuristic { reason } => format!("heuristic:{reason}"),
        BinaryFactEvidence::Unknown => "unknown".to_string(),
        _ => "future-evidence".to_string(),
    }
}

fn detect_memory_local(lifted: &LiftedFunction) -> Option<usize> {
    memory_local_from_store_formula(lifted)
        .or_else(|| memory_local_from_decl_name(lifted))
        .or_else(|| memory_local_from_known_layout(lifted))
}

fn memory_local_from_store_formula(lifted: &LiftedFunction) -> Option<usize> {
    lifted.trust_ir_body.blocks.iter().flat_map(|block| block.stmts.iter()).find_map(|stmt| {
        let Statement::Assign { place, rvalue, .. } = stmt else {
            return None;
        };

        rvalue_stores_to_mem(rvalue).then_some(place.local)
    })
}

fn memory_local_from_decl_name(lifted: &LiftedFunction) -> Option<usize> {
    lifted
        .trust_ir_body
        .locals
        .iter()
        .find_map(|local| (local.name.as_deref() == Some("MEM")).then_some(local.index))
}

fn memory_local_from_known_layout(lifted: &LiftedFunction) -> Option<usize> {
    let x86_64 = LocalLayout::x86_64();
    if known_layout_matches(lifted, &x86_64, &[(1, "RAX"), (2, "RCX"), (19, "CF"), (20, "ZF")]) {
        return Some(x86_64.mem_local);
    }

    let aarch64 = LocalLayout::aarch64();
    if known_layout_matches(lifted, &aarch64, &[(1, "X0"), (2, "X1"), (34, "N"), (35, "Z")]) {
        return Some(aarch64.mem_local);
    }

    None
}

fn known_layout_matches(
    lifted: &LiftedFunction,
    layout: &LocalLayout,
    named_anchors: &[(usize, &str)],
) -> bool {
    let locals = &lifted.trust_ir_body.locals;
    has_local_index(locals, layout.mem_local)
        && (named_anchors.iter().any(|(index, name)| has_local_name(locals, *index, name))
            || has_exact_dense_layout(locals, layout.total))
}

fn has_local_index(locals: &[trust_types::LocalDecl], index: usize) -> bool {
    locals.iter().any(|local| local.index == index)
}

fn has_local_name(locals: &[trust_types::LocalDecl], index: usize, name: &str) -> bool {
    locals.iter().any(|local| local.index == index && local.name.as_deref() == Some(name))
}

fn has_exact_dense_layout(locals: &[trust_types::LocalDecl], total: usize) -> bool {
    locals.iter().map(|local| local.index).max() == Some(total - 1)
        && (0..total).all(|index| has_local_index(locals, index))
}

fn rvalue_stores_to_mem(rvalue: &Rvalue) -> bool {
    matches!(rvalue, Rvalue::Use(Operand::Symbolic(formula)) if formula_stores_to_mem(formula))
}

fn formula_stores_to_mem(formula: &Formula) -> bool {
    memory_store_address_formula(formula).is_some()
}

fn memory_store_address(rvalue: &Rvalue) -> Option<Formula> {
    let Rvalue::Use(Operand::Symbolic(formula)) = rvalue else {
        return None;
    };

    memory_store_address_formula(formula)
}

fn memory_read_address(rvalue: &Rvalue) -> Option<Formula> {
    match rvalue {
        Rvalue::Use(Operand::Symbolic(formula)) => memory_read_address_formula(formula),
        Rvalue::Use(Operand::Copy(place) | Operand::Move(place))
            if place
                .projections
                .iter()
                .any(|projection| matches!(projection, Projection::Deref)) =>
        {
            Some(Formula::Var(
                generated_lift_symbol(&format!("load_addr_local{}", place.local)),
                Sort::BitVec(64),
            ))
        }
        _ => None,
    }
}

fn memory_read_address_formula(formula: &Formula) -> Option<Formula> {
    match formula {
        Formula::Select(base, address) if formula_is_mem_array(base) => {
            Some(address.as_ref().clone())
        }
        _ => None,
    }
}

fn memory_store_address_formula(formula: &Formula) -> Option<Formula> {
    match formula {
        Formula::Store(base, address, _) if formula_is_mem_array(base) => {
            Some(address.as_ref().clone())
        }
        _ => None,
    }
}

fn formula_is_mem_array(formula: &Formula) -> bool {
    match formula {
        Formula::Store(base, _, _) => formula_is_mem_array(base),
        _ => {
            formula.var_name() == Some("MEM")
                && matches!(formula.var_sort(), Some(Sort::Array(_, _)))
        }
    }
}

fn detect_sp_local(lifted: &LiftedFunction) -> Option<usize> {
    sp_local_from_decl_name(lifted).or_else(|| sp_local_from_known_layout(lifted))
}

fn sp_local_from_decl_name(lifted: &LiftedFunction) -> Option<usize> {
    lifted
        .trust_ir_body
        .locals
        .iter()
        .find_map(|local| (local.name.as_deref() == Some("SP")).then_some(local.index))
}

fn sp_local_from_known_layout(lifted: &LiftedFunction) -> Option<usize> {
    let x86_64 = LocalLayout::x86_64();
    if known_layout_matches(lifted, &x86_64, &[(1, "RAX"), (2, "RCX"), (19, "CF"), (20, "ZF")]) {
        return Some(x86_64.sp_local);
    }

    let aarch64 = LocalLayout::aarch64();
    if known_layout_matches(lifted, &aarch64, &[(1, "X0"), (2, "X1"), (34, "N"), (35, "Z")]) {
        return Some(aarch64.sp_local);
    }

    None
}

fn latest_sp_assignment_in_block(
    block: &trust_types::BasicBlock,
    sp_local_index: usize,
) -> Option<(Formula, SourceSpan)> {
    block.stmts.iter().rev().find_map(|stmt| {
        let Statement::Assign { place, rvalue, span } = stmt else {
            return None;
        };
        (place.local == sp_local_index)
            .then(|| lifted_rvalue_formula(rvalue).map(|formula| (formula, span.clone())))
            .flatten()
    })
}

fn lifted_rvalue_formula(rvalue: &Rvalue) -> Option<Formula> {
    let Rvalue::Use(operand) = rvalue else {
        return None;
    };

    lifted_operand_formula(operand)
}

fn lifted_operand_formula(operand: &Operand) -> Option<Formula> {
    match operand {
        Operand::Symbolic(formula) => Some(formula.clone()),
        Operand::Constant(value) => Some(const_value_to_formula(value)),
        Operand::Copy(_) | Operand::Move(_) => None,
        _ => None,
    }
}

fn const_value_to_formula(value: &ConstValue) -> Formula {
    match value {
        ConstValue::Bool(value) => Formula::Bool(*value),
        ConstValue::Int(value) => Formula::Int(*value),
        ConstValue::Uint(value, width) => match i128::try_from(*value) {
            Ok(value) => Formula::BitVec { value, width: *width },
            Err(_) => Formula::UInt(*value),
        },
        ConstValue::Float(value) => {
            Formula::Var(generated_lift_symbol(&format!("float_{value}")), Sort::BitVec(64))
        }
        ConstValue::Unit => Formula::Int(0),
        ConstValue::CallableItem { def_path, kind, def_path_hash } => Formula::var_owned(
            ConstValue::callable_smt_var_name(def_path, *kind, *def_path_hash),
            Sort::Int,
        ),
        // opaque, injectively-named term for a `&str` literal.
        ConstValue::Str { bytes } => Formula::Var(ConstValue::str_smt_var_name(bytes), Sort::Int),
        _ => Formula::Var(generated_lift_symbol("unknown_constant"), Sort::Int),
    }
}

fn stack_pointer_mismatch_formula(
    block: &trust_types::BasicBlock,
    sp_local_index: Option<usize>,
) -> Formula {
    let entry_sp = Formula::Var("SP".into(), Sort::BitVec(64));
    let return_sp = sp_local_index
        .and_then(|sp_local| latest_sp_assignment_in_block(block, sp_local))
        .map(|(formula, _)| formula)
        .unwrap_or_else(|| {
            // Return terminators do not currently carry an SP operand, and lifted
            // TrustIr has no cross-block SP SSA value. This fallback remains
            // path-insensitive but is tied to the return block and source span.
            Formula::Var(
                generated_lift_symbol(&format!("return_sp_bb{}", block.id.0)),
                Sort::BitVec(64),
            )
        });

    Formula::Not(Box::new(Formula::Eq(Box::new(return_sp), Box::new(entry_sp))))
}

fn return_source_span(
    lifted: &LiftedFunction,
    block: &trust_types::BasicBlock,
    sp_local_index: Option<usize>,
) -> SourceSpan {
    block_return_instruction_span(lifted, block.id.0)
        .or_else(|| {
            sp_local_index.and_then(|sp_local| {
                latest_sp_assignment_in_block(block, sp_local).map(|(_, span)| span)
            })
        })
        .or_else(|| block.stmts.last().and_then(statement_span))
        .or_else(|| block_start_span(lifted, block.id.0))
        .unwrap_or_else(|| SourceSpan {
            file: format!("binary:0x{:x}", lifted.entry_point),
            line_start: 0,
            col_start: 0,
            line_end: 0,
            col_end: 0,
        })
}

fn block_return_instruction_span(lifted: &LiftedFunction, block_id: usize) -> Option<SourceSpan> {
    let cfg_block = lifted.cfg.blocks.iter().find(|block| block.id == block_id)?;
    let address = cfg_block.instructions.last()?.address;

    Some(SourceSpan {
        file: format!("binary:0x{address:x}"),
        line_start: 0,
        col_start: 0,
        line_end: 0,
        col_end: 0,
    })
}

fn block_start_span(lifted: &LiftedFunction, block_id: usize) -> Option<SourceSpan> {
    let cfg_block = lifted.cfg.blocks.iter().find(|block| block.id == block_id)?;
    let address = cfg_block.start_addr;

    Some(SourceSpan {
        file: format!("binary:0x{address:x}"),
        line_start: 0,
        col_start: 0,
        line_end: 0,
        col_end: 0,
    })
}

fn statement_span(stmt: &Statement) -> Option<SourceSpan> {
    match stmt {
        Statement::Assign { span, .. } => Some(span.clone()),
        _ => None,
    }
}

/// Generate memory model VCs for lifted binary code.
///
/// These VCs are specific to binary analysis (not present in source-level MIR):
/// - **Memory read validity**: Every memory read accesses a previously written
///   or argument-initialized address (no reading uninitialized memory).
/// - **Stack discipline**: SP decrements on function entry and is restored on exit.
/// - **No out-of-bounds memory access**: Memory accesses within known bounds.
///
/// Each VC's formula uses the array theory (Select/Store) to model memory as a
/// flat byte-addressable array, matching trust-machine-sem's memory model.
///
/// Memory-write VCs are emitted only for lifted `Store(MEM, address, value)`
/// formulas so the OOB check uses the real access address. Stack-discipline VCs
/// use the last lifted SP assignment in the return block when one exists; if no
/// same-block SP assignment is available, the fallback is still path-insensitive
/// because TrustIr return terminators do not carry a current SP operand.
#[must_use]
pub fn generate_memory_model_vcs(lifted: &LiftedFunction) -> Vec<VerificationCondition> {
    let mut vcs = Vec::new();
    let func_name = &lifted.name;
    let mem_local_index = detect_memory_local(lifted);
    let sp_local_index = detect_sp_local(lifted);
    let has_memory_access_trace = !lifted.memory_accesses.is_empty();

    if has_memory_access_trace {
        vcs.extend(lifted.memory_accesses.iter().map(|access| memory_access_vc(func_name, access)));
        vcs.extend(
            lifted
                .memory_accesses
                .iter()
                .filter_map(|access| saved_return_address_overwrite_access_vc(func_name, access)),
        );
    }

    // Scan TrustIr blocks for memory-related statements.
    for block in &lifted.trust_ir_body.blocks {
        for stmt in &block.stmts {
            if let Statement::Assign { place, rvalue, span } = stmt {
                if let Some(addr) = memory_read_address(rvalue) {
                    if has_memory_access_trace {
                        if !memory_access_fact_covers(
                            &lifted.memory_accesses,
                            MemoryAccessKind::Read,
                            span,
                            &addr,
                        ) {
                            vcs.push(missing_memory_read_fact_vc(
                                func_name, block.id.0, span, addr,
                            ));
                        }
                    } else {
                        vcs.push(missing_memory_read_fact_vc(func_name, block.id.0, span, addr));
                    }
                }

                // Detect writes to MEM local (memory store operations from the binary).
                if Some(place.local) == mem_local_index {
                    let Some(addr) = memory_store_address(rvalue) else {
                        continue;
                    };

                    if has_memory_access_trace {
                        if !memory_access_fact_covers(
                            &lifted.memory_accesses,
                            MemoryAccessKind::Write,
                            span,
                            &addr,
                        ) {
                            vcs.push(missing_memory_write_fact_vc(
                                func_name, block.id.0, span, addr,
                            ));
                        }
                    } else {
                        vcs.push(VerificationCondition {
                            kind: VcKind::Assertion {
                                message: format!(
                                    "binary memory write OOB in block bb{}",
                                    block.id.0,
                                ),
                            },
                            function: func_name.clone().into(),
                            location: span.clone(),
                            formula: memory_oob_formula(addr.clone()),
                            contract_metadata: None,
                        });
                        vcs.push(saved_return_address_overwrite_store_vc(
                            func_name, block.id.0, span, addr, 8,
                        ));
                    }
                }
            }
        }

        // Stack discipline: check that Return terminators restore SP.
        if matches!(block.terminator, Terminator::Return) {
            let sp_mismatch = stack_pointer_mismatch_formula(block, sp_local_index);

            vcs.push(VerificationCondition {
                kind: VcKind::Assertion {
                    message: format!(
                        "stack pointer not restored on return in block bb{}",
                        block.id.0,
                    ),
                },
                function: func_name.clone().into(),
                location: return_source_span(lifted, block, sp_local_index),
                formula: sp_mismatch,
                contract_metadata: None,
            });
        }

        if let Some(vc) = format_string_call_vc(func_name, lifted, block) {
            vcs.push(vc);
        }

        if let Some(vc) = copy_sink_length_call_vc(func_name, lifted, block) {
            vcs.push(vc);
        }
    }

    vcs
}

fn memory_access_fact_covers(
    accesses: &[MemoryAccessFact],
    kind: MemoryAccessKind,
    span: &SourceSpan,
    addr: &Formula,
) -> bool {
    accesses.iter().any(|access| {
        access.kind == kind && (access.address == *addr || access.origin.span().file == span.file)
    })
}

/// Generate fail-closed security VCs for unresolved binary control-flow targets.
///
/// The current lifted metadata can identify an unresolved strict CFG edge, but it
/// does not preserve a target taint label. Treat these as unconditional bad-state
/// VCs so indirect branch/call cases remain rejected or unknown instead of being
/// promoted as proof-grade evidence.
#[must_use]
pub fn generate_control_flow_vcs(lifted: &LiftedFunction) -> Vec<VerificationCondition> {
    let mut vcs = Vec::new();
    let mut cfg_unresolved_blocks = Vec::new();

    for block in &lifted.cfg.blocks {
        for edge in lifted.cfg.edges_for_block(block) {
            if !edge.kind.is_strict_control_flow() || edge.target != CfgEdgeTarget::Unresolved {
                continue;
            }

            let sink_kind = indirect_sink_kind(edge.kind);
            cfg_unresolved_blocks.push(block.id);
            vcs.push(VerificationCondition {
                kind: VcKind::TaintedIndirectBranch {
                    sink_kind: sink_kind.to_string(),
                    target: "unresolved_indirect_target".to_string(),
                    evidence: format!(
                        "CFG metadata has unresolved {sink_kind} at block bb{}; target taint unavailable",
                        block.id
                    ),
                },
                function: lifted.name.clone().into(),
                location: unresolved_edge_source_span(block),
                formula: Formula::Bool(true),
                contract_metadata: None,
            });
        }
    }

    for block in &lifted.trust_ir_body.blocks {
        let Terminator::Opaque { kind, targets, span } = &block.terminator else {
            continue;
        };
        if cfg_unresolved_blocks.contains(&block.id.0) {
            continue;
        }

        vcs.push(opaque_control_flow_vc(&lifted.name, block.id.0, kind, targets, span.clone()));
    }

    vcs
}

fn indirect_sink_kind(kind: CfgEdgeKind) -> &'static str {
    match kind {
        CfgEdgeKind::Call => "indirect_call",
        _ => "indirect_branch",
    }
}

fn unresolved_edge_source_span(block: &trust_lift::cfg::LiftedBlock) -> SourceSpan {
    let address = block.instructions.last().map_or(block.start_addr, |insn| insn.address);
    SourceSpan::binary_address(address)
}

fn opaque_control_flow_vc(
    func_name: &str,
    block_id: usize,
    kind: &str,
    targets: &[trust_types::BlockId],
    location: SourceSpan,
) -> VerificationCondition {
    VerificationCondition {
        kind: VcKind::TaintedIndirectBranch {
            sink_kind: "indirect_branch".to_string(),
            target: "unresolved_opaque_target".to_string(),
            evidence: format!(
                "opaque TrustIr control-flow terminator {kind} at block bb{block_id}; {} recovered target(s); target taint unavailable",
                targets.len()
            ),
        },
        function: func_name.to_string().into(),
        location,
        formula: Formula::Bool(true),
        contract_metadata: None,
    }
}

fn format_string_call_vc(
    func_name: &str,
    lifted: &LiftedFunction,
    block: &trust_types::BasicBlock,
) -> Option<VerificationCondition> {
    let Terminator::Call { func: callee, args, span, .. } = &block.terminator else {
        return None;
    };
    let short = callee.rsplit("::").next().unwrap_or(callee);
    let format_index = printf_family_format_index(short)?;
    let format_arg = args.get(format_index)?;
    let formula = format_operand_formula(format_arg, lifted);
    let evidence = unsafe_format_argument_evidence(&formula)?;

    Some(VerificationCondition {
        kind: VcKind::FormatStringViolation { callee: short.to_string(), evidence },
        function: func_name.to_string().into(),
        location: span.clone(),
        formula: Formula::Bool(true),
        contract_metadata: None,
    })
}

fn format_operand_formula(operand: &Operand, lifted: &LiftedFunction) -> Formula {
    match lifted_operand_formula(operand) {
        Some(formula) => formula,
        None => match operand {
            Operand::Copy(place) | Operand::Move(place) => {
                let name = lifted
                    .trust_ir_body
                    .locals
                    .iter()
                    .find(|local| local.index == place.local)
                    .and_then(|local| local.name.clone())
                    .unwrap_or_else(|| format!("_{}", place.local));
                Formula::Var(name, Sort::Int)
            }
            _ => Formula::Var(generated_lift_symbol("unknown_format_arg"), Sort::Int),
        },
    }
}

fn missing_memory_read_fact_vc(
    func_name: &str,
    block_id: usize,
    span: &SourceSpan,
    addr: Formula,
) -> VerificationCondition {
    missing_memory_access_fact_vc(func_name, block_id, span, addr, "read")
}

fn missing_memory_write_fact_vc(
    func_name: &str,
    block_id: usize,
    span: &SourceSpan,
    addr: Formula,
) -> VerificationCondition {
    missing_memory_access_fact_vc(func_name, block_id, span, addr, "write")
}

fn missing_memory_access_fact_vc(
    func_name: &str,
    block_id: usize,
    span: &SourceSpan,
    addr: Formula,
    access_kind: &str,
) -> VerificationCondition {
    VerificationCondition {
        kind: VcKind::Assertion {
            message: format!(
                "binary memory {access_kind} missing access fact in block bb{block_id}"
            ),
        },
        function: func_name.to_string().into(),
        location: span.clone(),
        formula: unknown_memory_region_formula(addr),
        contract_metadata: None,
    }
}

fn memory_oob_formula(addr: Formula) -> Formula {
    // VC convention is bad-state reachability: SAT means the access can be OOB.
    let stack_base = Formula::Var(generated_lift_symbol("stack_base"), Sort::BitVec(64));
    let stack_limit = Formula::Var(generated_lift_symbol("stack_limit"), Sort::BitVec(64));

    Formula::Or(vec![
        Formula::BvULt(Box::new(addr.clone()), Box::new(stack_base), 64),
        Formula::Not(Box::new(Formula::BvULt(Box::new(addr), Box::new(stack_limit), 64))),
    ])
}

fn unknown_memory_region_formula(_addr: Formula) -> Formula {
    // Without a recovered region/base/extent, a solver cannot prove the access
    // valid. Emit an unconditional bad-state VC so binary proofs fail closed.
    Formula::Bool(true)
}

fn saved_return_address_overwrite_access_vc(
    func_name: &str,
    access: &MemoryAccessFact,
) -> Option<VerificationCondition> {
    if access.kind != MemoryAccessKind::Write || !is_stack_like_access(access) {
        return None;
    }

    if stack_write_definitely_misses_saved_return_slot(access) {
        return None;
    }

    Some(saved_return_address_overwrite_vc(
        func_name,
        access.origin.span(),
        access.address.clone(),
        access.width_bytes,
        access.offset.is_none(),
    ))
}

fn saved_return_address_overwrite_store_vc(
    func_name: &str,
    block_id: usize,
    span: &SourceSpan,
    addr: Formula,
    access_width_bytes: u32,
) -> VerificationCondition {
    let mut vc =
        saved_return_address_overwrite_vc(func_name, span.clone(), addr, access_width_bytes, true);
    vc.kind = VcKind::SavedReturnAddressOverwrite {
        access_width_bytes,
        slot: format!("unknown_stack_return_slot_bb{block_id}"),
    };
    vc
}

fn saved_return_address_overwrite_vc(
    func_name: &str,
    location: SourceSpan,
    addr: Formula,
    access_width_bytes: u32,
    unknown_stack_return_slot: bool,
) -> VerificationCondition {
    let slot = if unknown_stack_return_slot {
        "unknown_stack_return_slot"
    } else {
        "saved_return_address"
    };
    let mut formula = saved_return_address_alias_formula(
        addr,
        access_width_bytes,
        default_saved_return_address_width_bytes(),
    );

    if unknown_stack_return_slot {
        formula = Formula::Or(vec![
            formula,
            Formula::Var(generated_lift_symbol(&format!("{slot}_may_alias")), Sort::Bool),
        ]);
    }

    VerificationCondition {
        kind: VcKind::SavedReturnAddressOverwrite { access_width_bytes, slot: slot.to_string() },
        function: func_name.to_string().into(),
        location,
        formula,
        contract_metadata: None,
    }
}

fn is_stack_like_access(access: &MemoryAccessFact) -> bool {
    access.region == MemoryRegionKind::Stack
        || (access.region == MemoryRegionKind::Unknown
            && access
                .base_object
                .as_deref()
                .is_some_and(|base| base.contains("stack") || base.contains("frame")))
}

fn stack_write_definitely_misses_saved_return_slot(access: &MemoryAccessFact) -> bool {
    let Some(offset) = access.offset.as_ref().and_then(formula_i128_value) else {
        return false;
    };
    let Some(width) = i128::from(access.width_bytes).checked_add(offset) else {
        return false;
    };
    let slot_width = i128::from(default_saved_return_address_width_bytes());

    width <= 0 || offset >= slot_width
}

fn formula_i128_value(formula: &Formula) -> Option<i128> {
    match formula {
        Formula::Int(value) | Formula::BitVec { value, .. } => Some(*value),
        Formula::UInt(value) => i128::try_from(*value).ok(),
        _ => None,
    }
}

fn default_saved_return_address_width_bytes() -> u32 {
    8
}

fn saved_return_address_alias_formula(
    addr: Formula,
    access_width_bytes: u32,
    slot_width_bytes: u32,
) -> Formula {
    let saved_return_address =
        Formula::Var(generated_lift_symbol("saved_return_address"), Sort::BitVec(64));
    let write_end = Formula::BvAdd(
        Box::new(addr.clone()),
        Box::new(Formula::BitVec { value: i128::from(access_width_bytes), width: 64 }),
        64,
    );
    let slot_end = Formula::BvAdd(
        Box::new(saved_return_address.clone()),
        Box::new(Formula::BitVec { value: i128::from(slot_width_bytes), width: 64 }),
        64,
    );

    Formula::And(vec![
        Formula::BvULt(Box::new(addr), Box::new(slot_end), 64),
        Formula::BvULt(Box::new(saved_return_address), Box::new(write_end), 64),
    ])
}

fn memory_access_vc(func_name: &str, access: &MemoryAccessFact) -> VerificationCondition {
    let kind = match access.kind {
        MemoryAccessKind::Read => "binary memory read invalid",
        MemoryAccessKind::Write => "binary memory write OOB",
        _ => "binary memory access invalid",
    };
    let formula = if access.region == MemoryRegionKind::Unknown {
        unknown_memory_region_formula(access.address.clone())
    } else {
        memory_oob_formula(access.address.clone())
    };

    VerificationCondition {
        kind: VcKind::Assertion {
            message: format!(
                "{kind} at 0x{:x} ({} bytes)",
                access.origin.instruction_address, access.width_bytes
            ),
        },
        function: func_name.to_string().into(),
        location: access.origin.span(),
        formula,
        contract_metadata: None,
    }
}

#[cfg(test)]
mod tests {
    use trust_types::UnwindEdge;
    use trust_lift::cfg::{Cfg, LiftedBlock};
    use trust_types::{
        BasicBlock, BinOp, BinaryAbiFact, BinaryAbiFactKind, BinaryFactConfidence,
        BinaryFactEvidence, BinaryFactSubject, BinaryOrigin, BinaryStorageFact,
        BinaryStorageLocation, BlockId, Endianness, LocalDecl, MemoryAccessFact, MemoryAccessKind,
        MemoryRegionKind, Operand, Place, Rvalue, SourceSpan, Statement, Terminator, TrustLevel,
        Ty, VerifiableBody, VerificationCondition,
    };

    use super::*;

    /// Build a minimal LiftedFunction for testing.
    fn make_test_lifted() -> LiftedFunction {
        make_test_lifted_with_op(BinOp::Add)
    }

    fn make_test_lifted_with_op(op: BinOp) -> LiftedFunction {
        // A simple function with one block: assigns result = X0 OP X1, then returns.
        let mut cfg = Cfg::new();
        cfg.add_block(LiftedBlock {
            id: 0,
            start_addr: 0x1000,
            instructions: vec![],
            successors: vec![],
            is_return: true,
        });

        let body = VerifiableBody {
            locals: vec![
                LocalDecl {
                    index: 0,
                    ty: Ty::Int { width: 64, signed: false },
                    name: Some("_lifted_result".into()),
                },
                LocalDecl {
                    index: 1,
                    ty: Ty::Int { width: 64, signed: false },
                    name: Some("X0".into()),
                },
                LocalDecl {
                    index: 2,
                    ty: Ty::Int { width: 64, signed: false },
                    name: Some("X1".into()),
                },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::BinaryOp(
                        op,
                        Operand::Copy(Place::local(1)),
                        Operand::Copy(Place::local(2)),
                    ),
                    span: SourceSpan {
                        file: "binary:0x1000".to_string(),
                        line_start: 0,
                        col_start: 0,
                        line_end: 0,
                        col_end: 0,
                    },
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: Ty::Int { width: 64, signed: false },
        };

        LiftedFunction {
            name: "test_add".to_string(),
            entry_point: 0x1000,
            cfg,
            trust_ir_body: body,
            ssa: None,
            annotations: vec![],
            memory_accesses: vec![],
            trust_level: trust_types::TrustLevel::Partial,
            unsupported: trust_types::UnsupportedLedger::default(),
        }
    }

    /// Build a LiftedFunction with memory operations for memory model VC tests.
    fn make_mem_lifted() -> LiftedFunction {
        make_mem_lifted_with_layout(LocalLayout::standard(), "test_mem", 0x2000)
    }

    fn test_mem_array() -> Formula {
        Formula::Var(
            "MEM".into(),
            Sort::Array(Box::new(Sort::BitVec(64)), Box::new(Sort::BitVec(8))),
        )
    }

    fn test_mem_store(address: Formula) -> Formula {
        Formula::Store(
            Box::new(test_mem_array()),
            Box::new(address),
            Box::new(Formula::BitVec { value: 0xaa, width: 8 }),
        )
    }

    fn test_mem_read(address: Formula) -> Formula {
        Formula::Select(Box::new(test_mem_array()), Box::new(address))
    }

    fn test_symbolic_formula(name: &str) -> Formula {
        Formula::Var(name.to_string(), Sort::BitVec(64))
    }

    #[test]
    fn test_operand_to_abstract_value_preserves_symbolic_formula() {
        let formula = test_symbolic_formula("symbolic_operand");

        assert_eq!(
            operand_to_abstract_value(&Operand::Symbolic(formula.clone())),
            AbstractValue::Formula(formula)
        );
    }

    #[test]
    fn test_rvalue_to_formula_preserves_symbolic_store_value() {
        let formula = test_symbolic_formula("symbolic_store_value");

        assert_eq!(rvalue_to_formula(&Rvalue::Use(Operand::Symbolic(formula.clone()))), formula);
    }

    #[test]
    fn test_symbolic_assign_preserved_in_abstract_insn() {
        let formula = test_symbolic_formula("symbolic_assign");
        let stmt = Statement::Assign {
            place: Place::local(3),
            rvalue: Rvalue::Use(Operand::Symbolic(formula.clone())),
            span: SourceSpan::binary_address(0x3000),
        };

        let insn = stmt_to_abstract_insn(&stmt, 0x3000).expect("assign instruction");

        assert_eq!(insn.op, AbstractOp::Assign { dst: 3, src: AbstractValue::Formula(formula) });
    }

    #[test]
    fn test_symbolic_cast_preserved_in_abstract_insn() {
        let formula = test_symbolic_formula("symbolic_cast");
        let stmt = Statement::Assign {
            place: Place::local(4),
            rvalue: Rvalue::Cast(Operand::Symbolic(formula.clone()), Ty::u64()),
            span: SourceSpan::binary_address(0x3004),
        };

        let insn = stmt_to_abstract_insn(&stmt, 0x3004).expect("cast instruction");

        assert_eq!(insn.op, AbstractOp::Assign { dst: 4, src: AbstractValue::Formula(formula) });
    }

    #[test]
    fn test_symbolic_binop_preserved_in_abstract_insn() {
        let formula = test_symbolic_formula("symbolic_binop");
        let stmt = Statement::Assign {
            place: Place::local(5),
            rvalue: Rvalue::BinaryOp(
                trust_types::BinOp::Add,
                Operand::Symbolic(formula.clone()),
                Operand::Constant(ConstValue::Uint(1, 64)),
            ),
            span: SourceSpan::binary_address(0x3008),
        };

        let insn = stmt_to_abstract_insn(&stmt, 0x3008).expect("binop instruction");

        match insn.op {
            AbstractOp::BinArith { dst, lhs, .. } => {
                assert_eq!(dst, 5);
                assert_eq!(lhs, AbstractValue::Formula(formula));
            }
            other => panic!("expected BinArith op, got {other:?}"),
        }
    }

    #[test]
    fn test_symbolic_call_arg_preserved_in_abstract_insn() {
        let formula = test_symbolic_formula("symbolic_call_arg");
        let term = Terminator::Call {
            unwind: UnwindEdge::Unreachable,
            is_unsafe_sig: false,
            is_foreign: false,
            func: "callee".to_string(),
            args: vec![Operand::Symbolic(formula.clone())],
            dest: Place::local(0),
            target: Some(BlockId(1)),
            span: SourceSpan::binary_address(0x300c),
            atomic: None,
        };

        let insn = terminator_to_abstract_insn(&term, 0x300c, 0x3000).expect("call instruction");

        match insn.op {
            AbstractOp::Call { args, .. } => {
                assert_eq!(args, vec![AbstractValue::Formula(formula)]);
            }
            other => panic!("expected Call op, got {other:?}"),
        }
    }

    #[test]
    fn test_symbolic_memory_store_value_preserved_in_abstract_insn() {
        let formula = test_symbolic_formula("symbolic_memory_store_value");
        let stmt = Statement::Assign {
            place: Place { local: 6, projections: vec![trust_types::Projection::Deref] },
            rvalue: Rvalue::Use(Operand::Symbolic(formula.clone())),
            span: SourceSpan::binary_address(0x3010),
        };

        let insn = stmt_to_abstract_insn(&stmt, 0x3010).expect("store instruction");

        match insn.op {
            AbstractOp::Store { access: MemoryAccess::Write { value, .. } } => {
                assert_eq!(value, formula);
            }
            other => panic!("expected Store op, got {other:?}"),
        }
    }

    fn make_mem_lifted_with_layout(
        layout: LocalLayout,
        name: &str,
        entry_point: u64,
    ) -> LiftedFunction {
        let mem_idx = layout.mem_local;

        let mut cfg = Cfg::new();
        cfg.add_block(LiftedBlock {
            id: 0,
            start_addr: entry_point,
            instructions: vec![],
            successors: vec![],
            is_return: true,
        });

        let body = VerifiableBody {
            locals: {
                let mut locals = Vec::new();
                // Build locals matching the selected layout up to MEM.
                locals.push(LocalDecl {
                    index: 0,
                    ty: Ty::Int { width: 64, signed: false },
                    name: Some("_result".into()),
                });
                locals.push(LocalDecl {
                    index: 1,
                    ty: Ty::Int { width: 64, signed: false },
                    name: Some("X0".into()),
                });
                locals.push(LocalDecl {
                    index: 2,
                    ty: Ty::Int { width: 64, signed: false },
                    name: Some("X1".into()),
                });
                // Pad locals 3..(mem_idx-1) to position MEM at the selected index.
                for i in 3..mem_idx {
                    locals.push(LocalDecl {
                        index: i,
                        ty: Ty::Int { width: 64, signed: false },
                        name: Some(format!("_pad{i}")),
                    });
                }
                locals.push(LocalDecl {
                    index: mem_idx,
                    ty: Ty::Int { width: 64, signed: false },
                    name: Some("MEM".into()),
                });
                locals
            },
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    // Memory write (to MEM local from the selected layout)
                    Statement::Assign {
                        place: Place::local(mem_idx),
                        rvalue: Rvalue::Use(Operand::Symbolic(test_mem_store(Formula::Var(
                            "write_addr".into(),
                            Sort::BitVec(64),
                        )))),
                        span: SourceSpan {
                            file: format!("binary:0x{entry_point:x}"),
                            line_start: 0,
                            col_start: 0,
                            line_end: 0,
                            col_end: 0,
                        },
                    },
                ],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: Ty::Int { width: 64, signed: false },
        };

        LiftedFunction {
            name: name.to_string(),
            entry_point,
            cfg,
            trust_ir_body: body,
            ssa: None,
            annotations: vec![],
            memory_accesses: vec![],
            trust_level: trust_types::TrustLevel::Partial,
            unsupported: trust_types::UnsupportedLedger::default(),
        }
    }

    fn formula_contains_var_name(formula: &Formula, name: &str) -> bool {
        formula.var_name() == Some(name)
            || formula.children().iter().any(|child| formula_contains_var_name(child, name))
    }

    fn formula_contains_var_prefix(formula: &Formula, prefix: &str) -> bool {
        formula.var_name().is_some_and(|name| name.starts_with(prefix))
            || formula.children().iter().any(|child| formula_contains_var_prefix(child, prefix))
    }

    fn assert_binary_security_blocker(vc: &VerificationCondition, code: &str) {
        let classification =
            classify_binary_security_vc(vc).expect("expected binary security VC classification");
        assert!(
            classification.proof_grade_blockers.iter().any(|blocker| blocker.code == code),
            "expected blocker `{code}` in {classification:?}"
        );
        assert!(
            formula_contains_var_prefix(&vc.formula, BINARY_ALLOCATOR_BLOCKER_PREFIX),
            "allocator VC should encode proof-grade blocker atoms"
        );
    }

    fn assert_binary_security_classification_blocker(
        vc: &VerificationCondition,
        family: BinarySecurityVcFamily,
        code: &str,
    ) {
        let classification =
            classify_binary_security_vc(vc).expect("expected binary security VC classification");
        assert_eq!(classification.family, family);
        assert_eq!(classification.family_id, family.stable_id());
        assert!(
            classification.proof_grade_blockers.iter().any(|blocker| blocker.code == code),
            "expected blocker `{code}` in {classification:?}"
        );
    }

    fn test_binary_origin(address: u64) -> BinaryOrigin {
        BinaryOrigin {
            binary_path: None,
            function_entry: Some(0x2000),
            instruction_address: address,
            instruction_size: Some(4),
            encoding: Some(0),
            instruction_bytes: vec![],
            source: None,
        }
    }

    fn unsupported_memory_record(address: u64) -> UnsupportedRecord {
        UnsupportedRecord {
            stage: "trust-lift::memory-provenance".to_string(),
            architecture: Some("x86_64".to_string()),
            origin: Some(test_binary_origin(address)),
            opcode: Some("mov".to_string()),
            operand: Some("[opaque]".to_string()),
            feature: "unclassified memory region".to_string(),
        }
    }

    fn aarch64_memory_access(address: u64, kind: MemoryAccessKind) -> MemoryAccessFact {
        MemoryAccessFact {
            origin: test_binary_origin(address),
            kind,
            address: Formula::Var(format!("atomic_addr_{address:x}"), Sort::BitVec(64)),
            width_bytes: 8,
            endianness: Endianness::Little,
            region: MemoryRegionKind::Unknown,
            base_object: None,
            offset: None,
            extent: None,
            provenance: Some("AArch64 scalar data-plane memory access".to_string()),
            taint: vec![],
        }
    }

    fn aarch64_selected_release_acquire_access(
        address: u64,
        kind: MemoryAccessKind,
    ) -> MemoryAccessFact {
        let mut access = aarch64_memory_access(address, kind);
        access.address = Formula::Var("aarch64_selected_ready".into(), Sort::BitVec(64));
        access.provenance = None;
        access
    }

    fn aarch64_selected_release_acquire_accesses(
        release_address: u64,
        acquire_address: u64,
    ) -> Vec<MemoryAccessFact> {
        let mut release =
            aarch64_selected_release_acquire_access(release_address, MemoryAccessKind::Write);
        let mut acquire =
            aarch64_selected_release_acquire_access(acquire_address, MemoryAccessKind::Read);
        let lifted = make_test_lifted();
        let selected_image_digest =
            aarch64_release_acquire_selected_image_digest(&lifted, &release, &acquire);
        release.provenance = Some(aarch64_selected_release_acquire_provenance(
            &release,
            "release",
            "release ordering event",
            &selected_image_digest,
        ));
        acquire.provenance = Some(aarch64_selected_release_acquire_provenance(
            &acquire,
            "acquire",
            "acquire ordering event",
            &selected_image_digest,
        ));
        vec![release, acquire]
    }

    fn aarch64_selected_release_acquire_provenance(
        access: &MemoryAccessFact,
        role: &str,
        ordering_event: &str,
        selected_image_digest: &str,
    ) -> String {
        let instruction_digest = aarch64_instruction_provenance_digest(&access.origin);
        let memory_digest = aarch64_memory_access_digest(access);
        let evidence_hash = aarch64_release_acquire_evidence_hash(
            role,
            selected_image_digest,
            &instruction_digest,
            &memory_digest,
        );
        let evidence_id = aarch64_release_acquire_evidence_id(
            role,
            selected_image_digest,
            &instruction_digest,
            &memory_digest,
        );
        let opcode = aarch64_release_acquire_opcode_for_role(role).expect("test role opcode");
        let ordering = aarch64_release_acquire_ordering_for_role(role).expect("test role ordering");
        format!(
            "accepted-slice:aarch64.release_acquire; role={role}; status=proof-consumed; evidence_schema={AARCH64_RELEASE_ACQUIRE_EVIDENCE_SCHEMA}; evidence_id={evidence_id}; artifact_digest=sha256:{evidence_hash}; artifact_row_schema={AARCH64_ORDERING_MONITOR_EVIDENCE_ROW_SCHEMA}; artifact_row_type={AARCH64_ORDERING_MONITOR_EVIDENCE_ROW_TYPE}; artifact_row_status=accepted; selected_image_identity=function_entry=0x{:x},release=synthetic,acquire=synthetic; selected_image_digest=sha256:{selected_image_digest}; instruction_provenance_digest=sha256:{instruction_digest}; memory_access_digest=sha256:{memory_digest}; opcode={opcode}; ordering={ordering}; ordering_event={ordering_event}; exclusive_monitor=None; exclusive_monitor_witness=not-applicable-reviewed; store_conditional_status=not-applicable-reviewed; synchronization_edge=absent-reviewed; happens_before_witness=absent-reviewed; thread_identity=absent-reviewed; unsupported_ledger_boundary=explicit-empty; unsupported_ledger_records=0; reviewed_unsupported_absence={AARCH64_REVIEWED_UNSUPPORTED_ABSENCE}; consumed_witnesses=[{ordering_event}, same atomic location witness]; reviewed_absence=[exclusive_monitor=None, exclusive monitor absent-reviewed, store-conditional status not-applicable-reviewed, synchronization edge absent-reviewed, happens-before witness absent-reviewed, thread identity absent-reviewed]; aarch64_ordering_monitor_evidence_schema={AARCH64_ORDERING_MONITOR_EVIDENCE_ROW_SCHEMA}; aarch64_ordering_monitor_evidence_status=accepted; aarch64_ordering_monitor_evidence_opcode={opcode}; aarch64_ordering_monitor_evidence_ordering={ordering}; aarch64_ordering_monitor_evidence_exclusive_monitor=None; aarch64_ordering_monitor_evidence_digest=sha256:{evidence_hash}; aarch64_ordering_monitor_evidence_blockers=[]; release_transcript_consumed=true; release_transcript_digest=sha256:{evidence_hash}; no FP/SIMD/syscall/trap/exception claim; no exclusive-monitor/status claim",
            access.origin.function_entry.unwrap_or(0)
        )
    }

    fn aarch64_atomic_record(address: u64, opcode: &str) -> UnsupportedRecord {
        UnsupportedRecord {
            stage: "trust-lift::semantic-lift".to_string(),
            architecture: Some("aarch64".to_string()),
            origin: Some(test_binary_origin(address)),
            opcode: Some(opcode.to_string()),
            operand: Some("[x0]".to_string()),
            feature: "atomic memory-order exclusive boundary".to_string(),
        }
    }

    fn aarch64_unsupported_record(address: u64, opcode: &str, feature: &str) -> UnsupportedRecord {
        UnsupportedRecord {
            stage: "trust-lift::semantic-lift".to_string(),
            architecture: Some("aarch64".to_string()),
            origin: Some(test_binary_origin(address)),
            opcode: Some(opcode.to_string()),
            operand: None,
            feature: feature.to_string(),
        }
    }

    fn x86_64_semantic_unsupported_record(
        address: u64,
        opcode: &str,
        feature: &str,
    ) -> UnsupportedRecord {
        UnsupportedRecord {
            stage: "trust-lift::semantic-lift".to_string(),
            architecture: Some("x86_64".to_string()),
            origin: Some(test_binary_origin(address)),
            opcode: Some(opcode.to_string()),
            operand: None,
            feature: feature.to_string(),
        }
    }

    fn make_x86_64_empty_unsupported_ledger_slice() -> LiftedFunction {
        let entry = 0x401000;
        let layout = LocalLayout::x86_64();
        let mut cfg = Cfg::new();
        cfg.add_block(LiftedBlock {
            id: 0,
            start_addr: entry,
            instructions: vec![],
            successors: vec![entry + 1],
            is_return: false,
        });
        cfg.add_block(LiftedBlock {
            id: 1,
            start_addr: entry + 1,
            instructions: vec![],
            successors: vec![],
            is_return: true,
        });

        let mut locals = Vec::with_capacity(layout.total);
        locals.push(LocalDecl {
            index: layout.return_local,
            ty: Ty::Int { width: 64, signed: false },
            name: Some("_lifted_result".to_string()),
        });
        for (offset, name) in [
            "RAX", "RCX", "RDX", "RBX", "RSP", "RBP", "RSI", "RDI", "R8", "R9", "R10", "R11",
            "R12", "R13", "R14", "R15",
        ]
        .into_iter()
        .enumerate()
        {
            locals.push(LocalDecl {
                index: layout.gpr_base + offset,
                ty: Ty::Int { width: 64, signed: false },
                name: Some(name.to_string()),
            });
        }
        locals.push(LocalDecl {
            index: layout.sp_local,
            ty: Ty::Int { width: 64, signed: false },
            name: Some("SP".to_string()),
        });
        locals.push(LocalDecl {
            index: layout.pc_local,
            ty: Ty::Int { width: 64, signed: false },
            name: Some("RIP".to_string()),
        });
        for (index, name) in [
            (layout.flag_n, "CF"),
            (layout.flag_z, "ZF"),
            (layout.flag_c, "SF"),
            (layout.flag_v, "OF"),
        ] {
            locals.push(LocalDecl { index, ty: Ty::Bool, name: Some(name.to_string()) });
        }
        locals.push(LocalDecl {
            index: layout.mem_local,
            ty: Ty::Int { width: 64, signed: false },
            name: Some("MEM".to_string()),
        });
        assert_eq!(locals.len(), layout.total);

        let body = VerifiableBody {
            locals,
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(layout.pc_local),
                        rvalue: Rvalue::Use(Operand::Symbolic(Formula::BvAdd(
                            Box::new(Formula::BitVec { value: entry as i128, width: 64 }),
                            Box::new(Formula::BitVec { value: 1, width: 64 }),
                            64,
                        ))),
                        span: SourceSpan::binary_address(entry),
                    }],
                    terminator: Terminator::Goto(BlockId(1)),
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 0,
            return_ty: Ty::Int { width: 64, signed: false },
        };

        LiftedFunction {
            name: "x86_64_empty_ledger_selected_slice".to_string(),
            entry_point: entry,
            cfg,
            trust_ir_body: body,
            ssa: None,
            annotations: vec![],
            memory_accesses: vec![],
            trust_level: TrustLevel::Partial,
            unsupported: trust_types::UnsupportedLedger::default(),
        }
    }

    fn register_location(name: &str) -> BinaryStorageLocation {
        BinaryStorageLocation::Register { name: name.to_string(), bit_width: Some(64) }
    }

    fn proof_grade_abi(
        subject: BinaryFactSubject,
        kind: BinaryAbiFactKind,
        evidence: BinaryFactEvidence,
    ) -> BinaryAbiFact {
        BinaryAbiFact {
            subject,
            kind,
            origin: Some(test_binary_origin(0x2100)),
            evidence,
            confidence: BinaryFactConfidence::Validated,
            trust_level: TrustLevel::ProofGrade,
            assumptions: vec![],
        }
    }

    fn proof_grade_storage(
        subject: BinaryFactSubject,
        location: BinaryStorageLocation,
        evidence: BinaryFactEvidence,
    ) -> BinaryStorageFact {
        BinaryStorageFact {
            subject,
            location,
            ty: None,
            mutable: None,
            alignment_bytes: None,
            valid_range: None,
            origin: Some(test_binary_origin(0x2110)),
            evidence,
            confidence: BinaryFactConfidence::Validated,
            trust_level: TrustLevel::ProofGrade,
            assumptions: vec![],
        }
    }

    fn allocator_event(
        kind: AllocatorLifetimeFactKind,
        allocation_id: Option<&str>,
        pointer: Option<&str>,
        address: u64,
    ) -> AllocatorLifetimeFact {
        AllocatorLifetimeFact {
            kind,
            allocation_id: allocation_id.map(str::to_string),
            pointer: pointer.map(|name| Formula::Var(name.to_string(), Sort::BitVec(64))),
            location: SourceSpan::binary_address(address),
            evidence: "synthetic allocator lifetime fact".to_string(),
        }
    }

    fn allocator_access(
        kind: AllocatorLifetimeAccessKind,
        allocation_id: Option<&str>,
        pointer: Option<&str>,
        address: u64,
    ) -> AllocatorLifetimeAccessFact {
        AllocatorLifetimeAccessFact {
            kind,
            allocation_id: allocation_id.map(str::to_string),
            pointer: pointer.map(|name| Formula::Var(name.to_string(), Sort::BitVec(64))),
            location: SourceSpan::binary_address(address),
            evidence: "synthetic allocator access fact".to_string(),
        }
    }

    fn copy_sink_fact(
        callee: &str,
        copy_length: Option<&str>,
        dest_capacity: Option<&str>,
        address: u64,
    ) -> BinaryCopySinkLengthFact {
        BinaryCopySinkLengthFact {
            callee: callee.to_string(),
            dest: Some(Formula::Var("dst".to_string(), Sort::BitVec(64))),
            copy_length: copy_length.map(|name| Formula::Var(name.to_string(), Sort::Int)),
            dest_capacity: dest_capacity.map(|name| Formula::Var(name.to_string(), Sort::Int)),
            location: SourceSpan::binary_address(address),
            evidence: "synthetic copy-sink length fact".to_string(),
        }
    }

    fn symbolic_formula(name: &str) -> Formula {
        Formula::Var(name.to_string(), Sort::BitVec(64))
    }

    #[test]
    fn test_symbolic_assign_operand_preserved_in_legacy_instruction() {
        let formula = symbolic_formula("sym_assign");
        let stmt = Statement::Assign {
            place: Place::local(3),
            rvalue: Rvalue::Use(Operand::Symbolic(formula.clone())),
            span: SourceSpan::binary_address(0x1000),
        };

        let insn = stmt_to_abstract_insn(&stmt, 0x1000).expect("assign should lower");
        match insn.op {
            AbstractOp::Assign { dst, src: AbstractValue::Formula(actual) } => {
                assert_eq!(dst, 3);
                assert_eq!(actual, formula);
            }
            other => panic!("expected symbolic assign formula, got {other:?}"),
        }
    }

    #[test]
    fn test_symbolic_cast_operand_preserved_in_legacy_instruction() {
        let formula = symbolic_formula("sym_cast");
        let stmt = Statement::Assign {
            place: Place::local(4),
            rvalue: Rvalue::Cast(
                Operand::Symbolic(formula.clone()),
                Ty::Int { width: 64, signed: false },
            ),
            span: SourceSpan::binary_address(0x1004),
        };

        let insn = stmt_to_abstract_insn(&stmt, 0x1004).expect("cast should lower");
        match insn.op {
            AbstractOp::Assign { dst, src: AbstractValue::Formula(actual) } => {
                assert_eq!(dst, 4);
                assert_eq!(actual, formula);
            }
            other => panic!("expected symbolic cast formula, got {other:?}"),
        }
    }

    #[test]
    fn test_symbolic_binop_operands_preserved_in_legacy_instruction() {
        let lhs = symbolic_formula("sym_lhs");
        let rhs = symbolic_formula("sym_rhs");
        let stmt = Statement::Assign {
            place: Place::local(5),
            rvalue: Rvalue::BinaryOp(
                trust_types::BinOp::Add,
                Operand::Symbolic(lhs.clone()),
                Operand::Symbolic(rhs.clone()),
            ),
            span: SourceSpan::binary_address(0x1008),
        };

        let insn = stmt_to_abstract_insn(&stmt, 0x1008).expect("binop should lower");
        match insn.op {
            AbstractOp::BinArith {
                dst,
                op,
                lhs: AbstractValue::Formula(actual_lhs),
                rhs: AbstractValue::Formula(actual_rhs),
            } => {
                assert_eq!(dst, 5);
                assert_eq!(op, trust_types::BinOp::Add);
                assert_eq!(actual_lhs, lhs);
                assert_eq!(actual_rhs, rhs);
            }
            other => panic!("expected symbolic binop formulas, got {other:?}"),
        }
    }

    #[test]
    fn test_symbolic_call_operand_preserved_in_legacy_instruction() {
        let formula = symbolic_formula("sym_call_arg");
        let term = Terminator::Call {
            unwind: UnwindEdge::Unreachable,
            is_unsafe_sig: false,
            is_foreign: false,
            func: "callee".to_string(),
            args: vec![Operand::Symbolic(formula.clone())],
            dest: Place::local(0),
            target: Some(BlockId(2)),
            span: SourceSpan::binary_address(0x100c),
            atomic: None,
        };

        let insn = terminator_to_abstract_insn(&term, 0x100c, 0x1000).expect("call should lower");
        match insn.op {
            AbstractOp::Call { func, args, dest, next } => {
                assert_eq!(func, "callee");
                assert_eq!(args, vec![AbstractValue::Formula(formula)]);
                assert_eq!(dest, None);
                assert_eq!(next, Some(0x1200));
            }
            other => panic!("expected symbolic call arg formula, got {other:?}"),
        }
    }

    #[test]
    fn test_symbolic_memory_store_value_preserved_in_legacy_instruction() {
        let store_formula = test_mem_store(symbolic_formula("sym_store_addr"));
        let stmt = Statement::Assign {
            place: Place { local: 6, projections: vec![Projection::Deref] },
            rvalue: Rvalue::Use(Operand::Symbolic(store_formula.clone())),
            span: SourceSpan::binary_address(0x1010),
        };

        let insn = stmt_to_abstract_insn(&stmt, 0x1010).expect("store should lower");
        match insn.op {
            AbstractOp::Store { access: MemoryAccess::Write { value, .. } } => {
                assert_eq!(value, store_formula);
            }
            other => panic!("expected exact symbolic store formula, got {other:?}"),
        }
    }

    #[test]
    fn test_lift_to_verifiable_preserves_name() {
        let lifted = make_test_lifted();
        let verifiable = lift_to_verifiable(&lifted);
        assert_eq!(verifiable.name, "test_add");
        assert_eq!(verifiable.def_path, "binary::test_add");
    }

    #[test]
    fn test_lift_to_verifiable_preserves_body() {
        let lifted = make_test_lifted();
        let verifiable = lift_to_verifiable(&lifted);
        assert_eq!(verifiable.body.blocks.len(), lifted.trust_ir_body.blocks.len());
        assert_eq!(verifiable.body.locals.len(), lifted.trust_ir_body.locals.len());
        assert_eq!(verifiable.body.arg_count, lifted.trust_ir_body.arg_count);
    }

    #[test]
    fn test_generate_binary_vcs_strips_source_arithmetic_overflow_vcs() {
        let lifted = make_test_lifted();
        let vcs = generate_binary_vcs(&lifted);

        // Binary-lifted arithmetic is machine modular arithmetic, not Rust
        // source overflow-panic semantics. trust-mc-lib owns that lane; vcgen
        // must not reintroduce source-style overflow obligations here.
        assert!(
            vcs.iter().all(|vc| !matches!(vc.kind, VcKind::ArithmeticOverflow { .. })),
            "binary lifted arithmetic should not surface source-style overflow VCs: {vcs:#?}"
        );
    }

    fn assert_generate_binary_vcs_strips_source_shift_overflow_vcs(op: BinOp) {
        let lifted = make_test_lifted_with_op(op);
        let source_vcs = crate::generate_vcs(&lift_to_verifiable(&lifted));
        assert!(
            source_vcs.iter().any(
                |vc| matches!(vc.kind, VcKind::ShiftOverflow { op: vc_op, .. } if vc_op == op)
            ),
            "source lowering should emit ShiftOverflow for {op:?}: {source_vcs:#?}"
        );

        let vcs = generate_binary_vcs(&lifted);
        assert!(
            vcs.iter().all(|vc| !matches!(vc.kind, VcKind::ShiftOverflow { .. })),
            "binary lifted shifts should not surface source-style ShiftOverflow VCs: {vcs:#?}"
        );
    }

    #[test]
    fn test_generate_binary_vcs_strips_source_shift_overflow_vcs_for_shl() {
        assert_generate_binary_vcs_strips_source_shift_overflow_vcs(BinOp::Shl);
    }

    #[test]
    fn test_generate_binary_vcs_strips_source_shift_overflow_vcs_for_shr() {
        assert_generate_binary_vcs_strips_source_shift_overflow_vcs(BinOp::Shr);
    }

    #[test]
    fn test_generate_binary_vcs_all_reference_function_name() {
        let lifted = make_test_lifted();
        let vcs = generate_binary_vcs(&lifted);

        for vc in &vcs {
            assert_eq!(
                vc.function, "test_add",
                "all VCs should reference the lifted function name"
            );
        }
    }

    #[test]
    fn test_generate_memory_model_vcs_mem_write() {
        let lifted = make_mem_lifted();
        let mem_vcs = generate_memory_model_vcs(&lifted);

        // Should produce memory OOB VC for the MEM write + stack discipline VC for return.
        let oob_vcs: Vec<_> = mem_vcs.iter()
            .filter(|vc| {
                matches!(&vc.kind, VcKind::Assertion { message } if message.contains("memory write OOB"))
            })
            .collect();
        assert!(!oob_vcs.is_empty(), "should produce memory OOB VCs for memory writes");
    }

    #[test]
    fn test_generate_memory_model_vcs_uses_store_address_formula() {
        let lifted = make_mem_lifted();
        let mem_vcs = generate_memory_model_vcs(&lifted);

        let oob_vc = mem_vcs
            .iter()
            .find(|vc| {
                matches!(&vc.kind, VcKind::Assertion { message } if message.contains("memory write OOB"))
            })
            .expect("should produce memory OOB VC");

        assert!(
            formula_contains_var_name(&oob_vc.formula, "write_addr"),
            "memory OOB VC should mention the lifted Store address"
        );
        assert!(
            !formula_contains_var_prefix(&oob_vc.formula, "mem_addr_bb"),
            "memory OOB VC should not invent synthetic memory-address variables"
        );
    }

    #[test]
    fn generated_address_and_alias_symbols_cannot_alias_lifted_names() {
        // Lifted/symbolic inputs may carry these legacy spellings. The memory
        // model must retain both the input leaf and a distinct verifier-owned
        // bound/slot leaf in the same obligation.
        let oob = memory_oob_formula(Formula::Var("stack_base".into(), Sort::BitVec(64)));
        let oob_vars = oob.free_variables();
        assert!(oob_vars.contains("stack_base"));
        assert!(oob_vars.contains(&generated_lift_symbol("stack_base")));
        assert!(oob_vars.contains(&generated_lift_symbol("stack_limit")));

        let alias = saved_return_address_alias_formula(
            Formula::Var("saved_return_address".into(), Sort::BitVec(64)),
            8,
            8,
        );
        let alias_vars = alias.free_variables();
        assert!(alias_vars.contains("saved_return_address"));
        assert!(alias_vars.contains(&generated_lift_symbol("saved_return_address")));
        assert_ne!(generated_lift_symbol("saved_return_address"), "saved_return_address");

        // The legacy abstract-instruction producer and the live memory-model
        // consumer must agree exactly; changing only one side makes the fact
        // inert and silently loses the recovered access address.
        let load_rvalue =
            Rvalue::Use(Operand::Copy(Place { local: 7, projections: vec![Projection::Deref] }));
        let statement = Statement::Assign {
            place: Place::local(8),
            rvalue: load_rvalue.clone(),
            span: SourceSpan::default(),
        };
        let produced = stmt_to_abstract_insn(&statement, 0x1000)
            .expect("deref load should produce an abstract instruction");
        let AbstractOp::Load { access: MemoryAccess::Read { addr: producer_addr, .. }, .. } =
            produced.op
        else {
            panic!("deref load should produce a read access")
        };
        let consumer_addr = memory_read_address(&load_rvalue)
            .expect("memory consumer should recover the deref load address");
        assert_eq!(producer_addr, consumer_addr);
        assert_eq!(
            consumer_addr,
            Formula::Var(generated_lift_symbol("load_addr_local7"), Sort::BitVec(64))
        );
    }

    #[test]
    fn test_generate_memory_model_vcs_mem_store_emits_unknown_return_slot_vc() {
        let lifted = make_mem_lifted();
        let mem_vcs = generate_memory_model_vcs(&lifted);

        let ret_addr_vc = mem_vcs
            .iter()
            .find(|vc| matches!(&vc.kind, VcKind::SavedReturnAddressOverwrite { .. }))
            .expect("memory store without access facts should protect unknown stack return slot");

        match &ret_addr_vc.kind {
            VcKind::SavedReturnAddressOverwrite { access_width_bytes, slot } => {
                assert_eq!(*access_width_bytes, 8);
                assert_eq!(slot, "unknown_stack_return_slot_bb0");
            }
            _ => unreachable!(),
        }
        assert!(formula_contains_var_name(&ret_addr_vc.formula, "write_addr"));
        assert!(formula_contains_var_name(
            &ret_addr_vc.formula,
            &generated_lift_symbol("unknown_stack_return_slot_may_alias")
        ));
    }

    #[test]
    fn test_generate_memory_model_vcs_uses_memory_access_read_fact() {
        let mut lifted = make_mem_lifted();
        lifted.memory_accesses = vec![MemoryAccessFact {
            origin: BinaryOrigin {
                binary_path: None,
                function_entry: Some(0x2000),
                instruction_address: 0x2008,
                instruction_size: Some(4),
                encoding: Some(0),
                instruction_bytes: vec![],
                source: None,
            },
            kind: MemoryAccessKind::Read,
            address: Formula::Var("read_addr".into(), Sort::BitVec(64)),
            width_bytes: 8,
            endianness: Endianness::Little,
            region: MemoryRegionKind::Stack,
            base_object: None,
            offset: None,
            extent: None,
            provenance: None,
            taint: vec![],
        }];

        let mem_vcs = generate_memory_model_vcs(&lifted);
        let read_vc = mem_vcs
            .iter()
            .find(|vc| {
                matches!(&vc.kind, VcKind::Assertion { message } if message.contains("memory read"))
            })
            .expect("memory read fact should produce a read validity VC");

        assert_eq!(read_vc.location.file, "binary:0x2008");
        assert!(formula_contains_var_name(&read_vc.formula, "read_addr"));
    }

    #[test]
    fn test_generate_memory_model_vcs_unknown_read_fact_fails_closed() {
        let mut lifted = make_mem_lifted();
        lifted.memory_accesses = vec![MemoryAccessFact {
            origin: BinaryOrigin {
                binary_path: None,
                function_entry: Some(0x2000),
                instruction_address: 0x2008,
                instruction_size: Some(4),
                encoding: Some(0),
                instruction_bytes: vec![],
                source: None,
            },
            kind: MemoryAccessKind::Read,
            address: Formula::Var("unknown_read_addr".into(), Sort::BitVec(64)),
            width_bytes: 8,
            endianness: Endianness::Little,
            region: MemoryRegionKind::Unknown,
            base_object: None,
            offset: None,
            extent: None,
            provenance: None,
            taint: vec![],
        }];

        let mem_vcs = generate_memory_model_vcs(&lifted);
        let read_vc = mem_vcs
            .iter()
            .find(|vc| {
                matches!(&vc.kind, VcKind::Assertion { message } if message.contains("memory read"))
            })
            .expect("memory read fact should produce a read validity VC");

        assert_eq!(
            read_vc.formula,
            Formula::Bool(true),
            "unknown-region read facts must fail closed instead of becoming provable OOB checks"
        );
    }

    #[test]
    fn test_generate_memory_model_vcs_stack_write_saved_return_address_overwrite_fact() {
        let mut lifted = make_mem_lifted();
        lifted.memory_accesses = vec![MemoryAccessFact {
            origin: test_binary_origin(0x2010),
            kind: MemoryAccessKind::Write,
            address: Formula::Var("stack_write_addr".into(), Sort::BitVec(64)),
            width_bytes: 8,
            endianness: Endianness::Little,
            region: MemoryRegionKind::Stack,
            base_object: Some("stack_frame".to_string()),
            offset: Some(Formula::Int(0)),
            extent: None,
            provenance: None,
            taint: vec![],
        }];

        let mem_vcs = generate_memory_model_vcs(&lifted);
        let ret_addr_vc = mem_vcs
            .iter()
            .find(|vc| matches!(&vc.kind, VcKind::SavedReturnAddressOverwrite { .. }))
            .expect("stack write at offset 0 may overwrite saved return address");

        match &ret_addr_vc.kind {
            VcKind::SavedReturnAddressOverwrite { access_width_bytes, slot } => {
                assert_eq!(*access_width_bytes, 8);
                assert_eq!(slot, "saved_return_address");
            }
            _ => unreachable!(),
        }
        assert_eq!(ret_addr_vc.location.file, "binary:0x2010");
        assert!(formula_contains_var_name(&ret_addr_vc.formula, "stack_write_addr"));
        assert!(formula_contains_var_name(
            &ret_addr_vc.formula,
            &generated_lift_symbol("saved_return_address")
        ));
        assert!(!formula_contains_var_name(
            &ret_addr_vc.formula,
            &generated_lift_symbol("unknown_stack_return_slot_may_alias")
        ));
    }

    #[test]
    fn test_binary_security_family_counts_are_stable_for_saved_return_slice() {
        let mut lifted = make_mem_lifted();
        lifted.memory_accesses = vec![MemoryAccessFact {
            origin: test_binary_origin(0x2010),
            kind: MemoryAccessKind::Write,
            address: Formula::Var("stack_write_addr".into(), Sort::BitVec(64)),
            width_bytes: 16,
            endianness: Endianness::Little,
            region: MemoryRegionKind::Stack,
            base_object: Some("stack_frame".to_string()),
            offset: Some(Formula::Int(-4)),
            extent: None,
            provenance: None,
            taint: vec![],
        }];

        let vcs = generate_memory_model_vcs(&lifted);
        let counts = binary_security_family_counts(&vcs);
        let ret_addr_vcs: Vec<_> = vcs
            .iter()
            .filter(|vc| matches!(&vc.kind, VcKind::SavedReturnAddressOverwrite { .. }))
            .collect();

        assert_eq!(ret_addr_vcs.len(), 1);
        assert_eq!(counts.get("saved_return_address_overwrite"), Some(&1));
        assert_eq!(counts.len(), 1);
        assert_binary_security_classification_blocker(
            ret_addr_vcs[0],
            BinarySecurityVcFamily::SavedReturnAddressOverwrite,
            BLOCKER_SAVED_RETURN_ADDRESS_ALIAS,
        );
        let classification = classify_binary_security_vc(ret_addr_vcs[0]).unwrap();
        assert!(classification.proof_grade_blockers.iter().any(|blocker| {
            blocker.detail.contains("slot=saved_return_address")
                && blocker.detail.contains("access_width_bytes=16")
        }));
        assert_eq!(ret_addr_vcs[0].kind.proof_level(), trust_types::ProofLevel::L0Safety);
        assert!(!ret_addr_vcs[0].kind.has_runtime_fallback(true));
    }

    #[test]
    fn test_generate_memory_model_vcs_disjoint_stack_write_skips_return_address_vc() {
        let mut lifted = make_mem_lifted();
        lifted.memory_accesses = vec![MemoryAccessFact {
            origin: test_binary_origin(0x2018),
            kind: MemoryAccessKind::Write,
            address: Formula::Var("local_stack_write_addr".into(), Sort::BitVec(64)),
            width_bytes: 8,
            endianness: Endianness::Little,
            region: MemoryRegionKind::Stack,
            base_object: Some("stack_frame".to_string()),
            offset: Some(Formula::Int(-16)),
            extent: None,
            provenance: None,
            taint: vec![],
        }];

        let mem_vcs = generate_memory_model_vcs(&lifted);
        assert!(
            !mem_vcs
                .iter()
                .any(|vc| matches!(&vc.kind, VcKind::SavedReturnAddressOverwrite { .. })),
            "stack writes whose known byte range misses [0, pointer_width) should not emit the saved-return-address VC"
        );
    }

    #[test]
    fn test_generate_allocator_lifetime_vcs_double_free_same_allocation() {
        let events = vec![
            allocator_event(
                AllocatorLifetimeFactKind::Allocate,
                Some("heap:main@1000"),
                Some("p"),
                0x1000,
            ),
            allocator_event(
                AllocatorLifetimeFactKind::Free,
                Some("heap:main@1000"),
                Some("p"),
                0x1010,
            ),
            allocator_event(
                AllocatorLifetimeFactKind::Free,
                Some("heap:main@1000"),
                Some("p"),
                0x1020,
            ),
        ];

        let vcs = generate_allocator_lifetime_vcs("main", &events, &[]);
        let double_free_vc = vcs
            .iter()
            .find(|vc| matches!(vc.kind, VcKind::DoubleFree))
            .expect("second free should emit a typed double-free VC");

        assert_eq!(double_free_vc.location.file, "binary:0x1020");
        assert_binary_security_blocker(double_free_vc, BLOCKER_ALLOCATION_ALREADY_FREED);
    }

    #[test]
    fn test_generate_allocator_lifetime_vcs_missing_free_id_keeps_double_free_family_visible() {
        let events = vec![allocator_event(
            AllocatorLifetimeFactKind::Free,
            None,
            Some("opaque_free_ptr"),
            0x1018,
        )];

        let vcs = generate_allocator_lifetime_vcs("main", &events, &[]);
        let double_free_vc = vcs
            .iter()
            .find(|vc| matches!(vc.kind, VcKind::DoubleFree))
            .expect("free with missing allocation identity should emit a typed double-free VC");

        assert_eq!(vcs.len(), 1);
        assert_eq!(double_free_vc.function, "main");
        assert_eq!(double_free_vc.location.file, "binary:0x1018");
        assert_binary_security_blocker(double_free_vc, BLOCKER_MISSING_ALLOCATION_IDENTITY);
        assert_eq!(double_free_vc.kind.proof_level(), trust_types::ProofLevel::L0Safety);
        assert!(
            !double_free_vc.kind.has_runtime_fallback(true),
            "binary allocator lifetime VCs must fail closed without runtime fallback"
        );
    }

    #[test]
    fn test_generate_allocator_lifetime_vcs_use_after_free_access() {
        let events = vec![
            allocator_event(
                AllocatorLifetimeFactKind::Allocate,
                Some("heap:main@1000"),
                Some("p"),
                0x1000,
            ),
            allocator_event(
                AllocatorLifetimeFactKind::Free,
                Some("heap:main@1000"),
                Some("p"),
                0x1010,
            ),
        ];
        let accesses = vec![allocator_access(
            AllocatorLifetimeAccessKind::Read,
            Some("heap:main@1000"),
            Some("p"),
            0x1020,
        )];

        let vcs = generate_allocator_lifetime_vcs("main", &events, &accesses);
        let uaf_vc = vcs
            .iter()
            .find(|vc| matches!(vc.kind, VcKind::UseAfterFree))
            .expect("post-free access should emit a typed use-after-free VC");

        assert_eq!(uaf_vc.location.file, "binary:0x1020");
        assert_binary_security_blocker(uaf_vc, BLOCKER_ACCESS_AFTER_FREE);
    }

    #[test]
    fn test_generate_allocator_lifetime_vcs_keeps_uaf_and_double_free_families_visible() {
        let events = vec![
            allocator_event(
                AllocatorLifetimeFactKind::Allocate,
                Some("heap:main@1000"),
                Some("p"),
                0x1000,
            ),
            allocator_event(
                AllocatorLifetimeFactKind::Free,
                Some("heap:main@1000"),
                Some("p"),
                0x1010,
            ),
            allocator_event(
                AllocatorLifetimeFactKind::Free,
                Some("heap:main@1000"),
                Some("p"),
                0x1020,
            ),
        ];
        let accesses = vec![allocator_access(
            AllocatorLifetimeAccessKind::Read,
            Some("heap:main@1000"),
            Some("p"),
            0x1030,
        )];

        let vcs = generate_allocator_lifetime_vcs("main", &events, &accesses);
        let double_free_count =
            vcs.iter().filter(|vc| matches!(&vc.kind, VcKind::DoubleFree)).count();
        let uaf_count = vcs.iter().filter(|vc| matches!(&vc.kind, VcKind::UseAfterFree)).count();

        assert_eq!(double_free_count, 1);
        assert_eq!(uaf_count, 1);
        assert_eq!(vcs.len(), 2, "allocator lifetime families must not collapse together");
        assert!(vcs.iter().all(|vc| vc.function == "main"));
        assert!(
            vcs.iter().all(|vc| formula_contains_var_prefix(
                &vc.formula,
                BINARY_ALLOCATOR_BLOCKER_PREFIX
            ))
        );
        assert!(vcs.iter().all(|vc| vc.kind.proof_level() == trust_types::ProofLevel::L0Safety));
        assert!(vcs.iter().all(|vc| !vc.kind.has_runtime_fallback(true)));
        assert!(vcs.iter().any(
            |vc| matches!(&vc.kind, VcKind::DoubleFree) && vc.location.file == "binary:0x1020"
        ));
        assert!(
            vcs.iter().any(|vc| matches!(&vc.kind, VcKind::UseAfterFree)
                && vc.location.file == "binary:0x1030")
        );
    }

    #[test]
    fn test_binary_security_family_counts_are_stable_for_allocator_slice() {
        let events = vec![
            allocator_event(
                AllocatorLifetimeFactKind::Allocate,
                Some("heap:main@1000"),
                Some("p"),
                0x1000,
            ),
            allocator_event(
                AllocatorLifetimeFactKind::Free,
                Some("heap:main@1000"),
                Some("p"),
                0x1010,
            ),
            allocator_event(
                AllocatorLifetimeFactKind::Free,
                Some("heap:main@1000"),
                Some("p"),
                0x1020,
            ),
        ];
        let accesses = vec![allocator_access(
            AllocatorLifetimeAccessKind::Write,
            Some("heap:main@1000"),
            Some("p"),
            0x1030,
        )];

        let vcs = generate_allocator_lifetime_vcs("main", &events, &accesses);
        let counts = binary_security_family_counts(&vcs);

        assert_eq!(counts.get("double_free"), Some(&1));
        assert_eq!(counts.get("use_after_free"), Some(&1));
        assert_eq!(counts.len(), 2);

        let classifications: Vec<_> =
            vcs.iter().map(|vc| classify_binary_security_vc(vc).unwrap()).collect();
        assert!(classifications.iter().any(|classification| {
            classification.family == BinarySecurityVcFamily::DoubleFree
                && classification.family_id == "double_free"
                && classification
                    .proof_grade_blockers
                    .iter()
                    .any(|blocker| blocker.code == BLOCKER_ALLOCATION_ALREADY_FREED)
        }));
        assert!(classifications.iter().any(|classification| {
            classification.family == BinarySecurityVcFamily::UseAfterFree
                && classification.family_id == "use_after_free"
                && classification
                    .proof_grade_blockers
                    .iter()
                    .any(|blocker| blocker.code == BLOCKER_ACCESS_AFTER_FREE)
        }));
    }

    #[test]
    fn test_mixed_allocator_and_opaque_memory_trace_keeps_families_without_runtime_fallback() {
        let mut lifted = make_test_lifted();
        lifted.name = "mixed_allocator_memory".to_string();
        lifted.trust_ir_body.blocks.clear();
        lifted.unsupported.records.push(unsupported_memory_record(0x1040));

        let mut vcs: Vec<_> = generate_binary_vcs(&lifted)
            .into_iter()
            .filter(|vc| {
                matches!(&vc.kind, VcKind::UnsafeOperation { desc }
                    if desc.contains("unsupported binary memory fact"))
            })
            .collect();

        let events = vec![
            allocator_event(
                AllocatorLifetimeFactKind::Allocate,
                Some("heap:mixed@1000"),
                Some("p"),
                0x1000,
            ),
            allocator_event(
                AllocatorLifetimeFactKind::Free,
                Some("heap:mixed@1000"),
                Some("p"),
                0x1010,
            ),
            allocator_event(
                AllocatorLifetimeFactKind::Free,
                Some("heap:mixed@1000"),
                Some("p"),
                0x1020,
            ),
        ];
        let accesses = vec![allocator_access(
            AllocatorLifetimeAccessKind::Read,
            Some("heap:mixed@1000"),
            Some("p"),
            0x1030,
        )];
        vcs.extend(generate_allocator_lifetime_vcs(&lifted.name, &events, &accesses));

        let memory_count = vcs
            .iter()
            .filter(|vc| {
                matches!(&vc.kind, VcKind::UnsafeOperation { desc }
                    if desc.contains("unclassified memory region"))
            })
            .count();
        let double_free_count =
            vcs.iter().filter(|vc| matches!(&vc.kind, VcKind::DoubleFree)).count();
        let uaf_count = vcs.iter().filter(|vc| matches!(&vc.kind, VcKind::UseAfterFree)).count();

        assert_eq!(memory_count, 1);
        assert_eq!(double_free_count, 1);
        assert_eq!(uaf_count, 1);
        assert_eq!(vcs.len(), 3, "mixed trace VC families must stay separate");
        assert!(vcs.iter().all(|vc| {
            matches!(&vc.kind, VcKind::UnsafeOperation { .. }) && vc.formula == Formula::Bool(true)
                || matches!(&vc.kind, VcKind::UseAfterFree | VcKind::DoubleFree)
                    && formula_contains_var_prefix(&vc.formula, BINARY_ALLOCATOR_BLOCKER_PREFIX)
        }));
        assert!(vcs.iter().all(|vc| !vc.kind.has_runtime_fallback(true)));
        assert!(vcs.iter().any(
            |vc| matches!(&vc.kind, VcKind::DoubleFree) && vc.location.file == "binary:0x1020"
        ));
        assert!(
            vcs.iter().any(|vc| matches!(&vc.kind, VcKind::UseAfterFree)
                && vc.location.file == "binary:0x1030")
        );
        assert!(vcs.iter().any(|vc| matches!(&vc.kind, VcKind::UnsafeOperation { .. })
            && vc.location.file == "binary:0x1040"));
    }

    #[test]
    fn test_generate_allocator_lifetime_vcs_unknown_heap_access_fails_closed() {
        let events = vec![allocator_event(
            AllocatorLifetimeFactKind::Allocate,
            Some("heap:main@1000"),
            Some("p"),
            0x1000,
        )];
        let accesses =
            vec![allocator_access(AllocatorLifetimeAccessKind::Write, None, None, 0x1030)];

        let vcs = generate_allocator_lifetime_vcs("main", &events, &accesses);
        let uaf_vc = vcs
            .iter()
            .find(|vc| matches!(vc.kind, VcKind::UseAfterFree))
            .expect("unknown heap access with allocator facts should fail closed");

        assert_eq!(uaf_vc.location.file, "binary:0x1030");
        assert_binary_security_blocker(uaf_vc, BLOCKER_MISSING_ALLOCATION_IDENTITY);
        assert_binary_security_blocker(uaf_vc, BLOCKER_MISSING_POINTER_FORMULA);
        assert_binary_security_blocker(uaf_vc, BLOCKER_UNRESOLVED_FREED_ALLOCATION_ALIAS);
    }

    #[test]
    fn test_generate_copy_sink_length_vcs_preserves_formula_and_family_count() {
        let facts = vec![
            copy_sink_fact("memcpy", Some("copy_len"), Some("dst_cap"), 0x1040),
            copy_sink_fact("strncpy", Some("strncpy_len"), None, 0x1050),
            copy_sink_fact("not_a_copy_sink", Some("n"), Some("cap"), 0x1060),
        ];

        let vcs = generate_copy_sink_length_vcs("copy_family", &facts);

        assert_eq!(vcs.len(), 2, "only recognized copy sinks should produce VCs");
        assert!(vcs.iter().all(|vc| {
            matches!(&vc.kind, VcKind::BinaryCopySinkLengthViolation { desc, .. }
                if desc.contains("copy sink length"))
        }));
        assert!(vcs.iter().all(|vc| vc.kind.is_binary_copy_sink_length_violation()));
        assert!(vcs.iter().all(|vc| {
            vc.kind.binary_copy_sink_length_family_tag()
                == Some(VcKind::BINARY_COPY_SINK_LENGTH_FAMILY)
        }));
        assert!(vcs.iter().all(|vc| vc.kind.proof_level() == trust_types::ProofLevel::L0Safety));
        assert!(vcs.iter().all(|vc| !vc.kind.has_runtime_fallback(true)));

        let exact_vc = vcs
            .iter()
            .find(|vc| {
                matches!(&vc.kind, VcKind::BinaryCopySinkLengthViolation { callee, .. } if callee == "memcpy")
            })
            .expect("memcpy copy-sink VC");
        match &exact_vc.formula {
            Formula::Gt(lhs, rhs) => {
                assert!(matches!(lhs.as_ref(), Formula::Var(name, _) if name == "copy_len"));
                assert!(matches!(rhs.as_ref(), Formula::Var(name, _) if name == "dst_cap"));
            }
            other => panic!("expected exact copy_len > dst_cap formula, got {other:?}"),
        }

        let missing_capacity_vc = vcs
            .iter()
            .find(|vc| {
                matches!(&vc.kind, VcKind::BinaryCopySinkLengthViolation { callee, .. } if callee == "strncpy")
            })
            .expect("strncpy missing-capacity VC");
        assert_eq!(missing_capacity_vc.formula, Formula::Bool(true));
        assert!(matches!(
            &missing_capacity_vc.kind,
            VcKind::BinaryCopySinkLengthViolation { desc, .. } if desc.contains("destination capacity")
        ));
    }

    #[test]
    fn test_generate_memory_model_vcs_memcpy_missing_destination_capacity_fails_closed() {
        let mut lifted = make_test_lifted();
        lifted.name = "binary_memcpy_sink".to_string();
        lifted.trust_ir_body.blocks[0].terminator = Terminator::Call {
            unwind: UnwindEdge::Unreachable,
            is_unsafe_sig: false,
            is_foreign: false,
            func: "memcpy".to_string(),
            args: vec![
                Operand::Copy(Place::local(1)),
                Operand::Copy(Place::local(2)),
                Operand::Symbolic(Formula::Var("copy_len".to_string(), Sort::Int)),
            ],
            dest: Place::local(0),
            target: None,
            span: SourceSpan::binary_address(0x1050),
            atomic: None,
        };

        let mem_vcs = generate_memory_model_vcs(&lifted);
        let copy_sink_vcs: Vec<_> = mem_vcs
            .iter()
            .filter(|vc| {
                matches!(&vc.kind, VcKind::BinaryCopySinkLengthViolation { callee, desc }
                    if callee == "memcpy" && desc.contains("copy sink length"))
            })
            .collect();

        assert_eq!(
            copy_sink_vcs.len(),
            1,
            "binary memcpy should emit exactly one copy-sink length VC"
        );
        let vc = copy_sink_vcs[0];
        assert_eq!(vc.function, "binary_memcpy_sink");
        assert_eq!(vc.location.file, "binary:0x1050");
        assert_eq!(
            vc.formula,
            Formula::Bool(true),
            "missing destination-capacity metadata must fail closed"
        );
        assert_eq!(vc.kind.proof_level(), trust_types::ProofLevel::L0Safety);
        assert!(!vc.kind.has_runtime_fallback(true));
        assert!(vc.kind.is_binary_copy_sink_length_violation());
        assert!(matches!(
            &vc.kind,
            VcKind::BinaryCopySinkLengthViolation { desc, .. } if desc.contains("destination capacity")
        ));
    }

    #[test]
    fn test_generate_memory_model_vcs_printf_tainted_format_fails_closed() {
        let mut lifted = make_test_lifted();
        lifted.trust_ir_body.locals[1].name = Some("tainted_user_format".to_string());
        lifted.trust_ir_body.blocks[0].terminator = Terminator::Call {
            unwind: UnwindEdge::Unreachable,
            is_unsafe_sig: false,
            is_foreign: false,
            func: "printf".to_string(),
            args: vec![Operand::Copy(Place::local(1))],
            dest: Place::local(0),
            target: None,
            span: SourceSpan::binary_address(0x1010),
            atomic: None,
        };

        let mem_vcs = generate_memory_model_vcs(&lifted);
        let fmt_vc = mem_vcs
            .iter()
            .find(|vc| matches!(&vc.kind, VcKind::FormatStringViolation { .. }))
            .expect("tainted printf format should emit format-string violation VC");

        assert_eq!(fmt_vc.formula, Formula::Bool(true));
        assert_eq!(fmt_vc.location.file, "binary:0x1010");
        match &fmt_vc.kind {
            VcKind::FormatStringViolation { callee, evidence } => {
                assert_eq!(callee, "printf");
                assert!(evidence.contains("taint"));
            }
            _ => unreachable!(),
        }
    }

    #[test]
    fn test_generate_memory_model_vcs_printf_constant_format_no_format_vc() {
        let mut lifted = make_test_lifted();
        lifted.trust_ir_body.blocks[0].terminator = Terminator::Call {
            unwind: UnwindEdge::Unreachable,
            is_unsafe_sig: false,
            is_foreign: false,
            func: "printf".to_string(),
            args: vec![Operand::Constant(ConstValue::Uint(0x4000, 64))],
            dest: Place::local(0),
            target: None,
            span: SourceSpan::binary_address(0x1014),
            atomic: None,
        };

        let mem_vcs = generate_memory_model_vcs(&lifted);
        assert!(
            !mem_vcs.iter().any(|vc| matches!(&vc.kind, VcKind::FormatStringViolation { .. })),
            "constant printf format pointer should not emit format-string violation VC"
        );
    }

    #[test]
    fn test_generate_memory_model_vcs_missing_read_fact_fails_closed() {
        let mut lifted = make_mem_lifted();
        lifted.trust_ir_body.blocks[0].stmts.insert(
            0,
            Statement::Assign {
                place: Place::local(1),
                rvalue: Rvalue::Use(Operand::Symbolic(test_mem_read(Formula::Var(
                    "missing_read_addr".into(),
                    Sort::BitVec(64),
                )))),
                span: SourceSpan {
                    file: "binary:0x2002".to_string(),
                    line_start: 0,
                    col_start: 0,
                    line_end: 0,
                    col_end: 0,
                },
            },
        );

        let mem_vcs = generate_memory_model_vcs(&lifted);
        let read_vc = mem_vcs
            .iter()
            .find(|vc| {
                matches!(&vc.kind, VcKind::Assertion { message } if message.contains("missing access fact"))
            })
            .expect("lifted memory read without access facts should produce fail-closed VC");

        assert_eq!(read_vc.location.file, "binary:0x2002");
        assert_eq!(read_vc.formula, Formula::Bool(true));
    }

    #[test]
    fn test_generate_memory_model_vcs_partial_trace_missing_read_fact_fails_closed() {
        let mut lifted = make_mem_lifted();
        lifted.trust_ir_body.blocks[0].stmts.insert(
            0,
            Statement::Assign {
                place: Place::local(1),
                rvalue: Rvalue::Use(Operand::Symbolic(test_mem_read(Formula::Var(
                    "partial_trace_read_addr".into(),
                    Sort::BitVec(64),
                )))),
                span: SourceSpan::binary_address(0x2002),
            },
        );
        lifted.memory_accesses = vec![MemoryAccessFact {
            origin: test_binary_origin(0x2010),
            kind: MemoryAccessKind::Write,
            address: Formula::Var("covered_write_addr".into(), Sort::BitVec(64)),
            width_bytes: 8,
            endianness: Endianness::Little,
            region: MemoryRegionKind::Stack,
            base_object: Some("stack_frame".to_string()),
            offset: Some(Formula::Int(-16)),
            extent: None,
            provenance: Some("partial recovered memory trace".to_string()),
            taint: vec![],
        }];

        let mem_vcs = generate_memory_model_vcs(&lifted);
        let read_vc = mem_vcs
            .iter()
            .find(|vc| {
                matches!(&vc.kind, VcKind::Assertion { message } if message.contains("memory read missing access fact"))
            })
            .expect("partial traces must fail closed for uncovered recovered reads");

        assert_eq!(read_vc.location.file, "binary:0x2002");
        assert_eq!(read_vc.formula, Formula::Bool(true));
    }

    #[test]
    fn test_generate_memory_model_vcs_partial_trace_missing_write_fact_fails_closed() {
        let mut lifted = make_mem_lifted();
        lifted.memory_accesses = vec![MemoryAccessFact {
            origin: test_binary_origin(0x2008),
            kind: MemoryAccessKind::Read,
            address: Formula::Var("covered_read_addr".into(), Sort::BitVec(64)),
            width_bytes: 8,
            endianness: Endianness::Little,
            region: MemoryRegionKind::Stack,
            base_object: Some("stack_frame".to_string()),
            offset: Some(Formula::Int(-16)),
            extent: None,
            provenance: Some("partial recovered memory trace".to_string()),
            taint: vec![],
        }];

        let mem_vcs = generate_memory_model_vcs(&lifted);
        let write_vc = mem_vcs
            .iter()
            .find(|vc| {
                matches!(&vc.kind, VcKind::Assertion { message } if message.contains("memory write missing access fact"))
            })
            .expect("partial traces must fail closed for uncovered recovered writes");

        assert_eq!(write_vc.location.file, "binary:0x2000");
        assert_eq!(write_vc.formula, Formula::Bool(true));
    }

    #[test]
    fn test_generate_memory_model_vcs_partial_trace_matching_write_fact_is_covered() {
        let mut lifted = make_mem_lifted();
        lifted.memory_accesses = vec![MemoryAccessFact {
            origin: test_binary_origin(0x2000),
            kind: MemoryAccessKind::Write,
            address: Formula::Var("write_addr".into(), Sort::BitVec(64)),
            width_bytes: 8,
            endianness: Endianness::Little,
            region: MemoryRegionKind::Stack,
            base_object: Some("stack_frame".to_string()),
            offset: Some(Formula::Int(-16)),
            extent: None,
            provenance: Some("complete recovered memory trace".to_string()),
            taint: vec![],
        }];

        let mem_vcs = generate_memory_model_vcs(&lifted);

        assert!(
            !mem_vcs.iter().any(|vc| {
                matches!(&vc.kind, VcKind::Assertion { message } if message.contains("memory write missing access fact"))
            }),
            "same-kind access fact at the recovered write address should cover the TrustIr store"
        );
        assert!(
            mem_vcs.iter().any(|vc| {
                matches!(&vc.kind, VcKind::Assertion { message } if message.contains("binary memory write OOB"))
            }),
            "covered write facts should still emit their ordinary memory safety VC"
        );
    }

    #[test]
    fn test_detect_memory_local_uses_x86_64_mem_decl() {
        let layout = LocalLayout::x86_64();
        let expected_mem = layout.mem_local;
        let lifted = make_mem_lifted_with_layout(layout, "test_x86_mem", 0x2400);

        assert_eq!(detect_memory_local(&lifted), Some(expected_mem));
        assert_ne!(detect_memory_local(&lifted), Some(LocalLayout::standard().mem_local));
    }

    #[test]
    fn test_generate_memory_model_vcs_x86_64_mem_write() {
        let layout = LocalLayout::x86_64();
        let lifted = make_mem_lifted_with_layout(layout, "test_x86_mem", 0x2400);
        let mem_vcs = generate_memory_model_vcs(&lifted);

        let oob_vcs: Vec<_> = mem_vcs
            .iter()
            .filter(|vc| {
                matches!(&vc.kind, VcKind::Assertion { message } if message.contains("memory write OOB"))
            })
            .collect();

        assert_eq!(oob_vcs.len(), 1, "should produce OOB VC for x86_64 MEM local");
        assert_eq!(oob_vcs[0].location.file, "binary:0x2400");
    }

    #[test]
    fn test_detect_memory_local_from_store_formula_without_mem_name() {
        let layout = LocalLayout::x86_64();
        let mem_idx = layout.mem_local;
        let mut lifted = make_mem_lifted_with_layout(layout, "test_x86_mem_store", 0x2500);
        lifted.trust_ir_body.locals = vec![
            LocalDecl { index: 0, ty: Ty::Int { width: 64, signed: false }, name: None },
            LocalDecl { index: mem_idx, ty: Ty::Int { width: 64, signed: false }, name: None },
        ];

        let store_formula = Formula::Store(
            Box::new(test_mem_array()),
            Box::new(Formula::Var("addr".into(), Sort::BitVec(64))),
            Box::new(Formula::Var("val".into(), Sort::BitVec(8))),
        );

        match &mut lifted.trust_ir_body.blocks[0].stmts[0] {
            Statement::Assign { rvalue, .. } => {
                *rvalue = Rvalue::Use(Operand::Symbolic(store_formula));
            }
            _ => panic!("expected memory assignment"),
        }

        assert_eq!(detect_memory_local(&lifted), Some(mem_idx));
    }

    #[test]
    fn test_generate_memory_model_vcs_stack_discipline() {
        let lifted = make_mem_lifted();
        let mem_vcs = generate_memory_model_vcs(&lifted);

        let sp_vcs: Vec<_> = mem_vcs.iter()
            .filter(|vc| {
                matches!(&vc.kind, VcKind::Assertion { message } if message.contains("stack pointer not restored"))
            })
            .collect();
        assert!(
            !sp_vcs.is_empty(),
            "should produce stack pointer restoration VCs for return blocks"
        );
    }

    #[test]
    fn test_generate_memory_model_vcs_stack_uses_lifted_sp_assignment() {
        let mut lifted = make_mem_lifted();
        let sp_formula = Formula::Var("SP_after_lifted_assignment".into(), Sort::BitVec(64));
        lifted.trust_ir_body.blocks[0].stmts.push(Statement::Assign {
            place: Place::local(LocalLayout::standard().sp_local),
            rvalue: Rvalue::Use(Operand::Symbolic(sp_formula)),
            span: SourceSpan {
                file: "binary:0x2004".to_string(),
                line_start: 0,
                col_start: 0,
                line_end: 0,
                col_end: 0,
            },
        });

        let mem_vcs = generate_memory_model_vcs(&lifted);
        let sp_vc = mem_vcs
            .iter()
            .find(|vc| {
                matches!(&vc.kind, VcKind::Assertion { message } if message.contains("stack pointer not restored"))
            })
            .expect("should produce stack pointer restoration VC");

        assert!(
            formula_contains_var_name(&sp_vc.formula, "SP_after_lifted_assignment"),
            "stack VC should use the lifted SP assignment formula"
        );
        assert!(
            !formula_contains_var_prefix(&sp_vc.formula, &generated_lift_symbol("return_sp_bb"),),
            "stack VC should not fall back when a lifted SP assignment is available"
        );
        assert_eq!(
            sp_vc.location.file, "binary:0x2004",
            "stack VC should point at the lifted SP assignment when no return instruction span exists"
        );
    }

    #[test]
    fn test_generate_memory_model_vcs_empty_function() {
        // A function with no memory ops and no return blocks should produce no memory VCs.
        let mut cfg = Cfg::new();
        cfg.add_block(LiftedBlock {
            id: 0,
            start_addr: 0x3000,
            instructions: vec![],
            successors: vec![],
            is_return: true,
        });

        let body = VerifiableBody {
            locals: vec![LocalDecl {
                index: 0,
                ty: Ty::Int { width: 64, signed: false },
                name: None,
            }],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Return,
            }],
            arg_count: 0,
            return_ty: Ty::Int { width: 64, signed: false },
        };

        let lifted = LiftedFunction {
            name: "empty_fn".to_string(),
            entry_point: 0x3000,
            cfg,
            trust_ir_body: body,
            ssa: None,
            annotations: vec![],
            memory_accesses: vec![],
            trust_level: trust_types::TrustLevel::Partial,
            unsupported: trust_types::UnsupportedLedger::default(),
        };

        let mem_vcs = generate_memory_model_vcs(&lifted);
        // Only stack pointer VC (from the Return terminator), no memory OOB.
        let oob_vcs: Vec<_> = mem_vcs
            .iter()
            .filter(
                |vc| matches!(&vc.kind, VcKind::Assertion { message } if message.contains("OOB")),
            )
            .collect();
        assert!(oob_vcs.is_empty(), "empty function should not produce OOB VCs");

        let sp_vcs: Vec<_> = mem_vcs.iter()
            .filter(|vc| {
                matches!(&vc.kind, VcKind::Assertion { message } if message.contains("stack pointer"))
            })
            .collect();
        assert_eq!(sp_vcs.len(), 1, "should produce exactly one SP restoration VC");
    }

    #[test]
    fn test_binary_vcs_include_both_standard_and_memory() {
        let lifted = make_mem_lifted();
        let all_vcs = generate_binary_vcs(&lifted);

        // Should have both standard VCs (from the VC pipeline) and memory model VCs.
        let mem_vcs = generate_memory_model_vcs(&lifted);
        assert!(
            all_vcs.len() >= mem_vcs.len(),
            "total VCs should include at least the memory model VCs"
        );
    }

    #[test]
    fn test_generate_binary_abi_contradiction_vcs_conflicting_parameter_and_return_storage() {
        let param_subject =
            BinaryFactSubject::Parameter { function: "test_abi".to_string(), index: 0 };
        let return_subject =
            BinaryFactSubject::ReturnValue { function: "test_abi".to_string(), index: 0 };
        let abi_facts = vec![
            proof_grade_abi(
                param_subject.clone(),
                BinaryAbiFactKind::Parameter { index: 0, location: register_location("RDI") },
                BinaryFactEvidence::Validation,
            ),
            proof_grade_abi(
                return_subject.clone(),
                BinaryAbiFactKind::Return { index: 0, location: register_location("RAX") },
                BinaryFactEvidence::Validation,
            ),
        ];
        let storage_facts = vec![
            proof_grade_storage(
                param_subject,
                register_location("RSI"),
                BinaryFactEvidence::DebugInfo,
            ),
            proof_grade_storage(
                return_subject,
                register_location("RDX"),
                BinaryFactEvidence::DebugInfo,
            ),
        ];

        let vcs = generate_binary_abi_contradiction_vcs(
            "test_abi",
            SourceSpan::binary_address(0x2000),
            &abi_facts,
            &storage_facts,
        );

        assert_eq!(vcs.len(), 2);
        assert!(vcs.iter().all(|vc| vc.formula == Formula::Bool(true)));
        assert!(vcs.iter().all(|vc| vc.kind.proof_level() == trust_types::ProofLevel::L0Safety));
        assert!(vcs.iter().all(|vc| !vc.kind.has_runtime_fallback(true)));
        assert!(vcs.iter().any(|vc| {
            matches!(&vc.kind, VcKind::BinaryAbiContradiction { fact, evidence }
                if fact.contains("parameter 0") && evidence.contains("RDI") && evidence.contains("RSI"))
        }));
        assert!(vcs.iter().any(|vc| {
            matches!(&vc.kind, VcKind::BinaryAbiContradiction { fact, evidence }
                if fact.contains("return 0") && evidence.contains("RAX") && evidence.contains("RDX"))
        }));
    }

    #[test]
    fn test_generate_binary_abi_contradiction_vcs_matching_storage_is_normal() {
        let subject = BinaryFactSubject::Parameter { function: "test_abi".to_string(), index: 0 };
        let location = register_location("RDI");
        let abi_facts = vec![proof_grade_abi(
            subject.clone(),
            BinaryAbiFactKind::Parameter { index: 0, location: location.clone() },
            BinaryFactEvidence::Validation,
        )];
        let storage_facts =
            vec![proof_grade_storage(subject, location, BinaryFactEvidence::DebugInfo)];

        let vcs = generate_binary_abi_contradiction_vcs(
            "test_abi",
            SourceSpan::binary_address(0x2000),
            &abi_facts,
            &storage_facts,
        );

        assert!(vcs.is_empty(), "matching proof-grade ABI/storage facts are not contradictions");
    }

    #[test]
    fn test_generate_binary_abi_contradiction_vcs_unknown_and_assumption_not_proof_grade() {
        let subject = BinaryFactSubject::Parameter { function: "test_abi".to_string(), index: 0 };
        let unknown_abi = proof_grade_abi(
            subject.clone(),
            BinaryAbiFactKind::Parameter { index: 0, location: register_location("RDI") },
            BinaryFactEvidence::Unknown,
        );
        let assumption_storage =
            proof_grade_storage(subject, register_location("RSI"), BinaryFactEvidence::Assumption);

        let vcs = generate_binary_abi_contradiction_vcs(
            "test_abi",
            SourceSpan::binary_address(0x2000),
            &[unknown_abi],
            &[assumption_storage],
        );

        assert!(vcs.is_empty(), "unknown/assumption facts are not proof-grade evidence");
    }

    #[test]
    fn test_x86_64_empty_unsupported_ledger_slice_emits_no_unsupported_vcs() {
        let lifted = make_x86_64_empty_unsupported_ledger_slice();

        assert!(
            lifted.unsupported.is_empty(),
            "selected x86_64 no-data slice artifact must carry an empty unsupported ledger"
        );
        assert!(
            generate_unsupported_ledger_vcs(&lifted).is_empty(),
            "empty artifact ledger must not synthesize verification unsupported-ledger VCs"
        );

        let vcs = generate_binary_vcs(&lifted);
        assert!(
            vcs.iter().all(|vc| !matches!(vc.kind, VcKind::UnsupportedMir { .. })),
            "selected no-data slice should not produce UnsupportedMir VCs: {vcs:#?}"
        );
    }

    #[test]
    fn test_x86_64_unsupported_semantic_ledger_record_emits_fail_closed_vc() {
        let mut lifted = make_x86_64_empty_unsupported_ledger_slice();
        lifted.name = "x86_64_syscall_blocker".to_string();
        lifted.unsupported = trust_types::UnsupportedLedger {
            records: vec![x86_64_semantic_unsupported_record(
                0x401020,
                "Syscall",
                "x86_64 syscall boundary semantics are unsupported fail-closed: proof-consumed syscall/ABI witnesses are missing",
            )],
        };

        let vcs = generate_unsupported_ledger_vcs(&lifted);

        assert_eq!(vcs.len(), 1);
        assert_eq!(vcs[0].function, "x86_64_syscall_blocker");
        assert_eq!(vcs[0].location.file, "binary:0x401020");
        assert_eq!(vcs[0].formula, Formula::Bool(true));
        assert!(matches!(
            &vcs[0].kind,
            VcKind::UnsupportedMir { kind, detail }
                if kind == "BinaryInstructionSemantics"
                    && detail.contains("arch=x86_64")
                    && detail.contains("opcode=Syscall")
                    && detail.contains("proof-consumed syscall/ABI witnesses are missing")
        ));
        assert!(!vcs[0].kind.has_runtime_fallback(true));
    }

    #[test]
    fn test_aarch64_empty_unsupported_ledger_selected_slice_consumes_boundary_certificate() {
        let mut lifted = make_test_lifted();
        lifted.name = "aarch64_selected_release_acquire_accepted".to_string();
        lifted.memory_accesses = aarch64_selected_release_acquire_accesses(0x2270, 0x2274);

        assert!(
            lifted.unsupported.is_empty(),
            "accepted AArch64 selected slice starts with an empty unsupported ledger"
        );
        let release_provenance = lifted.memory_accesses[0].provenance.as_deref().unwrap();
        let acquire_provenance = lifted.memory_accesses[1].provenance.as_deref().unwrap();
        let selected_image_digest = aarch64_release_acquire_selected_image_digest(
            &lifted,
            &lifted.memory_accesses[0],
            &lifted.memory_accesses[1],
        );
        let expected_release_id = aarch64_release_acquire_evidence_id(
            "release",
            &selected_image_digest,
            &aarch64_instruction_provenance_digest(&lifted.memory_accesses[0].origin),
            &aarch64_memory_access_digest(&lifted.memory_accesses[0]),
        );
        let expected_acquire_id = aarch64_release_acquire_evidence_id(
            "acquire",
            &selected_image_digest,
            &aarch64_instruction_provenance_digest(&lifted.memory_accesses[1].origin),
            &aarch64_memory_access_digest(&lifted.memory_accesses[1]),
        );
        assert_eq!(
            aarch64_provenance_value(release_provenance, "evidence_schema"),
            Some(AARCH64_RELEASE_ACQUIRE_EVIDENCE_SCHEMA)
        );
        assert_eq!(
            aarch64_provenance_value(release_provenance, "artifact_row_schema"),
            Some(AARCH64_ORDERING_MONITOR_EVIDENCE_ROW_SCHEMA)
        );
        assert_eq!(
            aarch64_provenance_value(release_provenance, "artifact_row_type"),
            Some(AARCH64_ORDERING_MONITOR_EVIDENCE_ROW_TYPE)
        );
        assert_eq!(
            aarch64_provenance_value(release_provenance, "artifact_row_status"),
            Some("accepted")
        );
        assert_eq!(
            aarch64_provenance_value(release_provenance, "evidence_id"),
            Some(expected_release_id.as_str())
        );
        assert_eq!(
            aarch64_provenance_value(acquire_provenance, "evidence_id"),
            Some(expected_acquire_id.as_str())
        );
        let expected_selected_image_digest = format!("sha256:{selected_image_digest}");
        assert_eq!(
            aarch64_provenance_value(release_provenance, "selected_image_digest"),
            Some(expected_selected_image_digest.as_str())
        );
        assert_eq!(
            aarch64_provenance_value(release_provenance, "unsupported_ledger_boundary"),
            Some("explicit-empty")
        );
        assert_eq!(
            aarch64_provenance_value(release_provenance, "unsupported_ledger_records"),
            Some("0")
        );
        assert_eq!(aarch64_provenance_value(release_provenance, "opcode"), Some("Stlr"));
        assert_eq!(aarch64_provenance_value(release_provenance, "ordering"), Some("Release"));
        assert_eq!(
            aarch64_provenance_value(release_provenance, "ordering_event"),
            Some("release ordering event")
        );
        assert_eq!(
            aarch64_provenance_value(release_provenance, "happens_before_witness"),
            Some("absent-reviewed")
        );
        assert_eq!(
            aarch64_provenance_value(release_provenance, "exclusive_monitor_witness"),
            Some("not-applicable-reviewed")
        );
        assert_eq!(
            aarch64_provenance_value(release_provenance, "store_conditional_status"),
            Some("not-applicable-reviewed")
        );
        assert_eq!(
            aarch64_provenance_value(release_provenance, "reviewed_unsupported_absence"),
            Some(AARCH64_REVIEWED_UNSUPPORTED_ABSENCE)
        );
        assert_eq!(
            aarch64_provenance_value(
                release_provenance,
                "aarch64_ordering_monitor_evidence_schema"
            ),
            Some(AARCH64_ORDERING_MONITOR_EVIDENCE_ROW_SCHEMA)
        );
        assert_eq!(
            aarch64_provenance_value(
                release_provenance,
                "aarch64_ordering_monitor_evidence_status"
            ),
            Some("accepted")
        );
        assert_eq!(
            aarch64_provenance_value(
                release_provenance,
                "aarch64_ordering_monitor_evidence_opcode"
            ),
            Some("Stlr")
        );
        assert_eq!(
            aarch64_provenance_value(
                release_provenance,
                "aarch64_ordering_monitor_evidence_ordering"
            ),
            Some("Release")
        );
        assert_eq!(
            aarch64_provenance_value(
                release_provenance,
                "aarch64_ordering_monitor_evidence_exclusive_monitor"
            ),
            Some("None")
        );
        let expected_release_digest =
            format!("sha256:{}", &expected_release_id["aarch64-ra:sha256:".len()..]);
        assert_eq!(
            aarch64_provenance_value(
                release_provenance,
                "aarch64_ordering_monitor_evidence_digest"
            ),
            Some(expected_release_digest.as_str())
        );
        assert_eq!(
            aarch64_provenance_value(release_provenance, "release_transcript_consumed"),
            Some("true")
        );
        assert_eq!(
            aarch64_provenance_value(release_provenance, "release_transcript_digest"),
            Some(expected_release_digest.as_str())
        );
        assert_eq!(aarch64_provenance_value(acquire_provenance, "opcode"), Some("Ldar"));
        assert_eq!(aarch64_provenance_value(acquire_provenance, "ordering"), Some("Acquire"));
        assert_eq!(
            aarch64_provenance_value(
                acquire_provenance,
                "aarch64_ordering_monitor_evidence_opcode"
            ),
            Some("Ldar")
        );
        assert!(
            generate_aarch64_selected_slice_boundary_vcs(&lifted).is_empty(),
            "proof-consumed ordering facts and reviewed absence certificates discharge the boundary"
        );

        let vcs = generate_binary_vcs(&lifted);
        assert!(
            vcs.iter().all(|vc| {
                !matches!(
                    &vc.kind,
                    VcKind::UnsupportedMir { kind, .. }
                        if kind == "AArch64SelectedSliceBoundaryNotProofConsumed"
                )
            }),
            "accepted selected slice must not emit an AArch64 boundary VC: {vcs:#?}"
        );
    }

    #[test]
    fn test_aarch64_selected_slice_evidence_id_is_stable_and_rejects_stale_provenance() {
        let mut lifted = make_test_lifted();
        lifted.name = "aarch64_selected_release_acquire_stable_evidence".to_string();
        lifted.memory_accesses = aarch64_selected_release_acquire_accesses(0x2280, 0x2284);

        let selected_image_digest = aarch64_release_acquire_selected_image_digest(
            &lifted,
            &lifted.memory_accesses[0],
            &lifted.memory_accesses[1],
        );
        let release_id = aarch64_release_acquire_evidence_id(
            "release",
            &selected_image_digest,
            &aarch64_instruction_provenance_digest(&lifted.memory_accesses[0].origin),
            &aarch64_memory_access_digest(&lifted.memory_accesses[0]),
        );
        let release_id_repeat = aarch64_release_acquire_evidence_id(
            "release",
            &selected_image_digest,
            &aarch64_instruction_provenance_digest(&lifted.memory_accesses[0].origin),
            &aarch64_memory_access_digest(&lifted.memory_accesses[0]),
        );
        assert_eq!(release_id, release_id_repeat);

        let mut stale = make_test_lifted();
        stale.name = "aarch64_selected_release_acquire_stale_evidence".to_string();
        stale.memory_accesses = lifted.memory_accesses.clone();
        stale.memory_accesses[0].origin.instruction_address += 4;
        let stale_selected_image_digest = aarch64_release_acquire_selected_image_digest(
            &stale,
            &stale.memory_accesses[0],
            &stale.memory_accesses[1],
        );
        let stale_release_id = aarch64_release_acquire_evidence_id(
            "release",
            &stale_selected_image_digest,
            &aarch64_instruction_provenance_digest(&stale.memory_accesses[0].origin),
            &aarch64_memory_access_digest(&stale.memory_accesses[0]),
        );
        assert_ne!(release_id, stale_release_id);

        let vcs = generate_aarch64_selected_slice_boundary_vcs(&stale);
        assert_eq!(vcs.len(), 1);
        assert!(matches!(
            &vcs[0].kind,
            VcKind::UnsupportedMir { kind, detail }
                if kind == "AArch64SelectedSliceBoundaryNotProofConsumed"
                    && detail.contains("release evidence_id=")
                    && detail.contains("selected_image_digest")
                    && detail.contains("evidence_identifiers=[")
        ));
    }

    #[test]
    fn test_aarch64_selected_slice_requires_explicit_empty_unsupported_ledger_boundary() {
        let mut lifted = make_test_lifted();
        lifted.name = "aarch64_selected_release_acquire_nonempty_ledger".to_string();
        lifted.memory_accesses = aarch64_selected_release_acquire_accesses(0x2290, 0x2294);
        lifted.unsupported = trust_types::UnsupportedLedger {
            records: vec![aarch64_atomic_record(0x2298, "ldaxr")],
        };

        let vcs = generate_aarch64_selected_slice_boundary_vcs(&lifted);
        assert_eq!(vcs.len(), 1);
        assert!(matches!(
            &vcs[0].kind,
            VcKind::UnsupportedMir { kind, detail }
                if kind == "AArch64SelectedSliceBoundaryNotProofConsumed"
                    && detail.contains("unsupported-ledger-empty boundary")
                    && detail.contains("unsupported ledger is empty only")
        ));
    }

    #[test]
    fn test_aarch64_selected_slice_missing_ordering_or_monitor_witness_fails_closed() {
        let mut lifted = make_test_lifted();
        lifted.name = "aarch64_selected_release_acquire_missing_witness".to_string();
        let mut accesses = aarch64_selected_release_acquire_accesses(0x22a0, 0x22a4);
        accesses[0].provenance = accesses[0].provenance.take().map(|provenance| {
            provenance
                .replace("release ordering event", "release-ordering-event-missing")
                .replace("exclusive_monitor=None", "exclusive_monitor missing")
                .replace("happens_before_witness=absent-reviewed", "happens_before_witness=missing")
        });
        lifted.memory_accesses = accesses;

        let vcs = generate_aarch64_selected_slice_boundary_vcs(&lifted);

        assert_eq!(vcs.len(), 1);
        assert_eq!(vcs[0].function, "aarch64_selected_release_acquire_missing_witness");
        assert_eq!(vcs[0].formula, Formula::Bool(true));
        assert!(matches!(
            &vcs[0].kind,
            VcKind::UnsupportedMir { kind, detail }
                if kind == "AArch64SelectedSliceBoundaryNotProofConsumed"
                    && detail.contains("release release ordering event")
                    && detail.contains("release exclusive_monitor=None")
                    && detail.contains("release happens_before_witness=absent-reviewed")
                    && detail.contains("release release_transcript_digest=")
                    && detail.contains("unsupported ledger is empty only")
        ));
        assert!(!vcs[0].kind.has_runtime_fallback(true));
    }

    #[test]
    fn test_aarch64_selected_slice_unsupported_boundary_facts_fail_closed() {
        let cases = [
            (
                "Dmb",
                "AArch64 synchronization boundary modeled as explicit partial unsupported-ledger boundary; ordering=LoadsAndStores",
                "synchronization boundary",
            ),
            (
                "Mrs",
                "AArch64 system register semantics are unsupported fail-closed: proof-consumed system-register witnesses are missing",
                "system register",
            ),
            (
                "Fadd",
                "AArch64 FP/SIMD semantics are unsupported fail-closed: proof-consumed FP/SIMD witnesses are missing",
                "FP/SIMD",
            ),
            (
                "Brk",
                "AArch64 trap semantics are unsupported fail-closed: proof-consumed syscall/trap witnesses are missing",
                "trap",
            ),
            (
                "Svc",
                "AArch64 syscall/trap semantics are unsupported fail-closed: proof-consumed syscall/trap witnesses are missing",
                "syscall/trap",
            ),
        ];

        for (opcode, feature, expected_detail) in cases {
            let mut lifted = make_test_lifted();
            lifted.name = format!("aarch64_selected_release_acquire_with_{opcode}");
            lifted.memory_accesses = aarch64_selected_release_acquire_accesses(0x22b0, 0x22b4);
            lifted.unsupported = trust_types::UnsupportedLedger {
                records: vec![aarch64_unsupported_record(0x22b8, opcode, feature)],
            };

            let vcs = generate_aarch64_selected_slice_boundary_vcs(&lifted);

            assert_eq!(vcs.len(), 1, "{opcode}");
            assert!(matches!(
                &vcs[0].kind,
                VcKind::UnsupportedMir { kind, detail }
                    if kind == "AArch64SelectedSliceBoundaryNotProofConsumed"
                        && detail.contains("unsupported-ledger-empty boundary")
                        && detail.contains(&format!("opcode={opcode}"))
                        && detail.contains(expected_detail)
            ));
            assert_eq!(vcs[0].formula, Formula::Bool(true));
            assert!(!vcs[0].kind.has_runtime_fallback(true));
        }
    }

    #[test]
    fn test_aarch64_atomic_semantic_fact_emits_unsupported_vc_until_proof_consumed() {
        let mut lifted = make_test_lifted();
        lifted.name = "aarch64_atomic_ldaxr".to_string();
        lifted.unsupported = trust_types::UnsupportedLedger {
            records: vec![aarch64_atomic_record(0x2210, "ldaxr")],
        };

        let vcs = generate_unsupported_ledger_vcs(&lifted);

        assert_eq!(vcs.len(), 1);
        assert_eq!(vcs[0].function, "aarch64_atomic_ldaxr");
        assert_eq!(vcs[0].location.file, "binary:0x2210");
        assert_eq!(vcs[0].formula, Formula::Bool(true));
        assert!(matches!(
            &vcs[0].kind,
            VcKind::UnsupportedMir { kind, detail }
                if kind == "AArch64AtomicSemanticFactNotProofConsumed"
                    && detail.contains("opcode=ldaxr")
                    && detail.contains(&format!(
                        "evidence_schema={AARCH64_ATOMIC_OBLIGATION_EVIDENCE_SCHEMA}"
                    ))
                    && detail.contains("evidence_id=aarch64-atomic:sha256:")
                    && detail.contains("artifact_digest=sha256:")
                    && detail.contains("instruction_provenance_digest=sha256:")
                    && detail.contains("memory_access_facts_digest=sha256:")
                    && detail.contains("not proof-consumed")
                    && detail.contains("acquire ordering event")
                    && detail.contains("exclusive-monitor reservation state")
                    && detail.contains("happens-before witness")
                    && detail.contains("exclusive_monitor=LoadReserve")
                    && detail.contains("exclusive forms remain fail-closed")
        ));
        assert!(!vcs[0].kind.has_runtime_fallback(true));
    }

    #[test]
    fn test_aarch64_ldar_stlr_atomic_metadata_emits_unsupported_vcs() {
        let mut lifted = make_test_lifted();
        lifted.name = "aarch64_atomic_acquire_release".to_string();
        lifted.unsupported = trust_types::UnsupportedLedger {
            records: vec![
                aarch64_atomic_record(0x2230, "ldar"),
                aarch64_atomic_record(0x2234, "stlr"),
            ],
        };

        let vcs = generate_unsupported_ledger_vcs(&lifted);

        assert_eq!(vcs.len(), 2);
        let ldar_vc = vcs
            .iter()
            .find(|vc| {
                matches!(
                    &vc.kind,
                    VcKind::UnsupportedMir { detail, .. } if detail.contains("opcode=ldar")
                )
            })
            .expect("LDAR metadata must become an unsupported VC");
        let stlr_vc = vcs
            .iter()
            .find(|vc| {
                matches!(
                    &vc.kind,
                    VcKind::UnsupportedMir { detail, .. } if detail.contains("opcode=stlr")
                )
            })
            .expect("STLR metadata must become an unsupported VC");

        assert_eq!(ldar_vc.location.file, "binary:0x2230");
        assert_eq!(stlr_vc.location.file, "binary:0x2234");
        assert_eq!(ldar_vc.formula, Formula::Bool(true));
        assert_eq!(stlr_vc.formula, Formula::Bool(true));
        match &ldar_vc.kind {
            VcKind::UnsupportedMir { kind, detail } => {
                assert_eq!(kind, "AArch64AtomicSemanticFactNotProofConsumed");
                assert!(detail.contains("proof obligation: consume AArch64 acquire ordering"));
                assert!(detail.contains("access=Read"));
                assert!(detail.contains("ordering=Acquire"));
                assert!(detail.contains("exclusive_monitor=None"));
                assert!(detail.contains("synchronization edge"));
                assert!(detail.contains("thread identity"));
                assert!(detail.contains("happens-before witness"));
            }
            _ => unreachable!(),
        }
        match &stlr_vc.kind {
            VcKind::UnsupportedMir { kind, detail } => {
                assert_eq!(kind, "AArch64AtomicSemanticFactNotProofConsumed");
                assert!(detail.contains("proof obligation: consume AArch64 release ordering"));
                assert!(detail.contains("access=Write"));
                assert!(detail.contains("ordering=Release"));
                assert!(detail.contains("exclusive_monitor=None"));
                assert!(detail.contains("synchronization edge"));
                assert!(detail.contains("thread identity"));
                assert!(detail.contains("happens-before witness"));
            }
            _ => unreachable!(),
        }
        assert!(!ldar_vc.kind.has_runtime_fallback(true));
        assert!(!stlr_vc.kind.has_runtime_fallback(true));
    }

    #[test]
    fn test_aarch64_ldar_stlr_scalar_memory_accesses_do_not_silence_atomic_vcs() {
        let mut lifted = make_test_lifted();
        lifted.name = "aarch64_atomic_scalar_data_plane".to_string();
        lifted.memory_accesses = vec![
            aarch64_memory_access(0x2240, MemoryAccessKind::Read),
            aarch64_memory_access(0x2244, MemoryAccessKind::Write),
        ];
        lifted.unsupported = trust_types::UnsupportedLedger {
            records: vec![
                aarch64_atomic_record(0x2240, "ldar"),
                aarch64_atomic_record(0x2244, "stlr"),
            ],
        };

        let vcs = generate_binary_vcs(&lifted);
        let atomic_unsupported = vcs
            .iter()
            .filter(|vc| {
                matches!(
                    &vc.kind,
                    VcKind::UnsupportedMir { kind, detail }
                        if kind == "AArch64AtomicSemanticFactNotProofConsumed"
                            && (detail.contains("opcode=ldar") || detail.contains("opcode=stlr"))
                )
            })
            .collect::<Vec<_>>();
        let scalar_memory = vcs
            .iter()
            .filter(|vc| {
                matches!(
                    &vc.kind,
                    VcKind::Assertion { message }
                        if message.contains("memory read") || message.contains("memory write")
                )
            })
            .count();

        assert_eq!(
            atomic_unsupported.len(),
            2,
            "LDAR/STLR ordering metadata must remain visible as unsupported VCs"
        );
        assert!(
            scalar_memory >= 2,
            "scalar memory-access VCs may coexist but must not discharge ordering metadata"
        );
        for vc in atomic_unsupported {
            assert_eq!(vc.formula, Formula::Bool(true));
            assert!(!vc.kind.has_runtime_fallback(true));
            if let VcKind::UnsupportedMir { detail, .. } = &vc.kind {
                assert!(detail.contains("not proof-consumed"));
                assert!(detail.contains("happens-before witness"));
            }
        }
    }

    #[test]
    fn test_aarch64_ldar_stlr_generated_vcs_include_fail_closed_consumer_evidence() {
        let mut lifted = make_test_lifted();
        lifted.name = "aarch64_atomic_consumer_evidence".to_string();
        lifted.unsupported = trust_types::UnsupportedLedger {
            records: vec![
                aarch64_atomic_record(0x2250, "stlr"),
                aarch64_atomic_record(0x2254, "ldar"),
            ],
        };

        let vcs = generate_binary_vcs(&lifted);
        let atomic_details = vcs
            .iter()
            .filter_map(|vc| match &vc.kind {
                VcKind::UnsupportedMir { kind, detail }
                    if kind == "AArch64AtomicSemanticFactNotProofConsumed" =>
                {
                    Some(detail.as_str())
                }
                _ => None,
            })
            .collect::<Vec<_>>();

        assert_eq!(atomic_details.len(), 2);
        for detail in atomic_details {
            assert!(
                detail.contains(&format!(
                    "evidence_schema={AARCH64_ATOMIC_OBLIGATION_EVIDENCE_SCHEMA}"
                ))
            );
            assert!(detail.contains("evidence_id=aarch64-atomic:sha256:"));
            assert!(detail.contains("artifact_digest=sha256:"));
            assert!(detail.contains("memory_access_facts_digest=sha256:"));
            assert!(detail.contains("vcgen proof consumer status=fail-closed"));
            assert!(detail.contains(
                "consumed_witnesses=[acquire ordering event, release ordering event, same atomic location witness]"
            ));
            assert!(detail.contains(
                "missing_witnesses=[cross-thread identity witness, happens-before witness, synchronization edge, thread identity]"
            ));
            assert!(detail.contains("AArch64 release/acquire obligation remains fail-closed"));
        }
    }

    #[test]
    fn test_aarch64_exclusive_monitor_generated_vc_blocks_on_unconsumed_monitor_witnesses() {
        let mut lifted = make_test_lifted();
        lifted.name = "aarch64_exclusive_monitor_consumer_evidence".to_string();
        lifted.unsupported = trust_types::UnsupportedLedger {
            records: vec![
                aarch64_atomic_record(0x2260, "ldaxr"),
                aarch64_atomic_record(0x2264, "stlxr"),
            ],
        };

        let vcs = generate_binary_vcs(&lifted);
        let atomic_details = vcs
            .iter()
            .filter_map(|vc| match &vc.kind {
                VcKind::UnsupportedMir { kind, detail }
                    if kind == "AArch64AtomicSemanticFactNotProofConsumed" =>
                {
                    Some(detail.as_str())
                }
                _ => None,
            })
            .collect::<Vec<_>>();

        assert_eq!(atomic_details.len(), 2);
        for detail in atomic_details {
            assert!(
                detail.contains(&format!(
                    "evidence_schema={AARCH64_ATOMIC_OBLIGATION_EVIDENCE_SCHEMA}"
                ))
            );
            assert!(detail.contains("evidence_id=aarch64-atomic:sha256:"));
            assert!(detail.contains("artifact_digest=sha256:"));
            assert!(detail.contains("memory_access_facts_digest=sha256:"));
            assert!(detail.contains("vcgen proof consumer status=fail-closed"));
            assert!(detail.contains(
                "consumed_witnesses=[acquire ordering event, happens-before witness, release ordering event, synchronization edge, thread identity]"
            ));
            assert!(detail.contains(
                "missing_witnesses=[exclusive-monitor invalidation, exclusive-monitor reservation state, store-conditional status result]"
            ));
            assert!(detail.contains("AArch64 exclusive-monitor obligation remains fail-closed"));
        }
    }

    #[test]
    fn test_aarch64_store_exclusive_status_fact_emits_unsupported_vc() {
        let mut lifted = make_test_lifted();
        lifted.name = "aarch64_atomic_stlxr".to_string();
        lifted.unsupported = trust_types::UnsupportedLedger {
            records: vec![aarch64_atomic_record(0x2220, "stlxr")],
        };

        let vcs = generate_binary_vcs(&lifted);
        let atomic_vc = vcs
            .iter()
            .find(|vc| {
                matches!(
                    &vc.kind,
                    VcKind::UnsupportedMir { kind, detail }
                        if kind == "AArch64AtomicSemanticFactNotProofConsumed"
                            && detail.contains("opcode=stlxr")
                )
            })
            .expect("STLXR semantic fact must remain visible as unsupported");

        assert_eq!(atomic_vc.formula, Formula::Bool(true));
        match &atomic_vc.kind {
            VcKind::UnsupportedMir { detail, .. } => {
                assert!(detail.contains("release ordering event"));
                assert!(detail.contains("store-conditional status result"));
                assert!(detail.contains("exclusive_monitor=StoreConditional"));
                assert!(detail.contains("reports_status=true"));
            }
            _ => unreachable!(),
        }
    }

    // Tests for LiftedFunction -> LiftedProgram adapter.

    #[test]
    fn test_lifted_to_legacy_preserves_entry_point() {
        let lifted = make_test_lifted();
        let legacy = lifted_to_legacy(&lifted);
        assert_eq!(legacy.entry_point, 0x1000);
    }

    #[test]
    fn test_lifted_to_legacy_creates_registers_from_locals() {
        let lifted = make_test_lifted();
        let legacy = lifted_to_legacy(&lifted);
        assert_eq!(
            legacy.registers.len(),
            lifted.trust_ir_body.locals.len(),
            "should have one register per local"
        );
        assert_eq!(legacy.registers[0].id, 0);
        assert_eq!(legacy.registers[1].name, "X0");
        assert_eq!(legacy.registers[2].name, "X1");
        assert_eq!(legacy.registers[0].width, 64);
    }

    #[test]
    fn test_lifted_to_legacy_produces_instructions() {
        let lifted = make_test_lifted();
        let legacy = lifted_to_legacy(&lifted);
        // One BinArith statement + one Return terminator
        assert!(
            legacy.instructions.len() >= 2,
            "should have at least 2 instructions (assign + return), got {}",
            legacy.instructions.len()
        );
    }

    #[test]
    fn test_lifted_to_legacy_binarith_op() {
        let lifted = make_test_lifted();
        let legacy = lifted_to_legacy(&lifted);

        let has_add = legacy.instructions.iter().any(|insn| {
            matches!(&insn.op, AbstractOp::BinArith { op: trust_types::BinOp::Add, .. })
        });
        assert!(has_add, "should have an Add instruction from the TrustIr body");
    }

    #[test]
    fn test_lifted_to_legacy_has_return() {
        let lifted = make_test_lifted();
        let legacy = lifted_to_legacy(&lifted);

        let has_ret =
            legacy.instructions.iter().any(|insn| matches!(&insn.op, AbstractOp::Return { .. }));
        assert!(has_ret, "should have a Return instruction");
    }

    #[test]
    fn test_generate_binary_vcs_opaque_control_flow_keeps_tainted_branch_family_visible() {
        let mut lifted = make_test_lifted();
        lifted.name = "opaque_binary_cf".to_string();
        lifted.cfg.blocks[0].is_return = false;
        lifted.cfg.add_block(LiftedBlock {
            id: 1,
            start_addr: 0x1100,
            instructions: vec![],
            successors: vec![],
            is_return: true,
        });
        lifted.trust_ir_body.blocks[0].terminator = Terminator::Opaque {
            kind: "UnresolvedBinaryControlFlow".to_string(),
            targets: vec![BlockId(1)],
            span: SourceSpan::binary_address(0x1004),
        };
        lifted.trust_ir_body.blocks.push(BasicBlock {
            id: BlockId(1),
            stmts: vec![],
            terminator: Terminator::Return,
        });

        let vcs = generate_binary_vcs(&lifted);
        let branch_vc = vcs
            .iter()
            .find(|vc| matches!(&vc.kind, VcKind::TaintedIndirectBranch { .. }))
            .expect("opaque binary control flow must emit a typed tainted-branch VC");

        assert_eq!(branch_vc.formula, Formula::Bool(true));
        assert_eq!(branch_vc.function, "opaque_binary_cf");
        assert_eq!(branch_vc.location.file, "binary:0x1004");
        assert_eq!(branch_vc.kind.proof_level(), trust_types::ProofLevel::L0Safety);
        assert!(!branch_vc.kind.has_runtime_fallback(true));
        match &branch_vc.kind {
            VcKind::TaintedIndirectBranch { sink_kind, target, evidence } => {
                assert_eq!(sink_kind, "indirect_branch");
                assert_eq!(target, "unresolved_opaque_target");
                assert!(evidence.contains("UnresolvedBinaryControlFlow"));
                assert!(evidence.contains("target taint unavailable"));
            }
            _ => unreachable!(),
        }
        assert!(
            vcs.iter().any(|vc| matches!(
                &vc.kind,
                VcKind::UnsupportedMir { kind, .. } if kind == "UnresolvedBinaryControlFlow"
            )),
            "the generic unsupported coverage gap should remain visible too"
        );
    }

    #[test]
    fn test_binary_security_family_counts_are_stable_for_tainted_indirect_control_slice() {
        let mut lifted = make_test_lifted();
        lifted.name = "tainted_indirect_family".to_string();
        lifted.cfg.blocks[0].is_return = false;
        lifted.cfg.add_block(LiftedBlock {
            id: 1,
            start_addr: 0x1200,
            instructions: vec![],
            successors: vec![],
            is_return: true,
        });
        lifted.trust_ir_body.blocks[0].terminator = Terminator::Opaque {
            kind: "UnresolvedBinaryControlFlow".to_string(),
            targets: vec![BlockId(1)],
            span: SourceSpan::binary_address(0x1004),
        };
        lifted.trust_ir_body.blocks.push(BasicBlock {
            id: BlockId(1),
            stmts: vec![],
            terminator: Terminator::Return,
        });

        let vcs = generate_binary_vcs(&lifted);
        let counts = binary_security_family_counts(&vcs);
        let branch_vcs: Vec<_> = vcs
            .iter()
            .filter(|vc| matches!(&vc.kind, VcKind::TaintedIndirectBranch { .. }))
            .collect();

        assert_eq!(branch_vcs.len(), 1);
        assert_eq!(counts.get("tainted_indirect_branch"), Some(&1));
        assert_eq!(counts.len(), 1);
        assert_binary_security_classification_blocker(
            branch_vcs[0],
            BinarySecurityVcFamily::TaintedIndirectBranch,
            BLOCKER_MISSING_INDIRECT_TARGET_TAINT,
        );
        assert_binary_security_classification_blocker(
            branch_vcs[0],
            BinarySecurityVcFamily::TaintedIndirectBranch,
            BLOCKER_UNRESOLVED_INDIRECT_CONTROL_TARGET,
        );
        let classification = classify_binary_security_vc(branch_vcs[0]).unwrap();
        assert!(classification.proof_grade_blockers.iter().any(|blocker| {
            blocker.detail.contains("target=unresolved_opaque_target")
                && blocker.detail.contains("target taint unavailable")
        }));
        assert_eq!(branch_vcs[0].kind.proof_level(), trust_types::ProofLevel::L0Safety);
        assert!(!branch_vcs[0].kind.has_runtime_fallback(true));
    }

    #[test]
    fn test_lifted_to_legacy_entry_point_in_instructions() {
        let lifted = make_test_lifted();
        let legacy = lifted_to_legacy(&lifted);

        let has_entry = legacy.instructions.iter().any(|insn| insn.address == legacy.entry_point);
        assert!(
            has_entry,
            "entry point 0x{:x} should be present in instructions",
            legacy.entry_point
        );
    }

    #[test]
    fn test_lifted_to_legacy_single_target_opaque_fails_closed() {
        let mut lifted = make_test_lifted();
        lifted.cfg.add_block(LiftedBlock {
            id: 1,
            start_addr: 0x1100,
            instructions: vec![],
            successors: vec![],
            is_return: true,
        });
        lifted.trust_ir_body.blocks[0].terminator = Terminator::Opaque {
            kind: "UnresolvedBinaryControlFlow".to_string(),
            targets: vec![BlockId(1)],
            span: SourceSpan::binary_address(0x1004),
        };
        lifted.trust_ir_body.blocks.push(BasicBlock {
            id: BlockId(1),
            stmts: vec![],
            terminator: Terminator::Return,
        });

        let legacy = lifted_to_legacy(&lifted);
        let opaque_insn = legacy
            .instructions
            .iter()
            .find(|insn| insn.address == 0x1004)
            .expect("opaque terminator should produce a legacy instruction");

        assert!(
            matches!(opaque_insn.op, AbstractOp::IndirectBranch { .. }),
            "single-target opaque control flow must not become a precise branch"
        );
        assert!(
            !legacy.instructions.iter().any(|insn| {
                matches!(
                    insn.op,
                    AbstractOp::Branch { target } if target == synthetic_block_address(0x1000, 1)
                )
            }),
            "legacy adapter must not encode opaque control flow as direct execution"
        );

        let err = crate::binary_analysis::lifter::lift_to_mir(&legacy)
            .expect_err("unresolved opaque control flow must fail closed");
        assert!(
            matches!(
                err,
                crate::binary_analysis::lifter::LiftError::UnresolvedIndirectBranch {
                    address: 0x1004
                }
            ),
            "expected unresolved indirect branch at opaque terminator, got {err:?}"
        );
    }
}
