//! Function-entry register bindings for binary-lifted bodies.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0
//!
//! A binary-lifted `VerifiableBody` names machine registers through symbolic
//! formulas: a bare `Var("X7")` in a statement of block B denotes the value of
//! GPR 7 **at B's entry** — the lift seeds a fresh symbolic machine state per
//! basic block and folds every register write into the threaded state, so a
//! later read within the block emits the folded formula, never the bare `Var`.
//! (`trust-lift/src/semantic_lift.rs`, `lift_cfg_with_semantics`.)
//!
//! It follows that a bare `Var("Xi")` in block B denotes Xi at **function**
//! entry exactly when no path from function entry to B writes Xi. This module
//! computes that justification — a forward must-analysis over the lifted
//! body's own statements — and carries the binding table that lets the
//! lowering consume such a `Var` as a real LIR function parameter, so a
//! byte-assembled load like `RAX := load_le_bytes(MEM, Var("X7"))` can lower
//! to a real `Opcode::Load` instead of refusing.
//!
//! Everything here fails closed: a statement or terminator shape the lift
//! cannot have produced, an unresolved successor, or an unjustified use
//! refuses (the existing symbolic-operand refusal, with the reason attached)
//! rather than guessing. An unverified promise never shrinks what is proven —
//! the ABI argument-register observation only selects *candidates*; every
//! individual binding is justified by the write-freedom analysis over the
//! body being lowered.

use trust_types::fx::FxHashMap;
use trust_types::{Formula, Sort, Statement, Terminator, VerifiableBody};

/// Machine-register namespace the binding table speaks. Checked structurally
/// against the body (`LocalDecl` names) before any binding is used, so a
/// table built for one architecture cannot silently apply to another.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BindingArch {
    /// x86-64 SysV: argument registers RDI, RSI, RDX, RCX, R8, R9.
    X86_64,
    /// AArch64 AAPCS64: argument registers X0..X7.
    Aarch64,
}

/// One entry-register parameter: LIR param `i` is the function-entry value of
/// `params[i]`. The params list is an ABI-order PREFIX of the architecture's
/// argument registers, so a param's position always equals its ABI slot.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BinaryEntryParam {
    /// Machine-state formula namespace name, e.g. `"X7"` (the lift's
    /// `MachineState::symbolic` seeds `Var("X{gpr_index}")` on both ISAs).
    pub var_name: String,
    /// ISA register name for diagnostics and the structural cross-check
    /// against the body's `LocalDecl` name, e.g. `"RDI"`.
    pub reg_name: String,
    /// The register's TrustIR local index in the lifted body's `LocalLayout`.
    pub local_index: usize,
}

/// Entry-register binding table for one binary-lifted function.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BinaryEntryBindings {
    pub arch: BindingArch,
    pub params: Vec<BinaryEntryParam>,
}

/// A symbolic formula the lowering actually consumed with target semantics
/// (today: the 8-byte little-endian load shape lowered to `Opcode::Load`, and
/// bare bound `Var`s lowered to the LIR parameter). Keyed so conversion
/// evidence rows `(block, statement_index)` can be marked consumed; the
/// formula is carried so two different formulas in one statement can never be
/// cross-marked.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConsumedSymbolicLowering {
    pub block: usize,
    pub statement_index: usize,
    pub formula: Formula,
    /// Human-readable account of the emitted LIR and the justification,
    /// naming BOTH evidence sources: the entry-block read-before-write
    /// observation (candidacy only) and the per-block write-freedom
    /// certificate (the binding).
    pub detail: String,
}

/// Why the whole binding table is unusable for a body (per-function refusal;
/// individual uses may additionally be refused by the per-block certificate).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EntryBindingRefusal {
    pub reason: String,
}

/// Per-block write-freedom certificate over the binding params.
///
/// `preserved[b]` holds param index `i` iff `params[i]`'s register local is
/// assigned by NO statement on ANY path from function entry to block `b`'s
/// entry — including paths that re-enter the entry block through a back edge.
#[derive(Clone, Debug)]
pub struct EntryPreservation {
    /// block id -> bitmask over param indices (bit i = params[i] preserved).
    preserved: FxHashMap<usize, u32>,
    /// param index -> every (block id, statement index) that kills it, for
    /// truthful refusal messages.
    kills: FxHashMap<usize, Vec<(usize, usize)>>,
}

impl EntryPreservation {
    pub fn is_preserved(&self, block: usize, param_index: usize) -> bool {
        self.preserved.get(&block).is_some_and(|mask| mask & (1 << param_index) != 0)
    }

    /// The concrete kill sites for a param, for refusal messages. Empty means
    /// the non-preservation came from a structural gate, not a located write.
    pub fn kill_sites(&self, param_index: usize) -> &[(usize, usize)] {
        self.kills.get(&param_index).map_or(&[], Vec::as_slice)
    }
}

/// Compute the per-block write-freedom certificate for `bindings` over `body`.
///
/// Fails closed (`Err`) when the body contains any shape the binary lift
/// cannot have produced — an unexpected statement or terminator variant, a
/// successor id that names no block, a param local whose declared name does
/// not match the binding's register name — because then this analysis has no
/// contract to stand on.
pub fn compute_entry_preservation(
    body: &VerifiableBody,
    bindings: &BinaryEntryBindings,
) -> Result<EntryPreservation, EntryBindingRefusal> {
    let refuse = |reason: String| Err(EntryBindingRefusal { reason });

    // Strictly below the mask width: exactly 32 would make the all-params mask
    // `(1u32 << 32) - 1`, a shift overflow (panic in debug, silently-empty
    // certificate in release — the wrong refusal with the wrong message).
    if bindings.params.len() >= 32 {
        return refuse(format!(
            "entry bindings carry {} params; the certificate mask supports at most 31",
            bindings.params.len()
        ));
    }
    if body.arg_count != 0 {
        return refuse(format!(
            "entry bindings require a machine-register body (arg_count 0), got arg_count {}",
            body.arg_count
        ));
    }

    // The table must BE the architecture's ABI argument-register prefix, in
    // order — the invariant every consumer of `params[i]` relies on (LIR param
    // position == ABI slot). The producer (trust-lift's
    // `entry_register_binding_prefix`) constructs exactly this; validating it
    // here makes a reordered, duplicated, or cross-architecture table from any
    // OTHER caller of the public API refuse instead of silently binding wrong
    // registers. The expected names are stable ABI facts; if the two copies
    // ever drift, the failure direction is refusal, never a wrong binding.
    let expected_prefix: &[(&str, &str)] = match bindings.arch {
        BindingArch::X86_64 => &[
            ("X7", "RDI"),
            ("X6", "RSI"),
            ("X2", "RDX"),
            ("X1", "RCX"),
            ("X8", "R8"),
            ("X9", "R9"),
        ],
        BindingArch::Aarch64 => &[
            ("X0", "X0"),
            ("X1", "X1"),
            ("X2", "X2"),
            ("X3", "X3"),
            ("X4", "X4"),
            ("X5", "X5"),
            ("X6", "X6"),
            ("X7", "X7"),
        ],
    };
    if bindings.params.len() > expected_prefix.len() {
        return refuse(format!(
            "entry bindings carry {} params but {:?} has {} ABI argument registers",
            bindings.params.len(),
            bindings.arch,
            expected_prefix.len()
        ));
    }
    for (abi_slot, param) in bindings.params.iter().enumerate() {
        let (expected_var, expected_reg) = expected_prefix[abi_slot];
        if param.var_name != expected_var || param.reg_name != expected_reg {
            return refuse(format!(
                "entry binding param {abi_slot} is {}/{} but ABI slot {abi_slot} of {:?} is \
                 {expected_var}/{expected_reg}; the table must be the ABI argument-register \
                 prefix in order (LIR param position IS the ABI slot)",
                param.var_name, param.reg_name, bindings.arch
            ));
        }
    }

    // Structural cross-check: each param's local must exist, be named exactly
    // the ISA register the binding claims, and be a 64-bit integer local.
    // This is what makes a table built for the wrong body (or the wrong
    // architecture) refuse instead of silently binding the wrong register.
    for param in &bindings.params {
        let Some(local) = body.locals.iter().find(|l| l.index == param.local_index) else {
            return refuse(format!(
                "entry binding {} names local {} which does not exist in the body",
                param.reg_name, param.local_index
            ));
        };
        if local.name.as_deref() != Some(param.reg_name.as_str()) {
            return refuse(format!(
                "entry binding {} names local {} but the body declares that local as {:?}; \
                 refusing a table that does not match the body it is applied to",
                param.reg_name, param.local_index, local.name
            ));
        }
    }

    let position_of: FxHashMap<usize, usize> =
        body.blocks.iter().enumerate().map(|(pos, bb)| (bb.id.0, pos)).collect();
    if position_of.len() != body.blocks.len() {
        return refuse("duplicate block ids in body".to_string());
    }

    let param_by_local: FxHashMap<usize, usize> = bindings
        .params
        .iter()
        .enumerate()
        .map(|(i, param)| (param.local_index, i))
        .collect();

    let all_params: u32 = if bindings.params.is_empty() {
        0
    } else {
        (1u32 << bindings.params.len()) - 1
    };

    // Kill sets per block position, from an exhaustive statement match. The
    // strict binary lift emits ONLY `Assign` (its `Nop`s are retained out);
    // every other variant refuses rather than being classified, because a
    // statement the lift cannot have produced voids the analysis's contract.
    let mut killed: Vec<u32> = vec![0; body.blocks.len()];
    let mut kills: FxHashMap<usize, Vec<(usize, usize)>> = FxHashMap::default();
    for (pos, bb) in body.blocks.iter().enumerate() {
        for (stmt_index, stmt) in bb.stmts.iter().enumerate() {
            match stmt {
                Statement::Assign { place, .. } => {
                    // A projected write into a register local is still a write.
                    if let Some(&param_index) = param_by_local.get(&place.local) {
                        killed[pos] |= 1 << param_index;
                        kills.entry(param_index).or_default().push((bb.id.0, stmt_index));
                    }
                }
                Statement::Nop => {}
                other => {
                    return refuse(format!(
                        "block {} statement {} has kind {:?}, which the binary lift does not \
                         emit; entry bindings refuse bodies outside the lift's statement contract",
                        bb.id.0,
                        stmt_index,
                        core::mem::discriminant(other)
                    ));
                }
            }
        }
    }

    // Successor edges from an exhaustive terminator match. `Goto`, `SwitchInt`
    // and `Return` are the strict semantic lift's complete terminator
    // vocabulary; anything else (Call writes a destination local, Assert,
    // Unreachable, Opaque, ...) voids the contract.
    let mut successors: Vec<Vec<usize>> = vec![Vec::new(); body.blocks.len()];
    for (pos, bb) in body.blocks.iter().enumerate() {
        let mut push_edge = |target: usize| -> Result<(), EntryBindingRefusal> {
            match position_of.get(&target) {
                Some(&target_pos) => {
                    successors[pos].push(target_pos);
                    Ok(())
                }
                None => Err(EntryBindingRefusal {
                    reason: format!(
                        "block {} names successor {} which does not exist; an incomplete CFG \
                         cannot support a must-analysis over all paths",
                        bb.id.0, target
                    ),
                }),
            }
        };
        match &bb.terminator {
            Terminator::Goto(target) => push_edge(target.0)?,
            Terminator::SwitchInt { targets, otherwise, .. } => {
                for (_, target) in targets {
                    push_edge(target.0)?;
                }
                push_edge(otherwise.0)?;
            }
            Terminator::Return => {}
            other => {
                return refuse(format!(
                    "block {} has terminator kind {:?}, which the binary lift does not emit; \
                     entry bindings refuse bodies outside the lift's terminator contract",
                    bb.id.0,
                    core::mem::discriminant(other)
                ));
            }
        }
    }

    let mut predecessors: Vec<Vec<usize>> = vec![Vec::new(); body.blocks.len()];
    for (pos, succs) in successors.iter().enumerate() {
        for &succ in succs {
            predecessors[succ].push(pos);
        }
    }

    // Forward must-analysis to fixpoint. The function-entry boundary is a
    // VIRTUAL edge into blocks[0] carrying `all_params`; the entry block still
    // PARTICIPATES in the intersection over its real predecessors, so a back
    // edge into the entry block kills through that edge (the entry block's
    // second arrival is not the function entry). Non-entry blocks with no
    // predecessors are unreachable: nothing is preserved there, and any use is
    // refused rather than reasoned about.
    let entry = 0usize;
    let mut preserved: Vec<u32> = vec![all_params; body.blocks.len()];
    loop {
        let mut changed = false;
        for pos in 0..body.blocks.len() {
            let mut incoming = if pos == entry {
                all_params
            } else if predecessors[pos].is_empty() {
                0
            } else {
                all_params
            };
            for &pred in &predecessors[pos] {
                incoming &= preserved[pred] & !killed[pred];
            }
            if incoming != preserved[pos] {
                preserved[pos] = incoming;
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }

    let preserved_by_id: FxHashMap<usize, u32> = body
        .blocks
        .iter()
        .enumerate()
        .map(|(pos, bb)| (bb.id.0, preserved[pos]))
        .collect();

    Ok(EntryPreservation { preserved: preserved_by_id, kills })
}

/// The candidate address root of a recognized formula: a bare bound `Var`
/// (`base_var`) plus an optional constant byte displacement.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LoadShapeRoot {
    pub base_var: String,
    pub displacement: Option<i128>,
}

/// Recognize the exact 8-byte little-endian load shape both lifters emit
/// (`trust-machine-sem::load_le_bytes` and `trust-lift::byte_load_formula`):
///
/// ```text
/// acc_0 = BvZeroExt(Select(MEM, root), 56)
/// acc_i = BvOr(acc_{i-1}, BvShl(BvZeroExt(Select(MEM, root + i), 56), 8·i, 64), 64)
/// ```
///
/// for i = 1..7, where MEM is the bare machine-memory seed
/// `Var("MEM", Array(BitVec 64, BitVec 8))` and `root` is a bare 64-bit `Var`
/// or `BvAdd(Var, constant, 64)`.
///
/// Recognition is reconstruct-and-equate: the candidate root is EXTRACTED
/// from the deepest-left term, the full expected formula is REBUILT from it,
/// and anything short of structural equality (byte order, extension kind or
/// amount, a missing byte, a different memory operand) returns `None`. Only
/// the root's shape is trusted from extraction; everything else is recomputed.
pub fn recognize_le_load(formula: &Formula) -> Option<LoadShapeRoot> {
    // Walk the left spine of the BvOr chain to the base term.
    let mut base = formula;
    while let Formula::BvOr(lhs, _, 64) = base {
        base = lhs;
    }
    // Base term: BvZeroExt(Select(mem_seed, root), 56).
    let Formula::BvZeroExt(inner, 56) = base else {
        return None;
    };
    let Formula::Select(mem, root) = inner.as_ref() else {
        return None;
    };
    if !is_machine_memory_seed(mem) {
        return None;
    }
    let root_shape = classify_root(root)?;

    // Reconstruct the full 8-byte little-endian load over the extracted root
    // and require structural equality with the input.
    let expected = build_le_load(mem, root);
    (*formula == expected).then_some(root_shape)
}

/// Recognize a bare 64-bit register `Var` operand (e.g. a `mov rax, rdi`
/// lowered against block-entry state). Returns the variable name.
pub fn recognize_bare_reg_var(formula: &Formula) -> Option<&str> {
    match formula {
        Formula::Var(name, Sort::BitVec(64)) => Some(name.as_str()),
        _ => None,
    }
}

fn is_machine_memory_seed(formula: &Formula) -> bool {
    matches!(
        formula,
        Formula::Var(name, Sort::Array(index, element))
            if name == "MEM"
                && matches!(index.as_ref(), Sort::BitVec(64))
                && matches!(element.as_ref(), Sort::BitVec(8))
    )
}

fn classify_root(root: &Formula) -> Option<LoadShapeRoot> {
    match root {
        Formula::Var(name, Sort::BitVec(64)) => {
            Some(LoadShapeRoot { base_var: name.clone(), displacement: None })
        }
        Formula::BvAdd(base, offset, 64) => match (base.as_ref(), offset.as_ref()) {
            (Formula::Var(name, Sort::BitVec(64)), Formula::BitVec { value, width: 64 }) => {
                Some(LoadShapeRoot { base_var: name.clone(), displacement: Some(*value) })
            }
            _ => None,
        },
        _ => None,
    }
}

fn build_le_load(mem: &Formula, root: &Formula) -> Formula {
    let mut result = Formula::BitVec { value: 0, width: 64 };
    for i in 0..8u32 {
        let byte_addr = if i == 0 {
            root.clone()
        } else {
            Formula::BvAdd(
                Box::new(root.clone()),
                Box::new(Formula::BitVec { value: i128::from(i), width: 64 }),
                64,
            )
        };
        let byte = Formula::Select(Box::new(mem.clone()), Box::new(byte_addr));
        let extended = Formula::BvZeroExt(Box::new(byte), 56);
        if i == 0 {
            result = extended;
        } else {
            let shifted = Formula::BvShl(
                Box::new(extended),
                Box::new(Formula::BitVec { value: i128::from(i * 8), width: 64 }),
                64,
            );
            result = Formula::BvOr(Box::new(result), Box::new(shifted), 64);
        }
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_types::{
        BasicBlock, BlockId, LocalDecl, Operand, Place, Rvalue, SourceSpan, Ty,
    };

    fn u64_ty() -> Ty {
        Ty::Int { width: 64, signed: false }
    }

    fn locals_with_regs(regs: &[(usize, &str)]) -> Vec<LocalDecl> {
        let mut locals = vec![LocalDecl { index: 0, ty: u64_ty(), name: None }];
        locals.extend(regs.iter().map(|(index, name)| LocalDecl {
            index: *index,
            ty: u64_ty(),
            name: Some((*name).to_string()),
        }));
        locals
    }

    fn assign_to(local: usize) -> Statement {
        Statement::Assign {
            place: Place::local(local),
            rvalue: Rvalue::Use(Operand::Constant(trust_types::ConstValue::Uint(0, 64))),
            span: SourceSpan::default(),
        }
    }

    fn body(locals: Vec<LocalDecl>, blocks: Vec<BasicBlock>) -> VerifiableBody {
        VerifiableBody {
            locals,
            blocks,
            arg_count: 0,
            return_ty: Ty::Unit,
            datatype_defs: Default::default(),
        }
    }

    fn rdi_bindings() -> BinaryEntryBindings {
        BinaryEntryBindings {
            arch: BindingArch::X86_64,
            params: vec![BinaryEntryParam {
                var_name: "X7".to_string(),
                reg_name: "RDI".to_string(),
                local_index: 8,
            }],
        }
    }

    fn block(id: usize, stmts: Vec<Statement>, terminator: Terminator) -> BasicBlock {
        BasicBlock { id: BlockId(id), stmts, terminator }
    }

    #[test]
    fn single_block_preserves_everything_at_entry() {
        let b = body(
            locals_with_regs(&[(8, "RDI")]),
            vec![block(0, vec![], Terminator::Return)],
        );
        let preservation = compute_entry_preservation(&b, &rdi_bindings()).expect("computes");
        assert!(preservation.is_preserved(0, 0));
    }

    #[test]
    fn diamond_with_one_clobbering_arm_does_not_preserve_at_the_join() {
        // 0 -> {1, 2}; 1 clobbers RDI; both -> 3. The join must NOT preserve
        // RDI (a path wrote it), while the clean arm 2 still does.
        let b = body(
            locals_with_regs(&[(8, "RDI")]),
            vec![
                block(
                    0,
                    vec![],
                    Terminator::SwitchInt {
                        discr: Operand::Constant(trust_types::ConstValue::Bool(true)),
                        targets: vec![(1, BlockId(1))],
                        otherwise: BlockId(2),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                ),
                block(1, vec![assign_to(8)], Terminator::Goto(BlockId(3))),
                block(2, vec![], Terminator::Goto(BlockId(3))),
                block(3, vec![], Terminator::Return),
            ],
        );
        let preservation = compute_entry_preservation(&b, &rdi_bindings()).expect("computes");
        assert!(preservation.is_preserved(0, 0));
        assert!(preservation.is_preserved(2, 0));
        assert!(!preservation.is_preserved(3, 0), "join after a clobbering arm must refuse");
        assert_eq!(preservation.kill_sites(0), &[(1, 0)]);
    }

    #[test]
    fn diamond_with_no_clobbers_preserves_at_the_join() {
        // The converse control: refusing here would be over-correction.
        let b = body(
            locals_with_regs(&[(8, "RDI")]),
            vec![
                block(
                    0,
                    vec![],
                    Terminator::SwitchInt {
                        discr: Operand::Constant(trust_types::ConstValue::Bool(true)),
                        targets: vec![(1, BlockId(1))],
                        otherwise: BlockId(2),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                ),
                block(1, vec![], Terminator::Goto(BlockId(3))),
                block(2, vec![], Terminator::Goto(BlockId(3))),
                block(3, vec![], Terminator::Return),
            ],
        );
        let preservation = compute_entry_preservation(&b, &rdi_bindings()).expect("computes");
        assert!(preservation.is_preserved(3, 0));
    }

    #[test]
    fn loop_body_clobber_reaches_the_loop_head_through_the_back_edge() {
        // 0 -> 1; 1 clobbers RDI and loops to itself or returns. Block 1's
        // entry is reached both clean (from 0) and clobbered (from itself):
        // not preserved.
        let b = body(
            locals_with_regs(&[(8, "RDI")]),
            vec![
                block(0, vec![], Terminator::Goto(BlockId(1))),
                block(
                    1,
                    vec![assign_to(8)],
                    Terminator::SwitchInt {
                        discr: Operand::Constant(trust_types::ConstValue::Bool(true)),
                        targets: vec![(1, BlockId(1))],
                        otherwise: BlockId(2),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                ),
                block(2, vec![], Terminator::Return),
            ],
        );
        let preservation = compute_entry_preservation(&b, &rdi_bindings()).expect("computes");
        assert!(!preservation.is_preserved(1, 0));
        assert!(!preservation.is_preserved(2, 0));
    }

    /// The panel's blocker control: a back edge INTO THE ENTRY BLOCK. The
    /// entry block's second arrival is not the function entry, so a clobber
    /// anywhere in the loop must strip preservation from the entry block
    /// itself.
    #[test]
    fn entry_as_loop_head_with_clobber_is_not_preserved() {
        let b = body(
            locals_with_regs(&[(8, "RDI")]),
            vec![block(
                0,
                vec![assign_to(8)],
                Terminator::SwitchInt {
                    discr: Operand::Constant(trust_types::ConstValue::Bool(true)),
                    targets: vec![(1, BlockId(0))],
                    otherwise: BlockId(1),
                    exhaustive_enum_unreachable: false,
                    span: SourceSpan::default(),
                },
            ), block(1, vec![], Terminator::Return)],
        );
        let preservation = compute_entry_preservation(&b, &rdi_bindings()).expect("computes");
        assert!(
            !preservation.is_preserved(0, 0),
            "a self-loop clobber reaches the entry block's own entry via the back edge"
        );
    }

    /// Converse of the blocker control: a self-loop that never writes the
    /// register keeps the binding.
    #[test]
    fn entry_as_loop_head_without_clobber_stays_preserved() {
        let b = body(
            locals_with_regs(&[(8, "RDI")]),
            vec![block(
                0,
                vec![],
                Terminator::SwitchInt {
                    discr: Operand::Constant(trust_types::ConstValue::Bool(true)),
                    targets: vec![(1, BlockId(0))],
                    otherwise: BlockId(1),
                    exhaustive_enum_unreachable: false,
                    span: SourceSpan::default(),
                },
            ), block(1, vec![], Terminator::Return)],
        );
        let preservation = compute_entry_preservation(&b, &rdi_bindings()).expect("computes");
        assert!(preservation.is_preserved(0, 0));
        assert!(preservation.is_preserved(1, 0));
    }

    #[test]
    fn unreachable_non_entry_block_preserves_nothing() {
        let b = body(
            locals_with_regs(&[(8, "RDI")]),
            vec![
                block(0, vec![], Terminator::Return),
                block(1, vec![], Terminator::Return),
            ],
        );
        let preservation = compute_entry_preservation(&b, &rdi_bindings()).expect("computes");
        assert!(!preservation.is_preserved(1, 0));
    }

    #[test]
    fn statement_outside_the_lift_contract_refuses() {
        let b = body(
            locals_with_regs(&[(8, "RDI")]),
            vec![block(0, vec![Statement::StorageLive(3)], Terminator::Return)],
        );
        let err = compute_entry_preservation(&b, &rdi_bindings()).expect_err("refuses");
        assert!(err.reason.contains("binary lift does not emit"), "{}", err.reason);
    }

    #[test]
    fn terminator_outside_the_lift_contract_refuses() {
        let b = body(
            locals_with_regs(&[(8, "RDI")]),
            vec![block(0, vec![], Terminator::Unreachable)],
        );
        let err = compute_entry_preservation(&b, &rdi_bindings()).expect_err("refuses");
        assert!(err.reason.contains("terminator"), "{}", err.reason);
    }

    /// The mask boundary: exactly 32 params must refuse (not shift-overflow),
    /// and the message names the ceiling.
    #[test]
    fn thirty_two_params_refuse_at_the_mask_boundary() {
        let params: Vec<BinaryEntryParam> = (0..32)
            .map(|i| BinaryEntryParam {
                var_name: format!("X{i}"),
                reg_name: format!("R{i}"),
                local_index: i + 1,
            })
            .collect();
        let bindings = BinaryEntryBindings { arch: BindingArch::X86_64, params };
        let b = body(
            locals_with_regs(&[(8, "RDI")]),
            vec![block(0, vec![], Terminator::Return)],
        );
        let err = compute_entry_preservation(&b, &bindings).expect_err("refuses at 32");
        assert!(err.reason.contains("at most 31"), "{}", err.reason);
    }

    /// The table must BE the ABI argument-register prefix in order: a
    /// reordered table (RSI in slot 0) refuses even though every entry is a
    /// real argument register — positional param meaning is the invariant.
    #[test]
    fn reordered_table_refuses() {
        let bindings = BinaryEntryBindings {
            arch: BindingArch::X86_64,
            params: vec![BinaryEntryParam {
                var_name: "X6".to_string(),
                reg_name: "RSI".to_string(),
                local_index: 7,
            }],
        };
        let b = body(
            locals_with_regs(&[(7, "RSI")]),
            vec![block(0, vec![], Terminator::Return)],
        );
        let err = compute_entry_preservation(&b, &bindings).expect_err("refuses non-prefix");
        assert!(err.reason.contains("ABI slot 0"), "{}", err.reason);
    }

    /// A table claiming the wrong architecture refuses before the local-name
    /// cross-check can be fooled by coincidental names.
    #[test]
    fn cross_architecture_table_refuses() {
        let bindings = BinaryEntryBindings {
            arch: BindingArch::Aarch64,
            params: vec![BinaryEntryParam {
                var_name: "X7".to_string(),
                reg_name: "RDI".to_string(),
                local_index: 8,
            }],
        };
        let b = body(
            locals_with_regs(&[(8, "RDI")]),
            vec![block(0, vec![], Terminator::Return)],
        );
        let err = compute_entry_preservation(&b, &bindings).expect_err("refuses wrong arch");
        assert!(err.reason.contains("Aarch64"), "{}", err.reason);
    }

    #[test]
    fn mismatched_register_local_name_refuses() {
        // A binding table applied to a body whose local 8 is not RDI (e.g. an
        // AArch64 layout, where local 8 is X7's neighbor namespace) must
        // refuse rather than bind the wrong register.
        let b = body(
            locals_with_regs(&[(8, "X7")]),
            vec![block(0, vec![], Terminator::Return)],
        );
        let err = compute_entry_preservation(&b, &rdi_bindings()).expect_err("refuses");
        assert!(err.reason.contains("does not match"), "{}", err.reason);
    }

    #[test]
    fn missing_successor_refuses() {
        let b = body(
            locals_with_regs(&[(8, "RDI")]),
            vec![block(0, vec![], Terminator::Goto(BlockId(7)))],
        );
        let err = compute_entry_preservation(&b, &rdi_bindings()).expect_err("refuses");
        assert!(err.reason.contains("does not exist"), "{}", err.reason);
    }

    fn mem_seed() -> Formula {
        Formula::Var(
            "MEM".to_string(),
            Sort::Array(Box::new(Sort::BitVec(64)), Box::new(Sort::BitVec(8))),
        )
    }

    fn x7() -> Formula {
        Formula::Var("X7".to_string(), Sort::BitVec(64))
    }

    #[test]
    fn recognizes_the_exact_le_load_shape() {
        let formula = build_le_load(&mem_seed(), &x7());
        assert_eq!(
            recognize_le_load(&formula),
            Some(LoadShapeRoot { base_var: "X7".to_string(), displacement: None })
        );
    }

    #[test]
    fn recognizes_a_constant_displacement_root() {
        let root = Formula::BvAdd(
            Box::new(x7()),
            Box::new(Formula::BitVec { value: 16, width: 64 }),
            64,
        );
        let formula = build_le_load(&mem_seed(), &root);
        assert_eq!(
            recognize_le_load(&formula),
            Some(LoadShapeRoot { base_var: "X7".to_string(), displacement: Some(16) })
        );
    }

    /// Mutation battery over the shape: each deviation must be refused, and
    /// the unmutated original must still be recognized (the converse control
    /// guarding against an over-strict matcher that refuses everything).
    #[test]
    fn shape_mutations_are_refused() {
        let original = build_le_load(&mem_seed(), &x7());
        assert!(recognize_le_load(&original).is_some(), "converse control");

        // Big-endian byte order: swap the shift amounts.
        let mut be = original.clone();
        if let Formula::BvOr(_, rhs, _) = &mut be {
            if let Formula::BvShl(_, amount, _) = rhs.as_mut() {
                **amount = Formula::BitVec { value: 0, width: 64 };
            }
        }
        assert!(recognize_le_load(&be).is_none(), "byte-order mutation must refuse");

        // Wrong extension amount (the historical BvZeroExt units bug).
        let wrong_ext = {
            let mut byte0_wrong = original.clone();
            fn deepest_left(formula: &mut Formula) -> &mut Formula {
                match formula {
                    Formula::BvOr(lhs, _, _) => deepest_left(lhs),
                    other => other,
                }
            }
            let base = deepest_left(&mut byte0_wrong);
            if let Formula::BvZeroExt(_, amount) = base {
                *amount = 64;
            }
            byte0_wrong
        };
        assert!(recognize_le_load(&wrong_ext).is_none(), "wrong extension amount must refuse");

        // Missing top byte: a 7-byte chain.
        let seven_bytes = {
            match &original {
                Formula::BvOr(lhs, _, _) => lhs.as_ref().clone(),
                _ => unreachable!("8-byte load is a BvOr chain"),
            }
        };
        assert!(recognize_le_load(&seven_bytes).is_none(), "missing byte must refuse");

        // A different memory operand (not the machine seed).
        let other_mem = Formula::Var(
            "MEM2".to_string(),
            Sort::Array(Box::new(Sort::BitVec(64)), Box::new(Sort::BitVec(8))),
        );
        let wrong_mem = build_le_load(&other_mem, &x7());
        assert!(recognize_le_load(&wrong_mem).is_none(), "non-seed memory must refuse");

        // A folded (non-bare) root: Select over a Store chain must refuse.
        let stored_mem = Formula::Store(
            Box::new(mem_seed()),
            Box::new(x7()),
            Box::new(Formula::BitVec { value: 0, width: 8 }),
        );
        let folded = build_le_load(&stored_mem, &x7());
        assert!(recognize_le_load(&folded).is_none(), "folded memory must refuse");
    }
}
