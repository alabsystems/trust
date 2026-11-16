//! The machine stack pointer across a lifted CFG, over FUNCTION-ENTRY SP.
//!
//! The semantic lift seeds a FRESH symbolic machine state per basic block
//! (`lift_cfg_with_semantics` in `semantic_lift.rs`): a bare `Var("SP")` in block
//! B's statements is SP at B's ENTRY, and an SP write in B is a formula over B's
//! entry state. A consumer that wants SP relative to FUNCTION entry — the
//! stack-discipline VC in `trust-vcgen`, the frame reconstruction in
//! `trust-decompile` — therefore cannot read it off one block. The two readings
//! coincide only in an entry block that nothing branches back into, so SP is
//! computed here by a forward analysis over the lifted CFG:
//!
//! * a block that writes no SP passes SP through unchanged — this is what makes
//!   `ldr x0, [x0]; ret` restore SP;
//! * an SP write is re-expressed over function-entry SP by substituting the SP
//!   that flows into the block — allowed only when the write reads no block-entry
//!   state other than SP (and, when one is tracked, the frame pointer), because no
//!   other register is tracked across blocks;
//! * paths that disagree, or any shape outside the lift's contract, yield no value.
//!
//! THE FRAME POINTER, when the caller names it (`stack_pointer_flow_with_frame_pointer`),
//! is carried the same way, because a frame-pointer epilogue restores SP FROM it:
//! `leave` / `mov rsp, rbp` on x86-64, `mov sp, x29` on AArch64. In the block that
//! set up the frame that write reads a known value; in a LATER block it reads the
//! frame pointer at that block's entry, which only a cross-block value can
//! re-express. Without it such a function's SP at return was not derivable, and
//! the stack-discipline VC reported a correct function as unbalanced, with a
//! counterexample. The frame pointer is a plain register the lift writes like any
//! other, so it gets exactly SP's rules: its last whole-local write, re-expressed
//! over function entry only when it reads nothing but SP and itself.
//!
//! Every imprecision falls on the "not derivable" side: a value is `Some` only
//! when every path from function entry agrees on it. Joins compare formulas
//! SYNTACTICALLY, so two paths that reach the same SP by different arithmetic
//! also yield no value.
//!
//! ONE SUBTLE DEPENDENCY. A block's effect is its LAST SP write. That is sound
//! only because the lift folds each write over the block's ENTRY state rather
//! than emitting MIR-sequential statements (`push rbp` lifts to
//! `SP := SP - 8`, and the store beside it addresses `SP - 8`, both over the
//! block's entry SP). A body built with sequential semantics is outside this
//! contract.
//!
//! This module is the single implementation both consumers share, so a fix to
//! the model reaches both. It was moved here from `trust-vcgen`'s
//! `lift_adapter.rs` (887ac8352d) unchanged in behaviour; the per-block ENTRY
//! values are the one addition, for `trust-decompile`.

use trust_machine_sem::MachineState;
use trust_types::{
    BasicBlock, BlockId, Formula, Rvalue, Sort, Statement, Terminator, VerifiableBody,
};

use crate::cfg::LiftedFunction;
use crate::semantic_lift::LocalLayout;

/// `Var("SP")` at 64 bits: the lift's name for the machine stack pointer, read
/// as SP at FUNCTION entry in every formula this module returns.
#[must_use]
pub fn function_entry_stack_pointer() -> Formula {
    Formula::Var("SP".into(), Sort::BitVec(64))
}

/// The position, in `lifted.trust_ir_body.blocks`, of the function's entry
/// block: the CFG's entry, read through the lifted block id (which is also the
/// body block's position when the body is well formed; `stack_pointer_flow`
/// checks that). `None` when the CFG names no entry block.
#[must_use]
pub fn lifted_entry_block(lifted: &LiftedFunction) -> Option<usize> {
    lifted.cfg.blocks.get(lifted.cfg.entry).map(|block| block.id)
}

/// A frame-pointer register the flow carries across blocks beside SP: the local
/// the lift writes it through, and the variable that names its value at a block's
/// entry. Both come from the lift's own definitions — `LocalLayout::gpr` and
/// `MachineState::symbolic` — so they cannot drift from what the lift emits.
#[derive(Debug, Clone, PartialEq)]
pub struct FramePointer {
    local: usize,
    register: Formula,
}

impl FramePointer {
    /// x86-64 `RBP` (general-purpose register 5).
    #[must_use]
    pub fn x86_64() -> Self {
        Self::gpr(&LocalLayout::x86_64(), 5)
    }

    /// AArch64 `X29`, the AAPCS64 frame pointer.
    #[must_use]
    pub fn aarch64() -> Self {
        Self::gpr(&LocalLayout::aarch64(), 29)
    }

    fn gpr(layout: &LocalLayout, index: u8) -> Self {
        Self { local: layout.gpr(index), register: MachineState::symbolic().read_gpr(index, 64) }
    }

    /// The local the lift writes this register through.
    #[must_use]
    pub fn local(&self) -> usize {
        self.local
    }
}

/// The stack pointer at one program point of a lifted body.
#[derive(Debug, Clone, PartialEq)]
enum EntrySp {
    /// No path from function entry reaches this point (yet, in the fixpoint).
    Unreached,
    /// SP here equals this formula, in which `Var("SP")` is SP at FUNCTION entry.
    Known(Formula),
    /// Not derivable from the lifted statements.
    Unknown,
}

impl EntrySp {
    fn join_ref(&mut self, other: &Self) {
        match (&*self, other) {
            (_, Self::Unreached) => {}
            (Self::Unreached, other) => *self = other.clone(),
            (Self::Known(left), Self::Known(right)) if left == right => {}
            _ => *self = Self::Unknown,
        }
    }

    fn known(self) -> Option<Formula> {
        match self {
            Self::Known(formula) => Some(formula),
            Self::Unreached | Self::Unknown => None,
        }
    }

    fn known_ref(&self) -> Option<&Formula> {
        match self {
            Self::Known(formula) => Some(formula),
            Self::Unreached | Self::Unknown => None,
        }
    }
}

/// SP and the frame pointer at one program point. They are reached together: a
/// point no path reaches has both `Unreached`, and a reached one has neither.
/// When no frame pointer is tracked its value is `Unknown` wherever SP is reached.
#[derive(Debug, Clone, PartialEq)]
struct Registers {
    sp: EntrySp,
    fp: EntrySp,
}

impl Registers {
    fn unreached() -> Self {
        Self { sp: EntrySp::Unreached, fp: EntrySp::Unreached }
    }

    fn join_ref(&mut self, other: &Self) {
        self.sp.join_ref(&other.sp);
        self.fp.join_ref(&other.fp);
    }
}

/// How one lifted block changes one tracked register's local.
enum RegisterWrite {
    /// No statement writes it.
    Preserves,
    /// The block's LAST write, a formula over the block's ENTRY machine state.
    Writes(Formula),
    /// Its last write is one the reader cannot read.
    Unreadable,
}

/// How one lifted block changes the tracked registers. A block holding a
/// statement this analysis cannot read has none (`block_writes` answers `None`):
/// every tracked value is lost there.
struct BlockWrites {
    sp: RegisterWrite,
    fp: RegisterWrite,
}

fn block_writes(
    block: &BasicBlock,
    sp_local: usize,
    fp_local: Option<usize>,
    read_write: &impl Fn(&Rvalue) -> Option<Formula>,
) -> Option<BlockWrites> {
    let (mut sp, mut fp) = (RegisterWrite::Preserves, RegisterWrite::Preserves);
    for stmt in &block.stmts {
        match stmt {
            // The lift writes whole machine locals only; a projected write
            // (through a pointer, into a field) is outside its contract and
            // could reach SP or the frame pointer by aliasing.
            Statement::Assign { place, .. } if !place.projections.is_empty() => return None,
            Statement::Assign { place, rvalue, .. } if place.local == sp_local => {
                sp = RegisterWrite::Writes(read_write(rvalue)?);
            }
            Statement::Assign { place, rvalue, .. } if Some(place.local) == fp_local => {
                fp = read_write(rvalue).map_or(RegisterWrite::Unreadable, RegisterWrite::Writes);
            }
            Statement::Assign { .. } | Statement::Nop => {}
            _ => return None,
        }
    }
    Some(BlockWrites { sp, fp })
}

/// Whether `formula` is the 64-bit machine stack pointer (`Var("SP", BitVec(64))`).
fn is_function_entry_stack_pointer(formula: &Formula) -> bool {
    matches!(formula, Formula::Var(name, Sort::BitVec(64)) if name == "SP")
}

/// Whether every variable in `formula` is the 64-bit machine stack pointer.
fn formula_reads_only_machine_sp(formula: &Formula) -> bool {
    trust_types::all_formula_nodes(formula, &mut |node| match node {
        Formula::Var(name, sort) => name == "SP" && *sort == Sort::BitVec(64),
        Formula::SymVar(..) | Formula::Forall(..) | Formula::Exists(..) => false,
        _ => true,
    })
}

/// `write` with its block-entry `Var("SP")` replaced by `sp_at_block_entry`.
fn substitute_block_entry_sp(write: &Formula, sp_at_block_entry: &Formula) -> Formula {
    write.clone().map(&mut |node| {
        if is_function_entry_stack_pointer(&node) { sp_at_block_entry.clone() } else { node }
    })
}

/// The value an SP write in some block stores, over FUNCTION-entry SP.
///
/// `write` is the written formula as the lift emits it — over its block's ENTRY
/// state — and `sp_at_block_entry` is SP at that block's entry over
/// function-entry SP (`StackPointerFlow::at_block_entry`). Answers `None` when
/// `write` reads anything but the 64-bit `Var("SP")` — another register, an
/// interned `SymVar`, a quantifier — because only SP is tracked across blocks,
/// so such a write cannot be re-expressed. This is the same substitution the
/// dataflow applies to a block's last write.
#[must_use]
pub fn stack_pointer_after_write(write: &Formula, sp_at_block_entry: &Formula) -> Option<Formula> {
    formula_reads_only_machine_sp(write)
        .then(|| substitute_block_entry_sp(write, sp_at_block_entry))
}

/// Read a bitvector literal as a SIGNED machine value.
///
/// A `sub rsp, 32` may lift as either `BvSub(SP, 32)` or `BvAdd(SP, 2^64 - 32)`;
/// the second is the same displacement written as an unsigned wrap, so the
/// literal is interpreted in two's complement at its own width.
fn bitvec_as_signed(value: i128, width: u32) -> Option<i64> {
    if width == 0 || width > 64 {
        return None;
    }
    let modulus = 1i128 << width;
    let wrapped = value.rem_euclid(modulus);
    let signed = if wrapped < modulus / 2 { wrapped } else { wrapped - modulus };
    i64::try_from(signed).ok()
}

/// The constant displacement of `formula` from FUNCTION-entry SP, when it is one.
///
/// Recognises `SP`, and `SP ± literal` nested to any depth, all at 64 bits, each
/// literal read in two's complement (see `bitvec_as_signed`). `None` for anything
/// that mixes in another variable or a non-literal, for `literal - SP` (a
/// negation, not a displacement), and for a sum that leaves `i64`.
///
/// "SP" is exactly `function_entry_stack_pointer()`, the one node this module
/// substitutes: an interned `SymVar` or an `SP` at another width would survive
/// the re-expression un-substituted, still meaning its block's SP, and must not
/// be read as function-entry SP. The widths are pinned for the same reason.
///
/// Meaningful on a formula this module returns (`StackPointerFlow`'s values, or
/// `stack_pointer_after_write`'s), which are over function-entry SP. On a raw
/// lifted formula the answer is relative to that formula's BLOCK — which is the
/// mistake this function exists to keep callers from making twice.
#[must_use]
pub fn function_entry_sp_offset(formula: &Formula) -> Option<i64> {
    match formula {
        _ if is_function_entry_stack_pointer(formula) => Some(0),
        Formula::BvAdd(lhs, rhs, 64) => match (&**lhs, &**rhs) {
            (_, Formula::BitVec { value, width: 64 }) => {
                function_entry_sp_offset(lhs)?.checked_add(bitvec_as_signed(*value, 64)?)
            }
            (Formula::BitVec { value, width: 64 }, _) => {
                function_entry_sp_offset(rhs)?.checked_add(bitvec_as_signed(*value, 64)?)
            }
            _ => None,
        },
        // Only `sp - literal`. `literal - sp` is a negation, not a displacement.
        Formula::BvSub(lhs, rhs, 64) => match &**rhs {
            Formula::BitVec { value, width: 64 } => {
                function_entry_sp_offset(lhs)?.checked_sub(bitvec_as_signed(*value, 64)?)
            }
            _ => None,
        },
        _ => None,
    }
}

/// `write` — over a block's ENTRY state — re-expressed over FUNCTION-entry state,
/// by substituting, in one simultaneous pass, SP and the tracked frame pointer at
/// that block's entry. `Unknown` when the write reads any other variable, an
/// interned `SymVar` or a quantifier, or reads a tracked register whose value at
/// the block's entry is not derivable. A write that reads no state at all is its
/// own value.
fn re_express_over_function_entry(
    write: &Formula,
    at_entry: &Registers,
    frame_pointer: Option<&Formula>,
) -> EntrySp {
    let sp_value = at_entry.sp.known_ref();
    let fp_value = at_entry.fp.known_ref();
    let derivable = trust_types::all_formula_nodes(write, &mut |node| match node {
        Formula::Var(..) if is_function_entry_stack_pointer(node) => sp_value.is_some(),
        Formula::Var(..) if Some(node) == frame_pointer => fp_value.is_some(),
        Formula::Var(..) | Formula::SymVar(..) | Formula::Forall(..) | Formula::Exists(..) => {
            false
        }
        _ => true,
    });
    if !derivable {
        return EntrySp::Unknown;
    }
    EntrySp::Known(write.clone().map(&mut |node| match (sp_value, fp_value) {
        (Some(sp), _) if is_function_entry_stack_pointer(&node) => sp.clone(),
        (_, Some(fp)) if Some(&node) == frame_pointer => fp.clone(),
        _ => node,
    }))
}

fn register_after_block(
    write: &RegisterWrite,
    unchanged: &EntrySp,
    at_entry: &Registers,
    entry_state_is_function_entry: bool,
    frame_pointer: Option<&Formula>,
) -> EntrySp {
    match write {
        RegisterWrite::Preserves => unchanged.clone(),
        RegisterWrite::Unreadable => EntrySp::Unknown,
        // This block's entry state IS the function's entry state, so every
        // variable in the write already names a function-entry value.
        RegisterWrite::Writes(formula) if entry_state_is_function_entry => {
            EntrySp::Known(formula.clone())
        }
        RegisterWrite::Writes(formula) => {
            re_express_over_function_entry(formula, at_entry, frame_pointer)
        }
    }
}

fn registers_after_block(
    writes: Option<&BlockWrites>,
    at_entry: &Registers,
    entry_state_is_function_entry: bool,
    frame_pointer: Option<&Formula>,
) -> Registers {
    if at_entry.sp == EntrySp::Unreached {
        return Registers::unreached();
    }
    let Some(BlockWrites { sp, fp }) = writes else {
        return Registers { sp: EntrySp::Unknown, fp: EntrySp::Unknown };
    };
    let after = |write, unchanged| {
        register_after_block(
            write,
            unchanged,
            at_entry,
            entry_state_is_function_entry,
            frame_pointer,
        )
    };
    Registers { sp: after(sp, &at_entry.sp), fp: after(fp, &at_entry.fp) }
}

/// SP at the entry and at the exit of every block of a lifted body, by block
/// position, over FUNCTION-entry SP. See the module note for the model.
#[derive(Debug, Clone, PartialEq)]
pub struct StackPointerFlow {
    at_entry: Vec<Option<Formula>>,
    at_exit: Vec<Option<Formula>>,
}

impl StackPointerFlow {
    fn underivable(count: usize) -> Self {
        Self { at_entry: vec![None; count], at_exit: vec![None; count] }
    }

    /// SP when control arrives at block `position`, over function-entry SP —
    /// the value that block's own `Var("SP")` denotes — or `None` where it is
    /// not derivable on every path (including an unreachable block).
    #[must_use]
    pub fn at_block_entry(&self, position: usize) -> Option<&Formula> {
        self.at_entry.get(position).and_then(Option::as_ref)
    }

    /// SP when block `position` finishes, over function-entry SP, or `None`
    /// where it is not derivable.
    #[must_use]
    pub fn at_block_exit(&self, position: usize) -> Option<&Formula> {
        self.at_exit.get(position).and_then(Option::as_ref)
    }

    /// SP at the end of every block, by position.
    #[must_use]
    pub fn into_block_exits(self) -> Vec<Option<Formula>> {
        self.at_exit
    }
}

/// Carry SP from function entry through `body`'s CFG, tracking no other
/// register: `stack_pointer_flow_with_frame_pointer` with no frame pointer.
#[must_use]
pub fn stack_pointer_flow(
    body: &VerifiableBody,
    entry: Option<usize>,
    sp_local: usize,
    read_sp_write: impl Fn(&Rvalue) -> Option<Formula>,
) -> StackPointerFlow {
    stack_pointer_flow_with_frame_pointer(body, entry, sp_local, None, read_sp_write)
}

/// Carry SP — and, when named, the frame pointer — from function entry through
/// `body`'s CFG. Only SP is reported.
///
/// * `entry` is the position of the function's entry block
///   (`lifted_entry_block` for a lifted function); `None` or out of range
///   voids the analysis.
/// * `sp_local` is the stack-pointer local.
/// * `frame_pointer`, when given, is carried beside SP (see the module note); a
///   frame pointer whose local IS `sp_local` is ignored.
/// * `read_write` reads the value of a whole-local write; an SP write it answers
///   `None` for makes its block's effect opaque, a frame-pointer write it
///   answers `None` for makes the frame pointer not derivable.
///
/// The whole analysis is void — every block `None` — when block ids are not
/// vector positions, a terminator's successors or SP effect are not modelled
/// (anything but `Goto`, `SwitchInt`, `Assert`, `Return`, `TailCall`,
/// `Unreachable`, `Resume`), a successor is out of range, or the fixpoint fails
/// to converge within its bound. A back edge into the entry block does not void
/// it: the entry block's writes are then re-expressed like any other block's,
/// over the JOIN of function-entry SP and every back edge.
#[must_use]
pub fn stack_pointer_flow_with_frame_pointer(
    body: &VerifiableBody,
    entry: Option<usize>,
    sp_local: usize,
    frame_pointer: Option<&FramePointer>,
    read_write: impl Fn(&Rvalue) -> Option<Formula>,
) -> StackPointerFlow {
    let frame_pointer = frame_pointer.filter(|fp| fp.local != sp_local);
    let fp_register = frame_pointer.map(|fp| &fp.register);
    let blocks = &body.blocks;
    let count = blocks.len();

    // Block ids are vector positions (`validate_function`'s invariant) and the
    // entry block is the CFG's entry; anything else voids the analysis.
    if blocks.iter().enumerate().any(|(position, block)| block.id.0 != position) {
        return StackPointerFlow::underivable(count);
    }
    let Some(entry) = entry.filter(|&entry| entry < count) else {
        return StackPointerFlow::underivable(count);
    };

    // Predecessors from an exhaustive match over the lift's terminator
    // vocabulary. A missed edge would make a block look better-constrained than
    // it is, so a terminator whose SP effect or successors are not modelled
    // voids the whole analysis instead.
    let mut predecessors: Vec<Vec<usize>> = vec![Vec::new(); count];
    for (position, block) in blocks.iter().enumerate() {
        let mut add_pred = |successor: BlockId| -> bool {
            let Some(preds) = predecessors.get_mut(successor.0) else {
                return false;
            };
            preds.push(position);
            true
        };
        match &block.terminator {
            Terminator::Goto(target) => {
                if !add_pred(*target) {
                    return StackPointerFlow::underivable(count);
                }
            }
            Terminator::SwitchInt { targets, otherwise, .. } => {
                for &(_, target) in targets {
                    if !add_pred(target) {
                        return StackPointerFlow::underivable(count);
                    }
                }
                if !add_pred(*otherwise) {
                    return StackPointerFlow::underivable(count);
                }
            }
            Terminator::Assert { target, unwind, .. } => {
                if !add_pred(*target) {
                    return StackPointerFlow::underivable(count);
                }
                if let Some(cleanup) = unwind.cleanup_target()
                    && !add_pred(cleanup)
                {
                    return StackPointerFlow::underivable(count);
                }
            }
            Terminator::Return
            | Terminator::TailCall { .. }
            | Terminator::Unreachable
            | Terminator::Resume => {}
            _ => return StackPointerFlow::underivable(count),
        }
    }

    let writes: Vec<Option<BlockWrites>> = blocks
        .iter()
        .map(|block| block_writes(block, sp_local, frame_pointer.map(|fp| fp.local), &read_write))
        .collect();
    // A back edge into the entry block means its entry state is not always the
    // function's entry state.
    let entry_is_pristine = predecessors[entry].is_empty();

    // Round-robin fixpoint over a flat lattice (Unreached < Known < Unknown)
    // per register, with monotone transfer: each of a block's two values moves
    // at most twice, so `4 * count + 1` rounds always suffice. Hitting the bound
    // anyway is treated as "not derivable", never as convergence.
    let at_function_entry = Registers {
        sp: EntrySp::Known(function_entry_stack_pointer()),
        fp: fp_register.map_or(EntrySp::Unknown, |register| EntrySp::Known(register.clone())),
    };
    let mut at_entry = vec![Registers::unreached(); count];
    let mut at_exit = vec![Registers::unreached(); count];
    for _round in 0..=(4 * count + 1) {
        let mut changed = false;
        for position in 0..count {
            let mut arriving =
                if position == entry { at_function_entry.clone() } else { Registers::unreached() };
            for &pred in &predecessors[position] {
                arriving.join_ref(&at_exit[pred]);
            }
            let next = registers_after_block(
                writes[position].as_ref(),
                &arriving,
                position == entry && entry_is_pristine,
                fp_register,
            );
            at_entry[position] = arriving;
            if next != at_exit[position] {
                at_exit[position] = next;
                changed = true;
            }
        }
        // A round that changed nothing read only final exit values, so the
        // entry values it recorded are final too.
        if !changed {
            return StackPointerFlow {
                at_entry: at_entry.into_iter().map(|registers| registers.sp.known()).collect(),
                at_exit: at_exit.into_iter().map(|registers| registers.sp.known()).collect(),
            };
        }
    }
    StackPointerFlow::underivable(count)
}

#[cfg(test)]
mod tests {
    use trust_types::{Operand, Place, SourceSpan};

    use super::*;

    const SP: usize = 32;

    fn sp() -> Formula {
        function_entry_stack_pointer()
    }

    fn bv(value: i128) -> Formula {
        Formula::BitVec { value, width: 64 }
    }

    fn sub(value: i128) -> Formula {
        Formula::BvSub(Box::new(sp()), Box::new(bv(value)), 64)
    }

    fn write(value: Formula) -> Statement {
        Statement::Assign {
            place: Place::local(SP),
            rvalue: Rvalue::Use(Operand::Symbolic(value)),
            span: SourceSpan::binary_address(0x1000),
        }
    }

    fn symbolic(rvalue: &Rvalue) -> Option<Formula> {
        match rvalue {
            Rvalue::Use(Operand::Symbolic(formula)) => Some(formula.clone()),
            _ => None,
        }
    }

    fn body(blocks: Vec<(Vec<Statement>, Terminator)>) -> VerifiableBody {
        VerifiableBody {
            locals: vec![],
            blocks: blocks
                .into_iter()
                .enumerate()
                .map(|(position, (stmts, terminator))| BasicBlock {
                    id: BlockId(position),
                    stmts,
                    terminator,
                })
                .collect(),
            arg_count: 0,
            return_ty: trust_types::Ty::Unit,
            datatype_defs: Default::default(),
        }
    }

    fn branch(to: usize, otherwise: usize) -> Terminator {
        Terminator::SwitchInt {
            discr: Operand::Symbolic(Formula::Var("X0".into(), Sort::BitVec(64))),
            targets: vec![(1, BlockId(to))],
            otherwise: BlockId(otherwise),
            exhaustive_enum_unreachable: false,
            span: SourceSpan::binary_address(0x1004),
        }
    }

    /// The ENTRY values: SP a block's own `Var("SP")` denotes. bb0 moves SP
    /// and branches to two blocks that each restore it; each arrives at
    /// `entry - 16`, and each exit is the write re-expressed over it.
    #[test]
    fn entry_values_are_the_sp_each_block_starts_from() {
        let flow = stack_pointer_flow(
            &body(vec![
                (vec![write(sub(16))], branch(2, 1)),
                (
                    vec![write(Formula::BvAdd(Box::new(sp()), Box::new(bv(16)), 64))],
                    Terminator::Return,
                ),
                (vec![], Terminator::Return),
            ]),
            Some(0),
            SP,
            symbolic,
        );

        assert_eq!(flow.at_block_entry(0), Some(&sp()));
        assert_eq!(flow.at_block_entry(1), Some(&sub(16)));
        assert_eq!(flow.at_block_entry(2), Some(&sub(16)));
        assert_eq!(
            flow.at_block_exit(1),
            Some(&Formula::BvAdd(Box::new(sub(16)), Box::new(bv(16)), 64))
        );
        assert_eq!(flow.at_block_exit(2), Some(&sub(16)));
    }

    /// Paths that disagree give no entry value at the join, and an
    /// unreachable block has none either.
    #[test]
    fn a_disagreeing_join_and_an_unreachable_block_have_no_entry_value() {
        let flow = stack_pointer_flow(
            &body(vec![
                (vec![], branch(2, 1)),
                (vec![write(sub(16))], Terminator::Goto(BlockId(2))),
                (vec![], Terminator::Return),
                (vec![], Terminator::Return),
            ]),
            Some(0),
            SP,
            symbolic,
        );

        assert_eq!(flow.at_block_entry(1), Some(&sp()));
        assert_eq!(flow.at_block_entry(2), None, "entry SP on one path, entry - 16 on the other");
        assert_eq!(flow.at_block_entry(3), None, "nothing reaches bb3");
        assert_eq!(flow.at_block_entry(4), None, "out of range");
    }

    /// A back edge into the entry block: its entry value is the join of the
    /// first arrival and every later one, so a loop that moves SP has none.
    #[test]
    fn a_back_edge_into_entry_joins_every_arrival() {
        let flow = stack_pointer_flow(
            &body(vec![(vec![write(sub(16))], branch(0, 1)), (vec![], Terminator::Return)]),
            Some(0),
            SP,
            symbolic,
        );

        assert_eq!(flow.at_block_entry(0), None);
        assert_eq!(flow.at_block_exit(1), None);
    }

    /// Everything outside the modelled shape voids the analysis.
    #[test]
    fn an_unmodelled_shape_voids_every_block() {
        let blocks = || {
            vec![(vec![write(sub(16))], Terminator::Goto(BlockId(1))), (vec![], Terminator::Return)]
        };
        let void = |flow: StackPointerFlow| {
            (0..2).all(|b| flow.at_block_entry(b).is_none() && flow.at_block_exit(b).is_none())
        };

        assert!(void(stack_pointer_flow(&body(blocks()), None, SP, symbolic)));
        assert!(void(stack_pointer_flow(&body(blocks()), Some(2), SP, symbolic)));

        let mut misnumbered = body(blocks());
        misnumbered.blocks[1].id = BlockId(7);
        assert!(void(stack_pointer_flow(&misnumbered, Some(0), SP, symbolic)));

        let mut dangling = body(blocks());
        dangling.blocks[0].terminator = Terminator::Goto(BlockId(9));
        assert!(void(stack_pointer_flow(&dangling, Some(0), SP, symbolic)));

        let mut call = body(blocks());
        call.blocks[0].terminator = Terminator::Drop {
            place: Place::local(1),
            target: BlockId(1),
            span: SourceSpan::binary_address(0x1004),
            unwind: Default::default(),
        };
        assert!(void(stack_pointer_flow(&call, Some(0), SP, symbolic)));
    }

    fn fp() -> FramePointer {
        FramePointer::aarch64()
    }

    fn x29() -> Formula {
        Formula::Var("X29".into(), Sort::BitVec(64))
    }

    fn write_fp(value: Formula) -> Statement {
        Statement::Assign {
            place: Place::local(fp().local()),
            rvalue: Rvalue::Use(Operand::Symbolic(value)),
            span: SourceSpan::binary_address(0x1000),
        }
    }

    fn plus(base: Formula, value: i128) -> Formula {
        Formula::BvAdd(Box::new(base), Box::new(bv(value)), 64)
    }

    /// The frame pointer's identity is the lift's own: X29's local and the
    /// variable `MachineState::symbolic` names it by; RBP likewise on x86-64.
    #[test]
    fn frame_pointers_are_the_lifts_own_registers() {
        assert_eq!(fp().local(), 30);
        assert_eq!(fp().register, x29());
        assert_eq!(FramePointer::x86_64().local(), 6);
        assert_eq!(FramePointer::x86_64().register, Formula::Var("X5".into(), Sort::BitVec(64)));
    }

    /// `mov sp, x29` in a LATER block: its write reads X29 at that block's entry,
    /// which the tracked frame pointer re-expresses over function entry. bb0
    /// moves SP and the frame pointer by DIFFERENT amounts, so a substitution
    /// that replaced X29 and then re-substituted the result's SP (or the reverse)
    /// would produce a different formula than the one asserted.
    #[test]
    fn a_frame_pointer_epilogue_in_a_later_block_is_re_expressed() {
        let blocks = || {
            body(vec![
                (vec![write(sub(32)), write_fp(sub(16))], Terminator::Goto(BlockId(1))),
                (vec![write(plus(x29(), 16))], Terminator::Return),
            ])
        };
        let tracked =
            stack_pointer_flow_with_frame_pointer(&blocks(), Some(0), SP, Some(&fp()), symbolic);
        assert_eq!(tracked.at_block_entry(1), Some(&sub(32)));
        assert_eq!(tracked.at_block_exit(1), Some(&plus(sub(16), 16)));

        // SP alone: X29 is not tracked, so the same body has no exit value.
        let untracked = stack_pointer_flow(&blocks(), Some(0), SP, symbolic);
        assert_eq!(untracked.at_block_exit(1), None);
        assert_eq!(untracked.at_block_entry(1), tracked.at_block_entry(1));
    }

    /// The frame pointer is carried by exactly SP's rules, so every way of
    /// losing it on one path leaves the epilogue's SP underivable at the join.
    #[test]
    fn a_frame_pointer_lost_on_any_path_is_not_carried() {
        let unreadable = Statement::Assign {
            place: Place::local(fp().local()),
            rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
            span: SourceSpan::binary_address(0x1008),
        };
        for (label, clobber) in [
            ("reads an untracked register", write_fp(Formula::Var("X0".into(), Sort::BitVec(64)))),
            ("moves it on one path only", write_fp(plus(x29(), 8))),
            ("is unreadable", unreadable),
        ] {
            let flow = stack_pointer_flow_with_frame_pointer(
                &body(vec![
                    (vec![write(sub(16)), write_fp(sub(16))], branch(2, 1)),
                    (vec![clobber], Terminator::Goto(BlockId(2))),
                    (vec![write(plus(x29(), 16))], Terminator::Return),
                ]),
                Some(0),
                SP,
                Some(&fp()),
                symbolic,
            );
            assert_eq!(flow.at_block_entry(2), Some(&sub(16)), "{label}: SP itself still agrees");
            assert_eq!(flow.at_block_exit(2), None, "{label}");
        }
    }

    /// Never set in the function, the frame pointer is the CALLER's: a return
    /// that restores SP from it is expressed over that unconstrained value, not
    /// over function-entry SP, so nothing ties it to a balanced stack.
    #[test]
    fn an_unset_frame_pointer_is_the_callers() {
        let flow = stack_pointer_flow_with_frame_pointer(
            &body(vec![
                (vec![], Terminator::Goto(BlockId(1))),
                (vec![write(x29())], Terminator::Return),
            ]),
            Some(0),
            SP,
            Some(&fp()),
            symbolic,
        );
        assert_eq!(flow.at_block_exit(1), Some(&x29()));
    }

    /// The displacement reader must reject anything that is not entry-SP plus a
    /// constant, whatever it is made of. (Moved from trust-decompile, which
    /// owned it until trust-vcgen needed the same answer.)
    #[test]
    fn only_entry_sp_plus_a_constant_is_a_displacement() {
        assert_eq!(function_entry_sp_offset(&sp()), Some(0));
        // `32 - sp` is a negation of the stack pointer, not a displacement.
        assert_eq!(
            function_entry_sp_offset(&Formula::BvSub(Box::new(bv(32)), Box::new(sp()), 64)),
            None
        );
        // A different register is not the stack pointer.
        assert_eq!(function_entry_sp_offset(&Formula::Var("X0".into(), Sort::BitVec(64))), None);
        // A bare constant has no stack-pointer base.
        assert_eq!(function_entry_sp_offset(&bv(8)), None);
        // Nesting is fine as long as every added term is a literal.
        assert_eq!(function_entry_sp_offset(&plus(plus(sp(), 8), 8)), Some(16));
        // Only the node the dataflow substitutes is SP. An interned or
        // differently-sized `SP` would survive the re-expression still meaning
        // its block's SP, so reading it as function-entry SP could mislabel it.
        let interned = Formula::SymVar(trust_types::Symbol::intern("SP"), Sort::BitVec(64));
        assert_eq!(function_entry_sp_offset(&interned), None);
        assert_eq!(function_entry_sp_offset(&Formula::Var("SP".into(), Sort::BitVec(32))), None);
        // A literal at another width than its operation is not a displacement.
        assert_eq!(
            function_entry_sp_offset(&Formula::BvAdd(
                Box::new(sp()),
                Box::new(Formula::BitVec { value: 0xFFFF_FFF0, width: 32 }),
                64,
            )),
            None
        );
    }

    /// An unsigned-wrapped literal is the same displacement as its signed
    /// spelling: `SP + (2^64 - 32)` is `SP - 32`, never "SP plus a huge number".
    #[test]
    fn a_wrapped_literal_is_read_in_twos_complement() {
        assert_eq!(function_entry_sp_offset(&plus(sp(), (1i128 << 64) - 32)), Some(-32));
        assert_eq!(function_entry_sp_offset(&sub(-16)), Some(16));
    }

    /// The re-expression is refused for a write that reads anything but the
    /// 64-bit `Var("SP")`, because nothing else is tracked across blocks.
    #[test]
    fn only_a_write_over_sp_alone_is_re_expressed() {
        let at_entry = sub(16);
        assert_eq!(
            stack_pointer_after_write(
                &Formula::BvAdd(Box::new(sp()), Box::new(bv(8)), 64),
                &at_entry
            ),
            Some(Formula::BvAdd(Box::new(sub(16)), Box::new(bv(8)), 64))
        );
        for write in [
            Formula::Var("X29".into(), Sort::BitVec(64)),
            Formula::BvAdd(
                Box::new(sp()),
                Box::new(Formula::Var("X0".into(), Sort::BitVec(64))),
                64,
            ),
            Formula::Var("SP".into(), Sort::BitVec(32)),
            Formula::SymVar(trust_types::Symbol::intern("SP"), Sort::BitVec(64)),
        ] {
            assert_eq!(stack_pointer_after_write(&write, &at_entry), None, "{write:?}");
        }
    }
}
