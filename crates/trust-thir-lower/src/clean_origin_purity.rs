//! Trust (plan step 3.5, docs/design/2026-10-02-step3-lean-through-trust-ir.md §5.1, §2.3, §12
//! item 8): the Clean language's two Rust-callee rules decided ON TRUST-IR, for F1.
//!
//! A Clean `def` that calls Rust (`RustCallChain`) treats each Rust callee as a pure kernel
//! value, so the language refuses (1) a callee that is not provably PURE and (2) a callee that
//! leads back into the `def` (a CROSS-LANGUAGE CYCLE). On the MIR lane both are decided inside the
//! `clean_origin_mir` provider, over MIR (`rust_callee_is_pure`, `callee_reaches_a_gate_on_this_stack`).
//! F1 never builds that MIR (§5.7), so on F1 both are decided here, over the crate's trust-ir:
//!
//! * PURITY ([`rust_callee_purity`]) over the callee's CONSERVED trust-ir effect census (D28):
//!   a body is read only when `effect_conservation::finalize` judged its trust-ir to carry every
//!   effect of its MIR (`conserved_function_ids`). A body reached through the callee's direct
//!   calls is walked the same way. Deny by default: an instruction outside the pure vocabulary
//!   below is either a finding (IMPURE) or a reason the census cannot decide (UNDECIDED), never
//!   a pass.
//! * THE CYCLE ([`cross_language_cycles`]) over the PUBLISHED module's call graph (every body,
//!   conserved or not, so an edge a withdrawn body carries is still seen): a `Producer::Clean`
//!   function whose strongly connected component also holds a function of another producer.
//!
//! # The census vocabulary, and how it mirrors the MIR walk
//!
//! The MIR walk refuses a write outside the frame, a read through a reference whose referent is
//! not provably in the frame, a raw-pointer or thread-local creation, an indirect or foreign call,
//! inline asm and a drop, and admits a panic check (a pure callee may panic: panic freedom and
//! termination are the callee's own obligations). The census reads the same things in trust-ir:
//!
//! * IMPURE: a `Load`/`Store`/`MemCopy`/`MemSet` through a pointer whose root is not the body's
//!   own `Alloca` (a parameter, a global, a loaded pointer: `effect_conservation::ir_roots`, which
//!   reads an unknown root as escaping); any atomic or fence; an indirect call; a drop; an
//!   allocation, free or reference-count operation; the address of a global or of a symbol; a
//!   yield; inline asm (a dialect op).
//! * PURE: scalar arithmetic, comparisons, casts, selects, copies, aggregates, the body's own
//!   stack slots and pointer arithmetic over them, control flow, `Assume`, a panic check, and a
//!   DIRECT call, whose callee is walked in turn.
//! * UNDECIDED: a callee with no body in the module (an upstream or foreign function, whose
//!   trust-ir reaches this crate only at increment 6, or a body withdrawn because its trust-ir is
//!   not conserved), an `undef`, and anything else.
//!
//! Every block is walked, reachable or not, as the MIR walk does.
//!
//! # What the caller does with each answer (rustc_mir_transform::clean_origin_ir)
//!
//! IMPURE and a cycle are the language's refusal, fatal on F1 as on the MIR lane. UNDECIDED is
//! not a pass: the row is published below `gate` (no `RustCallChain` row is a gate target; plan
//! step 3.1(b) must require a PURE verdict before one can be), and the MIR walk is consulted to
//! REFUSE only (docs/DECISION_QUEUE.md STEP3.5-PURITY-UNDECIDED), so F1 never accepts a program the
//! MIR lane refuses. PURE is never a license either: it is the precondition the gate's pure
//! callee model needs, not a proof grade.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::{BTreeSet, VecDeque};

use trust_ir::{BlockId, Constant, FuncId, Function, Inst, Module, Producer};

use crate::effect_conservation::IrRoot;

/// The census's answer for one Rust callee (and everything it calls).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CalleePurity {
    /// Every body the callee reaches is in the module, conserved, and inside the pure vocabulary.
    Pure,
    /// A finding: `function` (by name) does `finding`.
    Impure { function: String, finding: String },
    /// The census cannot decide: `function` (by name), because `reason`.
    Undecided { function: String, reason: String },
}

/// What one instruction is, for the census.
enum Reading {
    Pure,
    Calls(FuncId),
    /// An effect: an access to memory outside the frame, an atomic, an indirect call, a drop, an
    /// allocation, a yield, asm.
    Impure(String),
    /// The address of a global or symbol, which no access in this body used. Refused like the MIR
    /// walk refuses a raw-pointer creation, but reported only when the body has no effect to
    /// name instead (the access is the finding a reader can act on).
    TakesAddress(String),
    Undecided(String),
}

fn root_name(root: IrRoot) -> String {
    match root {
        IrRoot::Arg(i) => format!("parameter {i}"),
        IrRoot::Global => "a global".to_string(),
        IrRoot::Indirect => "a pointer loaded from memory (or of unknown origin)".to_string(),
        IrRoot::Local => "the body's own stack".to_string(),
    }
}

fn read_instruction(inst: &Inst, root_of: &dyn Fn(&trust_ir::ValueId) -> IrRoot) -> Reading {
    let through = |what: &str, ptr: &trust_ir::ValueId| match root_of(ptr) {
        IrRoot::Local => Reading::Pure,
        root => Reading::Impure(format!(
            "{what} memory outside its own frame, through a pointer rooted at {}",
            root_name(root)
        )),
    };
    match inst {
        Inst::BinOp { .. }
        | Inst::UnOp { .. }
        | Inst::Overflow { .. }
        | Inst::ICmp { .. }
        | Inst::FCmp { .. }
        | Inst::Cast { .. }
        | Inst::Select { .. }
        | Inst::Copy { .. }
        | Inst::ExtractField { .. }
        | Inst::InsertField { .. }
        | Inst::ExtractElement { .. }
        | Inst::InsertElement { .. }
        | Inst::MakeAggregate { .. }
        | Inst::ArraySplat { .. }
        | Inst::Br { .. }
        | Inst::CondBr { .. }
        | Inst::Switch { .. }
        | Inst::Return { .. }
        | Inst::Unreachable
        | Inst::Assume { .. }
        | Inst::Assert { .. }
        | Inst::AssertInvoke { .. }
        | Inst::LandingPad { .. }
        | Inst::Resume { .. }
        | Inst::NullPtr
        | Inst::Alloca { .. }
        | Inst::GEP { .. }
        | Inst::PtrData { .. }
        | Inst::PtrMetadata { .. }
        | Inst::PtrFromParts { .. }
        | Inst::Borrow { .. }
        | Inst::BorrowMut { .. }
        | Inst::EndBorrow { .. }
        | Inst::OpenFrame { .. }
        | Inst::BindSlot { .. }
        | Inst::LoadSlot { .. }
        | Inst::CloseFrame { .. } => Reading::Pure,
        Inst::Const { value, .. } => match value {
            Constant::SymbolAddr { symbol, .. } => {
                Reading::TakesAddress(format!("takes the address of the symbol `{symbol}`"))
            }
            Constant::Uninit | Constant::Ext(_) => {
                Reading::Undecided(format!("a constant the census does not read ({value:?})"))
            }
            // Data, and function values: calling one is an indirect call, refused where it is.
            _ => Reading::Pure,
        },
        Inst::Load { ptr, .. } => through("reads", ptr),
        Inst::Store { ptr, .. } | Inst::MemSet { dst: ptr, .. } => through("writes", ptr),
        Inst::MemCopy { dst, src, .. } => match through("reads", src) {
            Reading::Pure => through("writes", dst),
            impure => impure,
        },
        Inst::AtomicLoad { .. }
        | Inst::AtomicStore { .. }
        | Inst::AtomicRMW { .. }
        | Inst::CmpXchg { .. }
        | Inst::Fence { .. } => Reading::Impure("performs an atomic operation".to_string()),
        Inst::Call { callee, .. }
        | Inst::CallCannotUnwind { callee, .. }
        | Inst::Invoke { callee, .. } => Reading::Calls(*callee),
        Inst::CallIndirect { .. }
        | Inst::CallIndirectCannotUnwind { .. }
        | Inst::InvokeIndirect { .. } => Reading::Impure("makes an indirect call".to_string()),
        Inst::Drop { .. } | Inst::DropInvoke { .. } => {
            Reading::Impure("runs drop glue (a destructor)".to_string())
        }
        Inst::HeapAlloc { .. }
        | Inst::Dealloc { .. }
        | Inst::Retain { .. }
        | Inst::Release { .. }
        | Inst::IsUnique { .. } => {
            Reading::Impure("allocates, frees or counts references to heap memory".to_string())
        }
        Inst::GlobalAddr { .. } => {
            Reading::TakesAddress("takes the address of a global".to_string())
        }
        Inst::CoroSuspend { .. } => Reading::Impure("yields (a coroutine suspend)".to_string()),
        Inst::DialectOp(_) => Reading::Impure("executes a dialect op (inline asm)".to_string()),
        Inst::Undef { .. } => Reading::Undecided(
            "carries an `undef` value: its trust-ir abstracts a value of the program (D28)"
                .to_string(),
        ),
        other => Reading::Undecided(format!(
            "`{:?}` is outside the purity census's vocabulary",
            other.shape()
        )),
    }
}

/// The census's verdict for the Rust callee `callee` of a Clean row, read over `module` (the
/// published crate module). `conserved` is the set of functions the effect-conservation check
/// judged CONSERVED (`effect_conservation::conserved_function_ids`): a body of any producer but
/// `Clean` is read only when it is in it. A `Producer::Clean` body is read as it is: its census is
/// its declaration's (design §5.3), and the Rust callees it calls are walked in turn. PURE.
pub fn rust_callee_purity(
    module: &Module,
    conserved: &BTreeSet<FuncId>,
    callee: FuncId,
) -> CalleePurity {
    let mut seen = BTreeSet::new();
    let mut work = VecDeque::from([callee]);
    let mut undecided: Option<CalleePurity> = None;
    while let Some(id) = work.pop_front() {
        if !seen.insert(id) {
            continue;
        }
        let Some(function) = module.function_by_id(id) else {
            undecided.get_or_insert(CalleePurity::Undecided {
                function: format!("FuncId({})", id.index()),
                reason: "it is not a function of this crate's trust-ir module".to_string(),
            });
            continue;
        };
        if function.is_declaration() {
            undecided.get_or_insert(CalleePurity::Undecided {
                function: display_name(function),
                reason: "it has no body in this crate's trust-ir module (an upstream or foreign \
                         function: upstream trust-ir reaches a downstream compile at step 2 \
                         increment 6)"
                    .to_string(),
            });
            continue;
        }
        if function.producer != Some(Producer::Clean) && !conserved.contains(&id) {
            undecided.get_or_insert(CalleePurity::Undecided {
                function: display_name(function),
                reason: "its trust-ir is not conserved: the effect-conservation check did not \
                         find it to carry every effect of its MIR (D28), so its census is not the \
                         program's"
                    .to_string(),
            });
            continue;
        }
        match judge_body(function) {
            Ok(callees) => work.extend(callees),
            Err(CalleePurity::Impure { function, finding }) => {
                return CalleePurity::Impure { function, finding };
            }
            Err(found) => {
                undecided.get_or_insert(found);
            }
        }
    }
    undecided.unwrap_or(CalleePurity::Pure)
}

/// One body: `Ok` with its direct callees (in instruction order) when every instruction is in the
/// pure vocabulary, `Err` with the first IMPURE finding, else the first UNDECIDED reason.
/// The name a human-facing census verdict prints: the source def path the
/// producer recorded in `display_path`, not the link-time symbol `name` has
/// carried since WS5.2 (F-087) — a verdict naming `_RNvCs...4bump` tells the
/// author nothing; the MIR lane's twin diagnostic says `fn bump`.
fn display_name(function: &Function) -> String {
    function.display_path.clone().unwrap_or_else(|| function.name.clone())
}

fn judge_body(function: &Function) -> Result<Vec<FuncId>, CalleePurity> {
    let roots = crate::effect_conservation::ir_roots(function);
    let root_of = |v: &trust_ir::ValueId| roots.get(v).copied().unwrap_or(IrRoot::Indirect);
    let mut callees = Vec::new();
    let mut undecided = None;
    let mut address = None;
    let impure = |block: BlockId, finding: String| CalleePurity::Impure {
        function: display_name(function),
        finding: format!("block {}: {finding}", block.index()),
    };
    for block in &function.blocks {
        for node in &block.body {
            match read_instruction(&node.inst, &root_of) {
                Reading::Pure => {}
                Reading::Calls(callee) => callees.push(callee),
                Reading::Impure(finding) => return Err(impure(block.id, finding)),
                Reading::TakesAddress(finding) => {
                    address.get_or_insert_with(|| impure(block.id, finding));
                }
                Reading::Undecided(reason) => {
                    undecided.get_or_insert(CalleePurity::Undecided {
                        function: display_name(function),
                        reason: format!("block {}: {reason}", block.id.index()),
                    });
                }
            }
        }
    }
    match (address, undecided) {
        (Some(found), _) | (None, Some(found)) => Err(found),
        (None, None) => Ok(callees),
    }
}

/// One EMITTED row of the clean-origin disclosure (`clean_origin_join::CLEAN_ORIGIN_DISCLOSURE_NAME`,
/// the `fn:<id>` invariants): its published `FuncId`, the def's Rust path and the shape tag.
/// Disclosure, read here only to find a def's published Function; never authority.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DisclosedCleanRow {
    pub func_id: FuncId,
    pub def_path: String,
    pub shape: String,
}

/// Every emitted row the clean-origin disclosure of `module` lists. PURE.
pub fn disclosed_emitted_rows(module: &Module) -> Vec<DisclosedCleanRow> {
    let mut rows = Vec::new();
    for spec in &module.spec_modules {
        if spec.name != crate::clean_origin_join::CLEAN_ORIGIN_DISCLOSURE_NAME {
            continue;
        }
        for invariant in &spec.invariants {
            let Some(id) = invariant.name.strip_prefix("fn:") else { continue };
            let Ok(id) = id.parse::<u32>() else { continue };
            let (Some(def_path), Some(shape)) = (
                json_string_field(&invariant.formula, "def_path"),
                json_string_field(&invariant.formula, "shape"),
            ) else {
                continue;
            };
            rows.push(DisclosedCleanRow { func_id: FuncId::new(id), def_path, shape });
        }
    }
    rows
}

/// One JSON string field (`"key":"value"`) of a flat disclosure formula, undoing the minimal
/// escaping `clean_origin_join::json_escape_min` applies. PURE.
fn json_string_field(formula: &str, key: &str) -> Option<String> {
    let needle = format!("\"{key}\":\"");
    let start = formula.find(&needle)? + needle.len();
    let mut out = String::new();
    let mut chars = formula[start..].chars();
    while let Some(c) = chars.next() {
        match c {
            '"' => return Some(out),
            '\\' => match chars.next()? {
                'n' => out.push('\n'),
                'r' => out.push('\r'),
                't' => out.push('\t'),
                'u' => {
                    let hex: String = chars.by_ref().take(4).collect();
                    out.push(char::from_u32(u32::from_str_radix(&hex, 16).ok()?)?);
                }
                other => out.push(other),
            },
            c => out.push(c),
        }
    }
    None
}

/// A cross-language cycle through one Clean-origin function.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CrossLanguageCycle {
    /// The `Producer::Clean` function the cycle passes through.
    pub clean: FuncId,
    /// The cycle from `clean` back to it, both ends included (`[clean, f, .., clean]`), through
    /// the first function of another producer the forward walk meets.
    pub path: Vec<FuncId>,
}

/// The functions `function`'s instructions name: direct calls and function-value constants (a
/// function value may be called later; a cycle through one is a cycle).
fn references(function: &Function) -> Vec<FuncId> {
    let mut out = Vec::new();
    for node in function.blocks.iter().flat_map(|block| block.body.iter()) {
        match &node.inst {
            Inst::Call { callee, .. }
            | Inst::CallCannotUnwind { callee, .. }
            | Inst::Invoke { callee, .. } => out.push(*callee),
            Inst::Const { value: Constant::FnDef(callee), .. }
            | Inst::Const { value: Constant::Closure { func: callee, .. }, .. } => {
                out.push(*callee)
            }
            _ => {}
        }
    }
    out
}

/// Every cross-language cycle of `module` (design §2.3: "SCCs over Rust and Clean rows"): for each
/// `Producer::Clean` function with a body, the cycle through it when its strongly connected
/// component also holds a function of another producer. A Clean function reaching itself only
/// through Clean functions (Clean recursion, kernel-checked) is not one. PURE.
pub fn cross_language_cycles(module: &Module) -> Vec<CrossLanguageCycle> {
    use std::collections::BTreeMap;
    let clean: Vec<FuncId> = module
        .functions
        .iter()
        .filter(|f| f.producer == Some(Producer::Clean) && !f.is_declaration())
        .map(|f| f.id)
        .collect();
    if clean.is_empty() {
        return Vec::new();
    }
    let mut forward: BTreeMap<FuncId, Vec<FuncId>> = BTreeMap::new();
    let mut reverse: BTreeMap<FuncId, Vec<FuncId>> = BTreeMap::new();
    for function in &module.functions {
        for callee in references(function) {
            forward.entry(function.id).or_default().push(callee);
            reverse.entry(callee).or_default().push(function.id);
        }
    }
    let empty = Vec::new();
    // Breadth-first from `from` over `graph`; the parent of every node reached.
    let search = |graph: &BTreeMap<FuncId, Vec<FuncId>>, from: FuncId| {
        let mut parent: BTreeMap<FuncId, Option<FuncId>> = BTreeMap::from([(from, None)]);
        let mut order = Vec::new();
        let mut work = VecDeque::from([from]);
        while let Some(id) = work.pop_front() {
            order.push(id);
            for &next in graph.get(&id).unwrap_or(&empty) {
                if !parent.contains_key(&next) {
                    parent.insert(next, Some(id));
                    work.push_back(next);
                }
            }
        }
        (order, parent)
    };
    let walk_back = |parent: &BTreeMap<FuncId, Option<FuncId>>, to: FuncId| {
        let mut out = vec![to];
        let mut at = to;
        while let Some(Some(p)) = parent.get(&at) {
            out.push(*p);
            at = *p;
        }
        out.reverse();
        out
    };
    let mut cycles = Vec::new();
    for root in clean {
        let (_, reaches_root) = search(&reverse, root);
        let (order, from_root) = search(&forward, root);
        let closing = order.into_iter().skip(1).find(|id| {
            reaches_root.contains_key(id)
                && module.function_by_id(*id).is_some_and(|f| f.producer != Some(Producer::Clean))
        });
        let Some(other) = closing else { continue };
        let mut full = walk_back(&from_root, other);
        let (_, from_other) = search(&forward, other);
        if from_other.contains_key(&root) {
            full.extend(walk_back(&from_other, root).into_iter().skip(1));
            cycles.push(CrossLanguageCycle { clean: root, path: full });
        }
    }
    cycles
}

#[cfg(test)]
#[path = "clean_origin_purity/tests.rs"]
mod tests;
