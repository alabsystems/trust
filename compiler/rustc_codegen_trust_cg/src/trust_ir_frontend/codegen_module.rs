//! Trust (step 2 increment 5, sub-steps 5.4.2 and 5.4.3): THE CODEGEN MODULE of the compiler
//! lane (`-Ztrust-cg-f1-backend=compiler`) — one `trust_ir::Module` per crate, `M_cg`, built from
//! the producer module the frozen instance assembler planned (`star` when it was built,
//! otherwise the finalize-assembled `base`), together with the symbol table S, the placement
//! table P and the never-inline set that trust-cg's `Compiler::compile` and the call-event gate
//! read. Design of record: docs/design/2026-10-01-step2-inc5-real-calls-retarget.md §3.1
//! (rules 1-13); plan docs/design/2026-10-08-step2-inc5-step4-compiler-lane-plan.md §2 (5.4.2)
//! and §3 (5.4.3: rule 9's legalization).
//!
//! # NOT FROZEN YET (INC5.4-FREEZE)
//!
//! This file COMPUTES which bodies, names, linkages and call edges reach machine code, so under
//! the manifest's own rule it joins `scripts/frozen-files.txt` BYTE-IDENTICAL. It is frozen at
//! sub-step 5.4.4, NOT at its landing: 5.4 lands in four commits (5.4.3 added full rule-9 ABI
//! legalization here, 5.4.4 the crate-module and upstream-MIR lanes and the D31(b) stamp), and
//! a waiver argued as "admits nothing new" would be false for 5.4.3. Until the freeze the lane
//! is OPT-IN only: the default `-Ztrust-cg-f1-backend=lir` never calls this file.
//!
//! # PURE
//!
//! No `TyCtxt`, no `Session`: every input is plain data the rustc half
//! (`lib.rs::codegen_crate_via_compiler_lane`, `trust_ir_frontend::select_for_codegen_module`,
//! `abi_shape::abi_shape_of`) read from rustc first, so every rule below is a unit test
//! (`codegen_module/tests.rs`). It never lowers anything to LIR and never clones the producer
//! per function: `M_cg` is assembled once.
//!
//! # THE RULES (design §3.1, as amended by plan §2)
//!
//! 1. Bodies. Each work-list item names its producer `FuncId`; all items come from ONE module.
//!    When `star` was built, every body in a HANDOFF item's call closure must be equal in `base`
//!    and `star` (a relink must not have touched it). `FuncId <-> symbol` is injective.
//! 2. Reachable closure. A body reached through a direct call that is not a work-list item is
//!    INVENTORY RESIDUE: a local, non-generic handoff body is emitted `Internal` under its own
//!    symbol and disclosed (`inventory-residue-local`); residue the instance lane spliced is
//!    refused (5.4.4 / increment 7), an upstream body `[upstream-body]` (increment 6), and a
//!    body with no identity `[codegen-module]`. Unreached bodies are pruned.
//! 3. Declarations must carry a real link symbol: `!trust_self_edge::k` binds to the calling
//!    function's own body (and must be signed as that body is, since its call sites are
//!    legalized by the body's own rule-9 plan); every other reserved name, and every name absent
//!    from `declarations` (empty until 5.6), refuses. A declaration with an entry gets P from its
//!    `AbiShape`; its FuncTy must legalize against that shape (`[callee-abi-mismatch]`
//!    otherwise), M_cg signs it with the FnAbi-legalized signature, and every call site to it
//!    is legalized as a call to a body is (5.4.3). This path is DORMANT at 5.4
//!    (INC5.4-5.6-HOOKS); at 5.6.3 a declaration admits only an allow-list of shapes.
//! 4. Producers. Only a body of the Rust producer (`Producer::TRust`) is admitted. A
//!    Clean-origin body keeps its named refusal (`CleanOriginBelowCodegenGate`, step 3); every
//!    other producer (deprecated, native trust-ir, the generated-coroutine inspection model's
//!    `Other(..)`, none) refuses by name (INC5.4-PRODUCER).
//! 5. Renaming and tables. Bodies are renamed to their symbols and `FuncId`s remapped densely.
//!    The remap rewrites EXACTLY the callee of `Call` and `CallCannotUnwind`. Every other
//!    function reference refuses (INC5.4-FNREF): indirect, invoke, drop-invoke and `SeqMap`
//!    sites; `FnDef`, `Closure` and function-naming `SymbolAddr` constants in a body or a
//!    global initializer; a non-empty drop-glue table; a function-symbol proxy global. The
//!    type and global tables are untouched (`tables_unchanged`). M_cg carries no proof
//!    obligations, certificates, obligation diagnostics, spec modules, function summaries or
//!    source provenance: the remap would make them stale, nothing on this lane reads them, and
//!    the gate reads the UNMODIFIED producer. A completeness claim is carried VERBATIM, never
//!    erased (trust-cg refuses a module that carries one, by name).
//! 6. Linkage and visibility come from rustc (residue: `Internal`).
//! 7. `target_info` must be stamped (`Unclassified`, the expected triple, 64-bit, little
//!    endian); it is never written here.
//! 8. Statics are one-to-one with rustc's collector by symbol: every collector static needs
//!    an M_cg global of that symbol, and every exported data global must be a collector
//!    static. Mutable, thread-local and pointer-bearing globals refuse.
//! 9. ABI LEGALIZATION from rustc's `FnAbi` (5.4.2's scalar subset, completed at 5.4.3; plan
//!    §3). Each producer parameter and the result legalize to PRIMITIVE M_cg slots only:
//!    * `Direct` in the audited register lane with no extension and a producer scalar of the
//!      same width: the scalar itself (5.4.2). The `bool` result's `Zext` (INC5.4-BOOLRET).
//!    * `Direct` single-field struct (a newtype): its field's scalar; `MakeAggregate` rebuilds
//!      it at entry, `ExtractField` splits it at a call site.
//!    * `Pair` of a two-field struct or tuple: two scalars, in rustc's LAYOUT order (half 0 is
//!      the field at offset 0, cross-checked against the producer's recorded offsets);
//!      `MakeAggregate` at entry, `ExtractField` at a call site. `Pair` of a shared slice
//!      reference: (data, length), `PtrFromParts` at entry, `PtrData`/`PtrMetadata` at a call.
//!      A `Pair` result is two results (split before `Return`, rebuilt after `Call`).
//!    * `Indirect{on_stack: false}` by-value struct without metadata: a pointer parameter and a
//!      `Load` at entry; the caller copies into an `Alloca` with a `Store`.
//!    * `Indirect` result: a leading `ParamAttrs.sret` pointer and an empty result list, a
//!      `Store` at each `Return`; the caller passes an `Alloca` and `Load`s it after the call.
//!    * `Ignore` argument (a zero-sized one): dropped at both ends; the body gets its value back
//!      from a constant at entry.
//!    Everything else refuses `[unsupported-abi]` for all of 5.4: `Cast`, by-value stack, any
//!    extension other than the `bool` result's, unaudited slots (`&mut T`, raw pointers, floats,
//!    `&str`), `bool` parameters, and `Pair` enums (rebuilding one needs an enum
//!    `MakeAggregate`, which trust-cg does not lower: INC5.4-PAIR-ENUM). Producer bodies are
//!    NOT touched: legalization rewrites only M_cg's copy, and the gate reads the producer.
//!    It adds no table row: the only types it writes are the producer's own and primitives,
//!    and `tables_unchanged` refuses any addition.
//! 10. P, read from rustc's `FnAbi` per PRODUCER parameter. Integers and pointers take the next
//!    X register (at most 8), 128-bit values an even pair, a `Pair` two registers
//!    (`ParamPlace::Pair`, field 0 then field 1), an `Indirect` argument one register as
//!    `Slot::Indirect`, an `Ignore` argument `ParamPlace::Ignore`; a `bool` result is
//!    `Scalar{Gpr(0), 32, Zext}`, an sret result `ReturnPlace::Indirect`. A function with an
//!    argument past the register file, or with a `Pair` result (P has no Pair result), gets NO
//!    P entry, which makes the gate grade it Unknown; so do `Slot::Indirect` and
//!    `ReturnPlace::Indirect` (Unknown until step 5.10). A float never reaches P: the audited
//!    register lane has no float, so rule 9 refuses it `[unsupported-abi]` first.
//! 11. The never-inline set is every symbol rustc marks `#[inline(never)]`.
//! 12. Body gates are copied verbatim.
//! 13. POSTCONDITION ([`check_postcondition`], separate from [`assemble`] so a test can
//!     retarget an edge or swap a pair's halves between them): trust-ir's dependency census
//!     over each M_cg body reports only instruction-site edges of `Call`/`CallCannotUnwind`,
//!     each naming `S` of the producer callee at the matching producer site; the body equals its
//!     producer body modulo those callees and EXACTLY rule 9's legalization, which the
//!     postcondition re-derives from the input's `AbiShape`s and checks instruction by
//!     instruction ([`verify_legalized_body`]: every operand, lane index, type and result),
//!     never by trusting what `assemble` built. Each M_cg declaration is signed with its
//!     legalized signature. The census's own refusals (an unresolved `Drop`'s destructor, ...)
//!     are left for trust-cg's adapter to refuse by name. Then `validate_module` and
//!     `tables_unchanged`.
//!
//! The rustc plugin compiles M_cg only when [`CodegenModuleOutput::refusals`] is empty;
//! otherwise M_cg (over the ADMITTED subset: refused items and their transitive callers are
//! dropped) only feeds trust-cg's refusal census.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::{BTreeMap, BTreeSet};

use trust_cg_bridge::call_event::{
    AbiExt, FnPlacement, ParamPlace, ProducerBody, ReturnPlace, ScalarPlace, Slot,
};
use trust_cg_bridge::codegen_backend::FunctionLinkage;
use trust_ir::function_dependencies::{
    DependencyNode, DependencySite, inspect_function_dependencies,
};
use trust_ir::node::InstrNode;
use trust_ir::ty::{FatPtrKind, FuncTy};
use trust_ir::value::{BlockId, FuncId, ValueId};
use trust_ir::{
    Block, Constant, Function, Inst, Linkage, Module, ParamAttrs, Producer, Ty, Visibility,
};

use super::FrontendRefusal;
use super::abi_shape::{AbiExtension, AbiShape, ArgShape, PairOf, ScalarKind, ScalarShape};

/// The reserved declaration name that binds to the calling body itself (design §3.1 rule 3;
/// live only after 5.6).
pub(crate) const SELF_EDGE_PREFIX: &str = "!trust_self_edge::";

/// Declaration names that never carry a real link symbol (rule 3).
pub(crate) const RESERVED_DECLARATION_PREFIXES: [&str; 4] = [
    "!trust_unresolved_callee::",
    "!trust_bodyless_instance::",
    "!trust_conflicting_declaration::",
    "!trust_definition::",
];

/// The general-purpose argument registers AAPCS64 passes integers in.
const ARGUMENT_GPRS: u8 = 8;

// ===========================================================================
// INPUT
// ===========================================================================

/// What the frontend decided for one work-list item after selecting its body.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum WorkState {
    /// Selected and its `FnAbi` read.
    Admitted {
        /// rustc's `FnAbi`, as plain data.
        abi: AbiShape,
    },
    /// Selected, then refused by the frontend (its refusal is already in the census). Its
    /// callers are dropped.
    Refused,
}

/// One item of rustc's codegen inventory whose producer body was selected.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct WorkItem {
    /// `tcx.symbol_name(instance)`.
    pub(crate) symbol: String,
    /// Its body in the producer module.
    pub(crate) func: FuncId,
    /// rustc's linkage and visibility.
    pub(crate) linkage: FunctionLinkage,
    /// `#[inline(never)]`.
    pub(crate) never_inline: bool,
    /// Selected from the HANDOFF lane (rule 1 applies when `star` was built).
    pub(crate) handoff: bool,
    /// What the frontend decided.
    pub(crate) state: WorkState,
}

/// Who a reachable body that is not a work-list item is (rule 2), read by the rustc half.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum ResidueIdentity {
    /// A local, non-generic handoff body: emitted `Internal` under `symbol`.
    Local {
        /// `tcx.symbol_name(Instance::mono(def))`.
        symbol: String,
        /// rustc's `FnAbi` for that instance.
        abi: AbiShape,
        /// `#[inline(never)]`.
        never_inline: bool,
    },
    /// A local handoff body whose `FnAbi` failed the old lane's preconditions.
    LocalAbiRefused {
        /// Its symbol.
        symbol: String,
        /// The precondition's message, verbatim.
        detail: String,
    },
    /// A body the instance lane spliced that rustc's inventory does not name (INC5.4-SCOPE).
    InstanceSpliced {
        /// Its symbol.
        symbol: String,
    },
    /// A body whose definition lives in another crate (increment 6). No caller produces this
    /// at 5.4.2 (`-Ztrust-ir-upstream-mir` is refused on this lane until 5.4.4): the rule is
    /// part of the file frozen at 5.4.4, and `upstream_residue_is_refused` pins it.
    #[allow(dead_code)] // Trust (step 2 increment 5): dormant until 5.4.4; see above.
    Upstream {
        /// Its symbol, if known.
        symbol: String,
        /// Its definition path.
        def_path: String,
        /// Its crate.
        krate: String,
    },
    /// No identity could be established.
    Unidentified {
        /// Why.
        detail: String,
    },
}

/// One reachable static of rustc's collector (rule 8).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CollectorStatic {
    /// Its link symbol.
    pub(crate) symbol: String,
    /// `static mut` (or interior mutability).
    pub(crate) mutable: bool,
    /// `External` linkage.
    pub(crate) is_external: bool,
}

/// The target the producer must have stamped (rule 7).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ExpectedTarget {
    /// The triple the producer stamps (rustc's `llvm_target`).
    pub(crate) triple: String,
    /// The pointer size in bytes.
    pub(crate) pointer_size: u32,
}

/// Everything [`build`] reads.
#[derive(Debug, Clone, Copy)]
pub(crate) struct CodegenModuleInput<'a> {
    /// The module every work-list body comes from: `star` if built, else `base`.
    pub(crate) producer: &'a Module,
    /// `base` when `producer` is `star` (rule 1); `None` when the producer IS `base`.
    pub(crate) base: Option<&'a Module>,
    /// The work list, in rustc's inventory order.
    pub(crate) items: &'a [WorkItem],
    /// The identity of every reachable non-work-list body the rustc half could read.
    pub(crate) residue: &'a BTreeMap<FuncId, ResidueIdentity>,
    /// Declarations with a real link symbol and rustc's `FnAbi` (empty until 5.6).
    pub(crate) declarations: &'a BTreeMap<String, AbiShape>,
    /// rustc's reachable statics.
    pub(crate) statics: &'a [CollectorStatic],
    /// The stamped target.
    pub(crate) target: &'a ExpectedTarget,
}

// ===========================================================================
// OUTPUT
// ===========================================================================

/// One emitted residue body (rule 2), disclosed per function.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ResidueRow {
    /// Its symbol.
    pub(crate) symbol: String,
    /// Its producer body.
    pub(crate) producer_func: FuncId,
    /// Its id in M_cg.
    pub(crate) m_cg_func: FuncId,
}

/// What [`build`] hands the compiler and the gate.
#[derive(Debug)]
pub(crate) struct CodegenModuleOutput {
    /// M_cg over the ADMITTED subset.
    pub(crate) m_cg: Module,
    /// S: every producer `FuncId` an M_cg body's producer body names, to its link symbol.
    pub(crate) symbols: BTreeMap<FuncId, String>,
    /// Each M_cg body's producer body (producer index 0: the one producer module).
    pub(crate) bodies: BTreeMap<String, ProducerBody>,
    /// P, by symbol (definitions and declarations; absent = Unknown at the gate).
    pub(crate) placements: BTreeMap<String, FnPlacement>,
    /// Symbols the module inliner must never splice.
    pub(crate) never_inline: BTreeSet<String>,
    /// The emitted residue, for the coverage artifact.
    pub(crate) residue: Vec<ResidueRow>,
    /// Every refusal. The plugin compiles only when this is empty.
    pub(crate) refusals: Vec<FrontendRefusal>,
}

/// [`assemble`]'s result: the output plus the M_cg-body -> producer-body map the
/// postcondition reads.
#[derive(Debug)]
pub(crate) struct Assembled {
    /// The output so far.
    pub(crate) output: CodegenModuleOutput,
    /// Each M_cg body's producer body.
    pub(crate) m_to_producer: BTreeMap<FuncId, FuncId>,
}

// ===========================================================================
// THE BUILD
// ===========================================================================

/// Assemble M_cg, run the postcondition and the final checks.
pub(crate) fn build(input: &CodegenModuleInput<'_>) -> CodegenModuleOutput {
    let assembled = assemble(input);
    let mut post = check_postcondition(input, &assembled);
    let mut output = assembled.output;
    output.refusals.append(&mut post);
    output.refusals.extend(final_checks(input.producer, &output.m_cg));
    output
}

fn refusal(symbol: &str, detail: impl Into<String>) -> FrontendRefusal {
    FrontendRefusal::CodegenModule { symbol: symbol.to_string(), detail: detail.into() }
}

fn unsupported_abi(symbol: &str, detail: impl Into<String>) -> FrontendRefusal {
    FrontendRefusal::UnsupportedAbi { symbol: symbol.to_string(), detail: detail.into() }
}

/// Every producer body reachable from `roots` through `Call`/`CallCannotUnwind` edges that is
/// not itself a root: the bodies the rustc half must name (rule 2). Declarations are not
/// residue (rule 3).
pub(crate) fn residue_candidates(producer: &Module, roots: &BTreeSet<FuncId>) -> BTreeSet<FuncId> {
    let mut seen: BTreeSet<FuncId> = roots.clone();
    let mut queue: Vec<FuncId> = roots.iter().copied().collect();
    let mut residue = BTreeSet::new();
    while let Some(id) = queue.pop() {
        let Some(function) = producer.function_by_id(id) else { continue };
        for callee in direct_callees(function) {
            let is_body = producer.function_by_id(callee).is_some_and(|f| !f.is_declaration());
            if is_body && seen.insert(callee) {
                residue.insert(callee);
                queue.push(callee);
            }
        }
    }
    residue
}

/// The callee of every `Call` and `CallCannotUnwind` of `function`, in body order.
fn direct_callees(function: &Function) -> Vec<FuncId> {
    let mut out = Vec::new();
    for block in &function.blocks {
        for node in &block.body {
            if let Inst::Call { callee, .. } | Inst::CallCannotUnwind { callee, .. } = &node.inst {
                out.push(*callee);
            }
        }
    }
    out
}

/// The name a producer function is known by (for messages).
fn producer_name(producer: &Module, id: FuncId) -> String {
    producer.function_by_id(id).map_or_else(
        || format!("FuncId({})", id.index()),
        |f| format!("`{}` (FuncId {})", f.display_path.as_deref().unwrap_or(&f.name), id.index()),
    )
}

/// A producer function's readable name (its display path, else its name).
fn plain_name(producer: &Module, id: FuncId) -> String {
    producer.function_by_id(id).map_or_else(
        || format!("FuncId({})", id.index()),
        |f| f.display_path.clone().unwrap_or_else(|| f.name.clone()),
    )
}

/// What one M_cg body is, during assembly.
#[derive(Debug, Clone)]
enum Member {
    /// Work-list item `index`.
    Item(usize),
    /// Local inventory residue.
    Residue { symbol: String, abi: AbiShape, never_inline: bool },
}

impl Member {
    fn symbol<'a>(&'a self, items: &'a [WorkItem]) -> &'a str {
        match self {
            Member::Item(index) => &items[*index].symbol,
            Member::Residue { symbol, .. } => symbol,
        }
    }

    fn abi<'a>(&'a self, items: &'a [WorkItem]) -> Option<&'a AbiShape> {
        match self {
            Member::Item(index) => match &items[*index].state {
                WorkState::Admitted { abi } => Some(abi),
                WorkState::Refused => None,
            },
            Member::Residue { abi, .. } => Some(abi),
        }
    }
}

/// Why one member is refused locally, by the class its refusal is reported under.
#[derive(Debug, Clone)]
enum LocalRefusal {
    /// `[codegen-module]`.
    Module(String),
    /// `[unsupported-abi]` (rule 9).
    Abi(String),
    /// `[callee-abi-mismatch]` (rule 3).
    CalleeAbi(String),
}

impl LocalRefusal {
    fn into_refusal(self, symbol: &str) -> FrontendRefusal {
        match self {
            LocalRefusal::Module(why) => refusal(symbol, why),
            LocalRefusal::Abi(why) => unsupported_abi(symbol, why),
            LocalRefusal::CalleeAbi(why) => {
                FrontendRefusal::CalleeAbiMismatch { symbol: symbol.to_string(), detail: why }
            }
        }
    }
}

/// A producer declaration an M_cg body calls (rule 3).
#[derive(Debug, Clone)]
enum DeclBinding {
    /// `!trust_self_edge::k`: the calling body itself.
    SelfEdge { caller: FuncId },
    /// A declaration with a real link symbol, its `FnAbi` and its rule-9 legalization.
    Real { name: String, abi: AbiShape, legal: Legalization },
}

/// Assemble M_cg (rules 1-12). The postcondition (rule 13) is [`check_postcondition`].
pub(crate) fn assemble(input: &CodegenModuleInput<'_>) -> Assembled {
    let p = input.producer;
    let mut refusals: Vec<FrontendRefusal> = Vec::new();

    // ---- module-wide rules (5, 7, 8) ---------------------------------------
    module_rules(input, &mut refusals);

    // ---- rule 1: the work list, injective ----------------------------------
    // Producer body -> M_cg member; bodies that are refused (with why, for callers).
    let mut members: BTreeMap<FuncId, Member> = BTreeMap::new();
    let mut refused: BTreeMap<FuncId, String> = BTreeMap::new();
    let mut symbol_owner: BTreeMap<String, FuncId> = BTreeMap::new();
    for (index, item) in input.items.iter().enumerate() {
        if let Some(previous) = symbol_owner.insert(item.symbol.clone(), item.func)
            && previous != item.func
        {
            refusals.push(refusal(
                &item.symbol,
                format!(
                    "two producer bodies ({} and {}) claim this one link symbol; the FuncId <-> \
                     symbol map must be injective (design §3.1 rule 1)",
                    producer_name(p, previous),
                    producer_name(p, item.func)
                ),
            ));
            refused.insert(item.func, item.symbol.clone());
            refused.insert(previous, item.symbol.clone());
            continue;
        }
        if let Some(existing) = members.get(&item.func) {
            let other = existing.symbol(input.items).to_string();
            refusals.push(refusal(
                &item.symbol,
                format!(
                    "the producer body {} is selected for both `{other}` and this symbol; the \
                     FuncId <-> symbol map must be injective (design §3.1 rule 1)",
                    producer_name(p, item.func)
                ),
            ));
            refused.insert(item.func, item.symbol.clone());
            continue;
        }
        match &item.state {
            WorkState::Refused => {
                refused.insert(item.func, item.symbol.clone());
            }
            WorkState::Admitted { .. } => {
                members.insert(item.func, Member::Item(index));
            }
        }
    }
    // A FuncId refused above may already have been inserted as a member by an earlier item.
    for id in refused.keys() {
        members.remove(id);
    }

    // ---- rule 2: the reachable closure -------------------------------------
    let mut queue: Vec<FuncId> = members.keys().copied().collect();
    let mut seen: BTreeSet<FuncId> = members.keys().copied().collect();
    let mut residue_refused: BTreeSet<FuncId> = BTreeSet::new();
    let mut declarations: BTreeMap<FuncId, DeclBinding> = BTreeMap::new();
    // Per-member local refusal (the member is dropped, its callers with it).
    let mut local: BTreeMap<FuncId, LocalRefusal> = BTreeMap::new();
    while let Some(id) = queue.pop() {
        let Some(function) = p.function_by_id(id) else {
            local.insert(
                id,
                LocalRefusal::Module(format!(
                    "the producer module has no body FuncId({})",
                    id.index()
                )),
            );
            continue;
        };
        for callee in direct_callees(function) {
            if callee == id || members.contains_key(&callee) || refused.contains_key(&callee) {
                continue;
            }
            let Some(target) = p.function_by_id(callee) else {
                local.insert(
                    id,
                    LocalRefusal::Module(format!(
                        "calls FuncId({}), which the producer module lacks",
                        callee.index()
                    )),
                );
                continue;
            };
            if target.is_declaration() {
                match bind_declaration(input, id, function, target) {
                    Ok(binding) => match declarations.get(&callee) {
                        Some(DeclBinding::SelfEdge { caller }) if *caller != id => {
                            // Both callers refuse: the first one bound it before the second was
                            // seen, and a self edge names exactly one body.
                            let why = format!(
                                "the self-edge declaration `{}` is called by two bodies, so it \
                                 binds to neither (design §3.1 rule 3)",
                                target.name
                            );
                            local.insert(*caller, LocalRefusal::Module(why.clone()));
                            local.insert(id, LocalRefusal::Module(why));
                        }
                        _ => {
                            declarations.insert(callee, binding);
                        }
                    },
                    Err(why) => {
                        local.insert(id, why);
                    }
                }
                continue;
            }
            if !seen.insert(callee) {
                continue;
            }
            match input.residue.get(&callee) {
                Some(ResidueIdentity::Local { symbol, abi, never_inline }) => {
                    members.insert(
                        callee,
                        Member::Residue {
                            symbol: symbol.clone(),
                            abi: abi.clone(),
                            never_inline: *never_inline,
                        },
                    );
                    queue.push(callee);
                }
                // Rule 4 before rule 2: a Clean-origin body keeps its named refusal whatever the
                // rustc half could say about its identity.
                _ if target.producer == Some(Producer::Clean) => {
                    residue_refused.insert(callee);
                    refusals.push(refusal(
                        &plain_name(p, callee),
                        "CleanOriginBelowCodegenGate: a Clean-origin body is not admitted to \
                         codegen (step 3 owns admitting it; design §3.1 rule 4)",
                    ));
                }
                other => {
                    residue_refused.insert(callee);
                    refusals.push(residue_refusal(p, callee, other));
                }
            }
        }
    }
    for id in &residue_refused {
        refused.insert(*id, plain_name(p, *id));
    }

    // ---- per-member rules (1 handoff equality, 4, 5 FNREF, 9) ---------------
    // Each admitted member's rule-9 legalization, by producer body.
    let mut legal: BTreeMap<FuncId, Legalization> = BTreeMap::new();
    for (id, member) in &members {
        if local.contains_key(id) {
            continue;
        }
        let function = p.function_by_id(*id).expect("members are producer bodies");
        match member_refusal(input, *id, function, member) {
            Ok(plan) => {
                legal.insert(*id, plan);
            }
            Err(why) => {
                local.insert(*id, why);
            }
        }
    }

    // ---- refused callees drop their callers, transitively -------------------
    let mut dropped: BTreeMap<FuncId, String> = BTreeMap::new();
    for (id, why) in local {
        if let Some(member) = members.get(&id) {
            let symbol = member.symbol(input.items).to_string();
            refusals.push(why.into_refusal(&symbol));
            dropped.insert(id, symbol);
        }
    }
    loop {
        let mut newly: Vec<(FuncId, String)> = Vec::new();
        for (id, member) in &members {
            if dropped.contains_key(id) {
                continue;
            }
            let function = p.function_by_id(*id).expect("members are producer bodies");
            let blocked = direct_callees(function).into_iter().find_map(|callee| {
                if callee == *id {
                    return None;
                }
                dropped
                    .get(&callee)
                    .or_else(|| refused.get(&callee))
                    .map(|name| (callee, name.clone()))
            });
            if let Some((_, name)) = blocked {
                let symbol = member.symbol(input.items).to_string();
                refusals.push(refusal(
                    &symbol,
                    format!(
                        "calls `{name}`, which is refused, so this caller is dropped from the \
                         codegen module with it (design §3.1: M_cg covers the admitted subset)"
                    ),
                ));
                newly.push((*id, symbol));
            }
        }
        if newly.is_empty() {
            break;
        }
        dropped.extend(newly);
    }

    // ---- build M_cg (rules 5, 6, 10, 11, 12) --------------------------------
    let survivors_items: Vec<FuncId> = input
        .items
        .iter()
        .filter(|item| members.contains_key(&item.func) && !dropped.contains_key(&item.func))
        .filter(|item| matches!(members.get(&item.func), Some(Member::Item(_))))
        .map(|item| item.func)
        .collect();
    let survivors_residue: Vec<FuncId> = members
        .iter()
        .filter(|(id, m)| matches!(m, Member::Residue { .. }) && !dropped.contains_key(id))
        .map(|(id, _)| *id)
        .collect();
    let mut m_id: BTreeMap<FuncId, FuncId> = BTreeMap::new();
    for id in survivors_items.iter().chain(survivors_residue.iter()) {
        let next = FuncId::new(m_id.len() as u32);
        m_id.insert(*id, next);
    }
    // Declarations that a surviving body calls (self edges bind to their caller).
    let mut real_decls: BTreeMap<FuncId, (String, AbiShape, Legalization)> = BTreeMap::new();
    for (decl, binding) in &declarations {
        if let DeclBinding::Real { name, abi, legal: plan } = binding {
            let called = m_id.keys().any(|body| {
                p.function_by_id(*body).is_some_and(|f| direct_callees(f).contains(decl))
            });
            if called {
                real_decls.insert(*decl, (name.clone(), abi.clone(), plan.clone()));
            }
        }
    }
    for decl in real_decls.keys() {
        let next = FuncId::new(m_id.len() as u32);
        m_id.insert(*decl, next);
    }

    let mut m_cg = empty_codegen_module(p);
    let mut symbols: BTreeMap<FuncId, String> = BTreeMap::new();
    let mut bodies: BTreeMap<String, ProducerBody> = BTreeMap::new();
    let mut placements: BTreeMap<String, FnPlacement> = BTreeMap::new();
    let mut never_inline: BTreeSet<String> = BTreeSet::new();
    let mut residue_rows: Vec<ResidueRow> = Vec::new();
    let mut m_to_producer: BTreeMap<FuncId, FuncId> = BTreeMap::new();

    // The rule-9 plan of every callee a surviving body can name, by producer id: members,
    // bound real declarations; a self edge (and a call to the body's own id) is the caller's.
    let callee_plan = |caller: FuncId, callee: FuncId| -> Option<&Legalization> {
        if callee == caller {
            return legal.get(&caller);
        }
        match declarations.get(&callee) {
            Some(DeclBinding::SelfEdge { .. }) => legal.get(&caller),
            Some(DeclBinding::Real { legal: plan, .. }) => Some(plan),
            None => legal.get(&callee),
        }
    };
    let mut build_refusals: Vec<FrontendRefusal> = Vec::new();

    for id in survivors_items.iter().chain(survivors_residue.iter()) {
        let member = &members[id];
        let source = p.function_by_id(*id).expect("members are producer bodies");
        let symbol = member.symbol(input.items).to_string();
        let new_id = m_id[id];
        let (linkage, visibility) = match member {
            Member::Item(index) => linkage_of(input.items[*index].linkage),
            Member::Residue { .. } => (Linkage::Internal, Visibility::Default),
        };
        let mut function = source.clone();
        function.id = new_id;
        if function.display_path.is_none() && function.name != symbol {
            function.display_path = Some(function.name.clone());
        }
        function.name = symbol.clone();
        function.linkage = linkage;
        function.visibility = visibility;
        function.summary = None;
        function.source_provenance = None;
        // Rule 9: the legalized signature and body (M_cg's copy only; the producer body the
        // gate reads is untouched). Survivors all carry a plan (`member_refusal` admitted them);
        // a failure here is unreachable and still refuses, never ships.
        let legalized = match legal.get(id) {
            None => Err("the member carries no rule-9 plan".to_string()),
            Some(plan) => {
                sign_legalized(&mut m_cg, &mut function, source, p, plan).and_then(|()| {
                    legalize_body(&mut function, plan, &|callee| callee_plan(*id, callee).cloned())
                })
            }
        };
        if let Err(why) = legalized {
            build_refusals.push(unsupported_abi(
                &symbol,
                format!("rule 9 could not legalize the body: {why}"),
            ));
        }
        remap_calls(&mut function, |callee| {
            if callee == *id {
                return Some(new_id);
            }
            match declarations.get(&callee) {
                Some(DeclBinding::SelfEdge { .. }) => Some(new_id),
                _ => m_id.get(&callee).copied(),
            }
        });
        m_cg.functions.push(function);
        symbols.insert(*id, symbol.clone());
        bodies.insert(symbol.clone(), ProducerBody { producer: 0, func: *id });
        m_to_producer.insert(new_id, *id);
        if let Some(abi) = member.abi(input.items)
            && let Some(plan) = legal.get(id)
            && let Some(place) = placement_of(abi, plan)
        {
            placements.insert(symbol.clone(), place);
        }
        let marked_never = match member {
            Member::Item(index) => input.items[*index].never_inline,
            Member::Residue { never_inline, .. } => *never_inline,
        };
        if marked_never {
            never_inline.insert(symbol.clone());
        }
        if let Member::Residue { .. } = member {
            residue_rows.push(ResidueRow { symbol, producer_func: *id, m_cg_func: new_id });
        }
    }
    for (decl, (name, abi, plan)) in &real_decls {
        let source = p.function_by_id(*decl).expect("bound declarations are producer functions");
        let mut function = source.clone();
        function.id = m_id[decl];
        function.name = name.clone();
        function.linkage = Linkage::External;
        function.visibility = Visibility::Default;
        function.summary = None;
        function.source_provenance = None;
        // Rule 3 / rule 9: the declaration is signed with its FnAbi-legalized signature, so
        // every (legalized) call site to it agrees with it.
        if let Err(why) = sign_legalized(&mut m_cg, &mut function, source, p, plan) {
            build_refusals.push(FrontendRefusal::CalleeAbiMismatch {
                symbol: name.clone(),
                detail: format!("rule 9 could not sign the declaration: {why}"),
            });
        }
        m_cg.functions.push(function);
        symbols.insert(*decl, name.clone());
        if let Some(place) = placement_of(abi, plan) {
            placements.insert(name.clone(), place);
        }
    }
    // A self edge's S is its caller's symbol, so the gate pairs the `bl` to the caller itself.
    for (decl, binding) in &declarations {
        if let DeclBinding::SelfEdge { caller } = binding
            && let Some(symbol) = symbols.get(caller).cloned()
        {
            symbols.insert(*decl, symbol);
        }
    }
    refusals.append(&mut build_refusals);

    Assembled {
        output: CodegenModuleOutput {
            m_cg,
            symbols,
            bodies,
            placements,
            never_inline,
            residue: residue_rows,
            refusals,
        },
        m_to_producer,
    }
}

/// rustc's `(linkage, visibility)` for a bridge `FunctionLinkage` (rule 6).
pub(crate) fn linkage_of(linkage: FunctionLinkage) -> (Linkage, Visibility) {
    match linkage {
        FunctionLinkage::External => (Linkage::External, Visibility::Default),
        FunctionLinkage::Hidden => (Linkage::External, Visibility::Hidden),
        FunctionLinkage::Internal => (Linkage::Internal, Visibility::Default),
    }
}

/// M_cg's tables: the producer's, untouched, with the proof-side tables left out (rule 5,
/// INC5.4-FNREF). The completeness claim is carried verbatim, never erased: trust-cg's adapter
/// refuses a module that carries one (`ModuleCompletenessUnsupported`), by name. Exhaustive
/// destructuring, so a table trust-ir adds later does not compile here until it is classified.
fn empty_codegen_module(p: &Module) -> Module {
    let Module {
        name,
        functions: _,
        structs,
        enums,
        records,
        closure_types,
        globals,
        func_types,
        types,
        proof_obligations: _,
        proof_certificates: _,
        target_info,
        files,
        obligation_diagnostics: _,
        spec_modules: _,
        universes,
        predicates,
        global_asm,
        imports,
        tuple_layouts,
        completeness,
        drop_glue: _,
        closure_layouts,
        // Trust: trust-ir v70's weight-blob table; `module_rules` refuses a non-empty one.
        blobs,
    } = p;
    Module {
        name: name.clone(),
        functions: Vec::new(),
        structs: structs.clone(),
        enums: enums.clone(),
        records: records.clone(),
        closure_types: closure_types.clone(),
        globals: globals.clone(),
        func_types: func_types.clone(),
        types: types.clone(),
        proof_obligations: Vec::new(),
        proof_certificates: Vec::new(),
        target_info: target_info.clone(),
        files: files.clone(),
        obligation_diagnostics: Vec::new(),
        spec_modules: Vec::new(),
        universes: universes.clone(),
        predicates: predicates.clone(),
        global_asm: global_asm.clone(),
        imports: imports.clone(),
        tuple_layouts: tuple_layouts.clone(),
        completeness: completeness.clone(),
        drop_glue: Vec::new(),
        // trust-ir v58: the layout table of `closure_types`, kept with them (as `tuple_layouts`
        // is with `types`) and as trust-cg-bridge's assembled-global copy keeps it.
        closure_layouts: closure_layouts.clone(),
        // Trust: trust-ir v70: carried verbatim, never dropped (dropping it would leave every
        // `Constant::TensorBlob` naming bytes M_cg lacks); `module_rules` refuses a non-empty
        // one by name, so it never reaches emission.
        blobs: blobs.clone(),
    }
}

/// Rewrite exactly the callee of every `Call` and `CallCannotUnwind` (rule 5). A callee the
/// map does not name is left as is; the postcondition then refuses the edge.
fn remap_calls(function: &mut Function, map: impl Fn(FuncId) -> Option<FuncId>) {
    for block in &mut function.blocks {
        for node in &mut block.body {
            if let Inst::Call { callee, .. } | Inst::CallCannotUnwind { callee, .. } =
                &mut node.inst
                && let Some(new) = map(*callee)
            {
                *callee = new;
            }
        }
    }
}

fn residue_refusal(p: &Module, id: FuncId, identity: Option<&ResidueIdentity>) -> FrontendRefusal {
    let name = producer_name(p, id);
    match identity {
        Some(ResidueIdentity::Local { .. }) => unreachable!("admitted by the caller"),
        Some(ResidueIdentity::LocalAbiRefused { symbol, detail }) => unsupported_abi(
            symbol,
            format!("inventory residue {name}: unsupported definition ABI: {detail}"),
        ),
        Some(ResidueIdentity::InstanceSpliced { symbol }) => refusal(
            symbol,
            format!(
                "inventory residue {name} is a body the instance lane spliced that rustc's \
                 inventory does not name (at -O the MIR inliner removed it); the compiler lane \
                 refuses spliced residue until step 5.4.4 / increment 7 (INC5.4-SCOPE)"
            ),
        ),
        Some(ResidueIdentity::Upstream { symbol, def_path, krate }) => {
            FrontendRefusal::UpstreamBody {
                symbol: symbol.clone(),
                def_path: def_path.clone(),
                krate: krate.clone(),
            }
        }
        Some(ResidueIdentity::Unidentified { detail }) => refusal(
            &plain_name(p, id),
            format!("inventory residue {name} has no link identity: {detail} (design §3.1 rule 2)"),
        ),
        None => refusal(
            &plain_name(p, id),
            format!(
                "inventory residue {name} was not named by the rustc half; a reachable body with \
                 no identity is refused (design §3.1 rule 2)"
            ),
        ),
    }
}

/// Rule 3: the binding of a producer DECLARATION that the body `caller` calls.
fn bind_declaration(
    input: &CodegenModuleInput<'_>,
    caller: FuncId,
    caller_fn: &Function,
    decl: &Function,
) -> Result<DeclBinding, LocalRefusal> {
    let name = decl.name.as_str();
    if name.starts_with(SELF_EDGE_PREFIX) {
        // A call through a self edge is legalized by the calling body's OWN rule-9 plan (5.4.3),
        // so the edge must be signed exactly as that body is.
        let signs = |f: &Function| {
            input
                .producer
                .func_types
                .get(f.ty.as_usize())
                .map(|t| (&t.params, &t.returns, t.is_vararg))
        };
        if signs(decl).is_none() || signs(decl) != signs(caller_fn) {
            return Err(LocalRefusal::Module(format!(
                "the self-edge declaration `{name}` is not signed as the body it binds to, so a \
                 call through it cannot be legalized by that body's FnAbi (design §3.1 rules 3 \
                 and 9)"
            )));
        }
        return Ok(DeclBinding::SelfEdge { caller });
    }
    if let Some(prefix) = RESERVED_DECLARATION_PREFIXES.iter().find(|p| name.starts_with(**p)) {
        return Err(LocalRefusal::Module(format!(
            "calls the declaration `{name}`, whose `{prefix}` name is reserved and carries no \
             real link symbol (design §3.1 rule 3; real callee declarations arrive at step 5.6)"
        )));
    }
    let Some(abi) = input.declarations.get(name) else {
        return Err(LocalRefusal::Module(format!(
            "calls the bodyless declaration `{name}`, which carries no link symbol and FnAbi this \
             lane was given (the declaration map is empty until step 5.6: foreign callees, \
             upstream callees rustc links to, and real self/cycle edges of the instance lane); \
             design §3.1 rule 3"
        )));
    };
    let ty = input.producer.func_types.get(decl.ty.as_usize()).ok_or_else(|| {
        LocalRefusal::Module(format!("the declaration `{name}` names a FuncTy the module lacks"))
    })?;
    if ty.is_vararg {
        return Err(LocalRefusal::Module(format!(
            "the declaration `{name}` is variadic; the variadic split is placed at step 5.6"
        )));
    }
    // A `Mismatch` (a genuine disagreement) and an `OutsideSubset` shape are told apart here;
    // both refuse `[callee-abi-mismatch]` until 5.6.1(b) maps the second to
    // `[unsupported-abi]` (INC5.6-CONV).
    let plan = legalize_signature(input.producer, ty, abi)
        .and_then(|plan| {
            legalizable_attributes(decl, &plan).map_err(AbiDisagreement::OutsideSubset)?;
            Ok(plan)
        })
        .map_err(|why| {
            LocalRefusal::CalleeAbi(format!(
                "the declaration `{name}` is signed {:?} -> {:?}, which is not rustc's \
                 FnAbi-legalized signature: {} (design §3.1 rule 3, design 179)",
                ty.params,
                ty.returns,
                why.message()
            ))
        })?;
    Ok(DeclBinding::Real { name: name.to_string(), abi: abi.clone(), legal: plan })
}

/// Rules 1 (handoff equality), 4 (producer), 5 (function references) and 9 (ABI) for one
/// member. `Ok` admits it, with its rule-9 legalization.
fn member_refusal(
    input: &CodegenModuleInput<'_>,
    id: FuncId,
    function: &Function,
    member: &Member,
) -> Result<Legalization, LocalRefusal> {
    let p = input.producer;
    // Rule 4.
    match &function.producer {
        Some(Producer::TRust) => {}
        Some(Producer::Clean) => {
            return Err(LocalRefusal::Module(
                "CleanOriginBelowCodegenGate: a Clean-origin body is not admitted to codegen \
                 (step 3 owns admitting it; design §3.1 rule 4)"
                    .to_string(),
            ));
        }
        other => {
            return Err(LocalRefusal::Module(format!(
                "a body of producer {other:?} is not admitted: the compiler lane licenses only \
                 the Rust producer's direct and instance lanes (D31(a); the generated-coroutine \
                 model is inspection-only and other producers have no lane here; INC5.4-PRODUCER)"
            )));
        }
    }
    // Rule 1: a handoff item's closure must be equal in `base` and `star`.
    if let (Some(base), Member::Item(index)) = (input.base, member)
        && input.items[*index].handoff
    {
        let census = inspect_function_dependencies(base, id);
        for node in census.nodes() {
            let DependencyNode::Function(f) = node else { continue };
            if base.function_by_id(*f) != p.function_by_id(*f) {
                return Err(LocalRefusal::Module(format!(
                    "the handoff body {} in this item's call closure differs between the \
                     finalize-assembled module and the instance-keyed one (a relink touched a \
                     handoff closure); design §3.1 rule 1",
                    producer_name(p, *f)
                )));
            }
        }
    }
    // Rule 5: every function reference other than a direct call.
    if let Some(why) = function_reference(p, function) {
        return Err(LocalRefusal::Module(why));
    }
    // Rule 9.
    let Some(abi) = member.abi(input.items) else {
        return Err(LocalRefusal::Module("the frontend refused this item".to_string()));
    };
    let Some(ty) = p.func_types.get(function.ty.as_usize()) else {
        return Err(LocalRefusal::Module(format!(
            "the body names FuncTy({}), which the module lacks",
            function.ty.index()
        )));
    };
    if ty.is_vararg {
        return Err(LocalRefusal::Abi(
            "a variadic definition is not represented by trust-cg".to_string(),
        ));
    }
    // A definition refuses `[unsupported-abi]` for a genuine mismatch and an outside-the-subset
    // shape alike (plan §3; 5.6.1(b) splits them for declarations only).
    let plan =
        legalize_signature(p, ty, abi).map_err(|why| LocalRefusal::Abi(why.into_message()))?;
    legalizable_attributes(function, &plan).map_err(LocalRefusal::Abi)?;
    legalizable_body(function, &plan).map_err(LocalRefusal::Abi)?;
    Ok(plan)
}

/// Rule 5 (INC5.4-FNREF): the first function reference of `function` that is not the callee
/// of a direct call, or a site this lane does not model.
fn function_reference(p: &Module, function: &Function) -> Option<String> {
    for block in &function.blocks {
        for (index, node) in block.body.iter().enumerate() {
            let at = format!("bb{}.{index}", block.id.index());
            let site = match &node.inst {
                Inst::CallIndirect { .. }
                | Inst::CallIndirectCannotUnwind { .. }
                | Inst::InvokeIndirect { .. } => {
                    Some("an indirect call (function pointers and closures land at step 5.9)")
                }
                Inst::Invoke { .. } | Inst::DropInvoke { .. } => {
                    Some("an unwinding call site (unwind edges land at step 5.11)")
                }
                Inst::SeqMap { .. } => {
                    Some("a `SeqMap` naming its element function (a function reference, step 5.9)")
                }
                // A siteless check names no function: its operands are registers. Its panic
                // site is added to M_cg after this module is built (`panic_sites`, PKG-CP), and
                // the bridge refuses any check still siteless then. A check the PRODUCER sited
                // names an entry `FuncId` the remap does not rewrite, and the unwinding form
                // names successors: both refuse.
                Inst::Assert { site: Some(_), .. } | Inst::AssertInvoke { .. } => {
                    Some("a runtime check whose failure calls a panic entry (step 5.7)")
                }
                Inst::Const { value, .. } => constant_reference(p, value),
                Inst::Switch { cases, .. } => {
                    cases.iter().find_map(|case| constant_reference(p, &case.value))
                }
                _ => None,
            };
            if let Some(what) = site {
                return Some(format!(
                    "{what} at {at}: the compiler lane remaps only the callee of `Call` and \
                     `CallCannotUnwind`, and refuses every other function reference \
                     (INC5.4-FNREF)"
                ));
            }
        }
    }
    None
}

/// A function-naming constant inside `value`, if any.
fn constant_reference(p: &Module, value: &Constant) -> Option<&'static str> {
    let mut found = None;
    value.visit_constants(|c| {
        if found.is_some() {
            return;
        }
        found = match c {
            Constant::FnDef(_) => Some("a `FnDef` constant (a function's address, step 5.9)"),
            Constant::Closure { .. } => Some("a `Closure` constant (step 5.9)"),
            Constant::SymbolAddr { symbol, .. } if !names_one_global(p, symbol) => Some(
                "a `SymbolAddr` constant that names no global (a function's address, step 5.9)",
            ),
            _ => None,
        };
    });
    found
}

fn names_one_global(p: &Module, symbol: &str) -> bool {
    p.globals.iter().filter(|g| g.name == symbol).count() == 1
        && !p.functions.iter().any(|f| f.name == symbol)
}

/// Rules 5 (module-wide references), 7 and 8.
fn module_rules(input: &CodegenModuleInput<'_>, refusals: &mut Vec<FrontendRefusal>) {
    let p = input.producer;
    let at = p.name.as_str();
    if !p.drop_glue.is_empty() {
        refusals.push(refusal(
            at,
            format!(
                "the producer module carries a drop-glue table ({} row(s)); each row is a \
                 function reference the remap would leave stale (INC5.4-FNREF; drops reach this \
                 lane with step 5.11 / increment 4)",
                p.drop_glue.len()
            ),
        ));
    }
    if !p.global_asm.is_empty() {
        refusals.push(refusal(
            at,
            "the producer module carries global assembly, which the \
                                   compiler lane does not emit",
        ));
    }
    // Trust: trust-ir v70's content-addressed tensor weights are inputs with no native
    // provider in this lane (trust-cg's module merge refuses the table too).
    if !p.blobs.is_empty() {
        refusals.push(refusal(
            at,
            format!(
                "the producer module carries a tensor weight-blob table ({} row(s), trust-ir \
                 v70), which the compiler lane does not emit",
                p.blobs.len()
            ),
        ));
    }
    // Rule 7.
    match &p.target_info {
        None => refusals.push(refusal(at, "the producer module carries no `target_info` (rule 7)")),
        Some(info) => {
            let mut wrong = Vec::new();
            if info.struct_passing != trust_ir::StructPassingPolicy::Unclassified {
                wrong.push(format!(
                    "struct passing is `{}`, not `unclassified` (the lane's ABI is rustc's FnAbi, \
                     never the producer's classification)",
                    info.struct_passing
                ));
            }
            if info.triple != input.target.triple {
                wrong.push(format!(
                    "the stamped triple is `{}`, not this compilation's `{}`",
                    info.triple, input.target.triple
                ));
            }
            if info.pointer_size != input.target.pointer_size {
                wrong.push(format!("the pointer size is {} bytes", info.pointer_size));
            }
            if info.endianness != trust_ir::Endianness::Little {
                wrong.push("the target is not little-endian".to_string());
            }
            if !wrong.is_empty() {
                refusals.push(refusal(
                    at,
                    format!(
                        "the producer's `target_info` is not this target's: {} (rule 7)",
                        wrong.join("; ")
                    ),
                ));
            }
        }
    }
    // Rule 8 and the module-wide half of rule 5.
    for global in &p.globals {
        let proxy = !global.mutable
            && global.initializer.is_none()
            && global.tls.is_none()
            && global.ty == Ty::Ptr
            && p.functions.iter().any(|f| f.name == global.name);
        if proxy {
            refusals.push(refusal(
                &global.name,
                "a function-symbol proxy global (a function's address spelled as data) is a \
                 function reference the remap does not rewrite (INC5.4-FNREF, step 5.9)",
            ));
            continue;
        }
        if global.tls.is_some() {
            refusals
                .push(refusal(&global.name, "a thread-local global is not emitted by this lane"));
            continue;
        }
        if global.mutable {
            refusals.push(refusal(
                &global.name,
                "a mutable global: the producer copies a static's value into a module-local \
                 global, which a write would not reach the real static through (rule 8)",
            ));
            continue;
        }
        match &global.initializer {
            Some(init) => {
                let mut pointer = false;
                init.visit_constants(|c| {
                    pointer |= matches!(
                        c,
                        Constant::FnDef(_) | Constant::Closure { .. } | Constant::SymbolAddr { .. }
                    );
                });
                if pointer {
                    refusals.push(refusal(
                        &global.name,
                        "a pointer-bearing global initializer (rule 8; a function address in it \
                         is INC5.4-FNREF)",
                    ));
                    continue;
                }
                let exported = matches!(global.linkage, Linkage::External)
                    && global.visibility == Visibility::Default;
                if exported && !input.statics.iter().any(|s| s.symbol == global.name) {
                    refusals.push(refusal(
                        &global.name,
                        "an exported data global that is not one of rustc's reachable statics \
                         (rule 8: statics are one-to-one with the collector)",
                    ));
                }
            }
            None => refusals.push(refusal(
                &global.name,
                "an initializer-less (imported) global names a symbol this lane cannot bind to a \
                 definition (rule 8)",
            )),
        }
    }
    for collected in input.statics {
        let found = p.globals.iter().find(|g| g.name == collected.symbol);
        let matches = found.is_some_and(|g| {
            g.initializer.is_some()
                && g.mutable == collected.mutable
                && matches!(g.linkage, Linkage::External) == collected.is_external
        });
        if !matches {
            refusals.push(refusal(
                &collected.symbol,
                "a reachable static of rustc's collector has no M_cg global of the same symbol, \
                 linkage and mutability; the producer models a static's value as a module-local \
                 copy, and adding the definition would change the global table \
                 (`tables_unchanged`). Statics are one-to-one with the collector (rule 8)",
            ));
        }
    }
}

// ===========================================================================
// RULE 9 AND RULE 10: ABI legalization from rustc's FnAbi, and P
// ===========================================================================

/// The width and kind of a producer scalar the subset admits (`None`: not such a scalar).
fn producer_scalar(ty: &Ty) -> Option<(Option<u32>, ScalarKind)> {
    let int = |bits: u32, signed: bool| Some((Some(bits), ScalarKind::Int { signed }));
    match ty {
        Ty::I8 => int(8, true),
        Ty::U8 => int(8, false),
        Ty::I16 => int(16, true),
        Ty::U16 => int(16, false),
        Ty::I32 => int(32, true),
        Ty::U32 | Ty::Char => int(32, false),
        Ty::I64 | Ty::Isize => int(64, true),
        Ty::U64 | Ty::Usize => int(64, false),
        Ty::I128 => int(128, true),
        Ty::U128 => int(128, false),
        Ty::Ptr => Some((Some(64), ScalarKind::Pointer)),
        // A fieldless enum: rustc's scalar size is P's width, and the frozen gate checks it
        // against the producer-derived carrier (an Unknown on disagreement, never Proven).
        Ty::Enum(_) => Some((None, ScalarKind::Int { signed: false })),
        _ => None,
    }
}

/// A scalar that may be a LANE of a legalized aggregate (a newtype's field, a pair's half): a
/// producer scalar of known width. A fieldless enum is not one: rebuilding an aggregate lane
/// from a register carrier of an enum is not a shape this lane carries.
fn lane_scalar(ty: &Ty) -> Option<(u32, ScalarKind)> {
    match producer_scalar(ty)? {
        (Some(width), kind) if width <= 64 => Some((width, kind)),
        _ => None,
    }
}

fn kinds_agree(producer: ScalarKind, rustc: ScalarKind) -> bool {
    match (producer, rustc) {
        // Signedness is not part of the slot: rustc's `char`/tag signedness is its own.
        (ScalarKind::Int { .. }, ScalarKind::Int { .. }) => true,
        (ScalarKind::Pointer, ScalarKind::Pointer) => true,
        _ => false,
    }
}

const LEGAL_NOTE: &str = "rule 9 legalizes a `Direct` scalar of the audited register lane, a \
    `Direct` newtype, a `Pair` of a two-field struct or tuple or of a shared slice reference, an \
    `Indirect` by-value struct, an sret result and an `Ignore` argument; `Cast`, by-value stack, \
    an extension other than the `bool` result's, unaudited slots (`&mut T`, raw pointers, \
    floats), `bool` parameters and `Pair` enums stay refused for all of 5.4";

fn scalar_agrees(ty: &Ty, bits: u32, kind: ScalarKind) -> Result<(), String> {
    let Some((width, producer_kind)) = producer_scalar(ty) else {
        return Err(format!("{ty:?} is not a producer scalar of the subset; {LEGAL_NOTE}"));
    };
    if !kinds_agree(producer_kind, kind) {
        return Err(format!(
            "the producer's {ty:?} is a {producer_kind:?}, rustc's slot a {kind:?}"
        ));
    }
    if let Some(width) = width
        && width != bits
    {
        return Err(format!("the producer's {ty:?} is {width} bits, rustc's slot {bits}"));
    }
    Ok(())
}

/// Why a producer signature does not legalize against rustc's `FnAbi` (rule 9). The two
/// classes are kept apart so a declaration can report a genuine disagreement separately from a
/// shape this lane does not carry (5.6.1(b), INC5.6-CONV). A definition refuses both
/// `[unsupported-abi]`; a declaration refuses both `[callee-abi-mismatch]` until 5.6.1(b).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum AbiDisagreement {
    /// The producer's signature contradicts rustc's `FnAbi` on a shape rule 9 carries: an
    /// arity difference, a width or kind disagreement, a producer type that rustc's pass mode
    /// cannot be the legalization of.
    Mismatch(String),
    /// A shape rule 9 does not carry, whatever the producer's type.
    OutsideSubset(String),
}

impl AbiDisagreement {
    /// The account, whichever class.
    pub(crate) fn message(&self) -> &str {
        match self {
            AbiDisagreement::Mismatch(why) | AbiDisagreement::OutsideSubset(why) => why,
        }
    }

    fn into_message(self) -> String {
        match self {
            AbiDisagreement::Mismatch(why) | AbiDisagreement::OutsideSubset(why) => why,
        }
    }

    fn context(self, what: &str) -> Self {
        match self {
            AbiDisagreement::Mismatch(why) => AbiDisagreement::Mismatch(format!("{what}: {why}")),
            AbiDisagreement::OutsideSubset(why) => {
                AbiDisagreement::OutsideSubset(format!("{what}: {why}"))
            }
        }
    }
}

fn mismatch(why: impl Into<String>) -> AbiDisagreement {
    AbiDisagreement::Mismatch(why.into())
}

fn outside(why: impl Into<String>) -> AbiDisagreement {
    AbiDisagreement::OutsideSubset(why.into())
}

/// How one PRODUCER parameter crosses the call boundary in M_cg (rule 9).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum ParamLegal {
    /// The producer's own scalar, unchanged (5.4.2's subset).
    Scalar {
        /// The producer type.
        ty: Ty,
    },
    /// A zero-sized parameter rustc does not pass: dropped at both ends. Admitted only when the
    /// body never reads it, so nothing has to rebuild its value.
    Ignored {
        /// The producer type.
        ty: Ty,
    },
    /// A single-field struct passed as its field's scalar.
    Newtype {
        /// The producer's struct type.
        agg: Ty,
        /// The field's scalar type (the M_cg parameter).
        lane: Ty,
    },
    /// A two-field struct or tuple passed as two scalars, half 0 first.
    PairFields {
        /// The producer's aggregate type.
        agg: Ty,
        /// The M_cg parameter types: the producer lane each half carries, half 0 first.
        halves: [Ty; 2],
        /// The producer lane (field index) half `k` carries.
        lanes: [u32; 2],
    },
    /// A shared slice reference passed as (data pointer, length).
    PairSlice {
        /// The producer's fat-pointer type.
        ptr_ty: Ty,
        /// Its metadata type (`usize`).
        metadata: Ty,
    },
    /// A by-value struct passed as a pointer to a caller copy.
    Indirect {
        /// The producer's struct type.
        agg: Ty,
    },
}

/// How the PRODUCER result crosses the call boundary in M_cg (rule 9).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum RetLegal {
    /// No result.
    Void,
    /// The producer's own scalar (the `bool` result's `Zext` included).
    Scalar {
        /// The producer type.
        ty: Ty,
    },
    /// A single-field struct returned as its field's scalar.
    Newtype {
        /// The producer's struct type.
        agg: Ty,
        /// The field's scalar type.
        lane: Ty,
    },
    /// A two-field struct or tuple returned as two results, half 0 first.
    PairFields {
        /// The producer's aggregate type.
        agg: Ty,
        /// The M_cg result types, half 0 first.
        halves: [Ty; 2],
        /// The producer lane half `k` carries.
        lanes: [u32; 2],
    },
    /// A shared slice reference returned as (data pointer, length).
    PairSlice {
        /// The producer's fat-pointer type.
        ptr_ty: Ty,
        /// Its metadata type.
        metadata: Ty,
    },
    /// A by-value struct returned through a leading `sret` pointer.
    Sret {
        /// The producer's struct type.
        agg: Ty,
    },
}

/// One function's rule-9 plan: how each producer parameter and the result are legalized.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Legalization {
    /// One entry per PRODUCER parameter.
    pub(crate) params: Vec<ParamLegal>,
    /// The result.
    pub(crate) ret: RetLegal,
}

impl Legalization {
    /// Every slot is the producer's own: M_cg keeps the producer's signature and body (5.4.2).
    pub(crate) fn is_identity(&self) -> bool {
        self.params.iter().all(|p| matches!(p, ParamLegal::Scalar { .. }))
            && matches!(self.ret, RetLegal::Void | RetLegal::Scalar { .. })
    }

    /// The entry block's parameters change (a non-scalar parameter, or the sret pointer).
    fn changes_entry(&self) -> bool {
        self.params.iter().any(|p| !matches!(p, ParamLegal::Scalar { .. }))
            || matches!(self.ret, RetLegal::Sret { .. })
    }

    /// The result is rewritten at every `Return`.
    fn rewrites_returns(&self) -> bool {
        !matches!(self.ret, RetLegal::Void | RetLegal::Scalar { .. })
    }

    /// M_cg's parameter types, in order (the sret pointer first).
    fn legal_params(&self) -> Vec<Ty> {
        let mut out = Vec::new();
        if matches!(self.ret, RetLegal::Sret { .. }) {
            out.push(Ty::Ptr);
        }
        for param in &self.params {
            match param {
                ParamLegal::Scalar { ty } => out.push(ty.clone()),
                ParamLegal::Ignored { .. } => {}
                ParamLegal::Newtype { lane, .. } => out.push(lane.clone()),
                ParamLegal::PairFields { halves, .. } => out.extend(halves.iter().cloned()),
                ParamLegal::PairSlice { metadata, .. } => {
                    out.push(Ty::Ptr);
                    out.push(metadata.clone());
                }
                ParamLegal::Indirect { .. } => out.push(Ty::Ptr),
            }
        }
        out
    }

    /// M_cg's result types.
    fn legal_returns(&self) -> Vec<Ty> {
        match &self.ret {
            RetLegal::Void | RetLegal::Sret { .. } => Vec::new(),
            RetLegal::Scalar { ty } => vec![ty.clone()],
            RetLegal::Newtype { lane, .. } => vec![lane.clone()],
            RetLegal::PairFields { halves, .. } => halves.to_vec(),
            RetLegal::PairSlice { metadata, .. } => vec![Ty::Ptr, metadata.clone()],
        }
    }

    /// The FnAbi-legalized signature M_cg signs the function with. An identity plan keeps the
    /// producer's signature verbatim (its recorded `abi` included); any other plan has none
    /// (`legalize_signature` refuses a producer signature that records one).
    pub(crate) fn signature(&self, producer: &FuncTy) -> FuncTy {
        if self.is_identity() {
            return producer.clone();
        }
        FuncTy {
            params: self.legal_params(),
            returns: self.legal_returns(),
            is_vararg: false,
            abi: None,
        }
    }

    /// M_cg's per-parameter attributes for a legalized signature: only the sret marker.
    fn param_attrs(&self) -> Vec<ParamAttrs> {
        match self.ret {
            RetLegal::Sret { .. } => vec![ParamAttrs { sret: true, ..ParamAttrs::default() }],
            _ => Vec::new(),
        }
    }

    /// The caller-frame slots one call to a function with this plan needs, in the order the
    /// call site takes them: the sret buffer first, then each `Indirect` argument's copy.
    fn call_slots(&self) -> Vec<Ty> {
        let mut out = Vec::new();
        if let RetLegal::Sret { agg } = &self.ret {
            out.push(agg.clone());
        }
        for param in &self.params {
            if let ParamLegal::Indirect { agg } = param {
                out.push(agg.clone());
            }
        }
        out
    }
}

/// Rule 9: `ty` against rustc's `abi`. `Ok` is the plan; the producer body is not read here
/// (see [`legalizable_body`]).
pub(crate) fn legalize_signature(
    p: &Module,
    ty: &FuncTy,
    abi: &AbiShape,
) -> Result<Legalization, AbiDisagreement> {
    if ty.params.len() != abi.params.len() {
        return Err(mismatch(format!(
            "the producer signs {} parameter(s) but rustc's FnAbi passes {}",
            ty.params.len(),
            abi.params.len()
        )));
    }
    let mut params = Vec::with_capacity(ty.params.len());
    for (index, (param, shape)) in ty.params.iter().zip(&abi.params).enumerate() {
        params.push(
            legalize_param(p, param, shape).map_err(|e| e.context(&format!("argument {index}")))?,
        );
    }
    let ret = legalize_result(p, &ty.returns, &abi.ret).map_err(|e| e.context("the result"))?;
    let plan = Legalization { params, ret };
    if !plan.is_identity() && ty.abi.is_some() {
        return Err(outside(
            "the producer signature records a typed ABI (`FuncTy.abi`), which a legalized \
             signature would have to remap; rule 9 refuses it rather than erase it",
        ));
    }
    Ok(plan)
}

/// A `Direct` slot: the producer's scalar, or a newtype's lane.
enum DirectLegal {
    Scalar,
    Newtype { lane: Ty },
}

fn direct_slot(p: &Module, ty: &Ty, shape: &ArgShape) -> Result<DirectLegal, AbiDisagreement> {
    let ArgShape::Direct { bits, kind, ext, inreg, audited, newtype } = shape else {
        return Err(outside(format!("{ty:?} is passed as {shape:?}; {LEGAL_NOTE}")));
    };
    if *ext != AbiExtension::None {
        return Err(outside(format!(
            "{ty:?} is passed with an extension ({shape:?}): extension-bearing slots wait for \
             step 5.10; {LEGAL_NOTE}"
        )));
    }
    if *inreg {
        return Err(outside(format!("{ty:?} is passed `InReg` ({shape:?}); {LEGAL_NOTE}")));
    }
    if producer_scalar(ty).is_some() {
        if !*audited {
            return Err(outside(format!(
                "{ty:?} is passed as {shape:?}, outside the audited register lane (floats, raw \
                 pointers and `&mut T` among them); {LEGAL_NOTE}"
            )));
        }
        scalar_agrees(ty, *bits, *kind).map_err(mismatch)?;
        return Ok(DirectLegal::Scalar);
    }
    if let Some((lanes, _)) = aggregate_lanes(p, ty) {
        if !*newtype {
            return Err(outside(format!(
                "{ty:?} is passed as {shape:?}, which rustc does not mark as a newtype of an \
                 integer, `char` or shared reference (outside the audited register lane); \
                 {LEGAL_NOTE}"
            )));
        }
        let [lane] = lanes.as_slice() else {
            return Err(mismatch(format!(
                "rustc passes {ty:?} as one scalar, but the producer gives it {} lane(s)",
                lanes.len()
            )));
        };
        lane_agrees(lane, *bits, *kind)?;
        return Ok(DirectLegal::Newtype { lane: lane.clone() });
    }
    Err(outside(format!(
        "{ty:?} is passed as {shape:?}, outside the audited register lane (floats, raw \
         pointers and `&mut T` among them); {LEGAL_NOTE}"
    )))
}

/// A lane of a legalized aggregate against one rustc scalar.
fn lane_agrees(lane: &Ty, bits: u32, kind: ScalarKind) -> Result<(), AbiDisagreement> {
    let Some((width, lane_kind)) = lane_scalar(lane) else {
        return Err(outside(format!(
            "the lane {lane:?} is not an integer, `char` or pointer scalar of at most 64 bits; \
             {LEGAL_NOTE}"
        )));
    };
    if !kinds_agree(lane_kind, kind) {
        return Err(mismatch(format!(
            "the producer's lane {lane:?} is a {lane_kind:?}, rustc's scalar a {kind:?}"
        )));
    }
    if width != bits {
        return Err(mismatch(format!(
            "the producer's lane {lane:?} is {width} bits, rustc's scalar {bits}"
        )));
    }
    Ok(())
}

/// The lane types (declaration order) and recorded offsets of a producer struct or tuple.
fn aggregate_lanes(p: &Module, ty: &Ty) -> Option<(Vec<Ty>, Vec<Option<u64>>)> {
    match ty {
        Ty::Struct(id) => {
            let def = p.struct_def(*id)?;
            Some((
                def.fields.iter().map(|f| f.ty.clone()).collect(),
                def.fields.iter().map(|f| f.offset).collect(),
            ))
        }
        Ty::Tuple(lanes) => Some((lanes.clone(), vec![None; lanes.len()])),
        _ => None,
    }
}

/// A `Pair` slot's legalization.
enum PairLegal {
    Fields { halves: [Ty; 2], lanes: [u32; 2] },
    Slice { metadata: Ty },
}

fn pair_slot(p: &Module, ty: &Ty, shape: &ArgShape) -> Result<PairLegal, AbiDisagreement> {
    let ArgShape::Pair { first, second, of, audited } = shape else {
        return Err(outside(format!("{ty:?} is passed as {shape:?}; {LEGAL_NOTE}")));
    };
    for half in [first, second] {
        if half.ext != AbiExtension::None || half.inreg {
            return Err(outside(format!(
                "{ty:?} is passed as a pair with an extension-bearing or `InReg` half \
                 ({shape:?}); {LEGAL_NOTE}"
            )));
        }
    }
    match of {
        PairOf::Enum => {
            return Err(outside(format!(
                "{ty:?} is an enum passed as a (tag, payload) pair: rebuilding it needs an enum \
                 `MakeAggregate`, which trust-cg does not lower (its adapter refuses \
                 `MakeAggregate` over `Ty::Enum`), and trust-ir forbids the `Undef` + \
                 `InsertField` spelling in new code (INC5.4-PAIR-ENUM); {LEGAL_NOTE}"
            )));
        }
        PairOf::Other => {
            return Err(outside(format!(
                "{ty:?} is passed as a pair that is not a two-field struct or tuple or a slice \
                 reference ({shape:?}); {LEGAL_NOTE}"
            )));
        }
        PairOf::Fields(_) | PairOf::SliceRef => {}
    }
    if !*audited {
        return Err(outside(format!(
            "{ty:?} is passed as a pair outside the audited pairs (a `&mut [T]`, a raw slice \
             pointer, or a pair of more than 16 bytes or with attributes; {shape:?}); \
             {LEGAL_NOTE}"
        )));
    }
    match (of, ty) {
        (PairOf::SliceRef, Ty::FatPtr(FatPtrKind::Slice(_))) => {
            let halves_ok = first.kind == ScalarKind::Pointer
                && first.bits == 64
                && matches!(second.kind, ScalarKind::Int { .. })
                && second.bits == 64;
            if !halves_ok {
                return Err(mismatch(format!(
                    "rustc passes the slice reference {ty:?} as ({first:?}, {second:?}), not a \
                     64-bit data pointer and a 64-bit length"
                )));
            }
            // trust-ir's own metadata type for the pointer (the target's pointer-sized unsigned
            // integer), so `PtrFromParts`/`PtrMetadata` type-check exactly as the producer's do.
            match ty.pointer_metadata_ty(64) {
                Some(metadata @ (Ty::U64 | Ty::Usize)) => Ok(PairLegal::Slice { metadata }),
                other => Err(mismatch(format!(
                    "the producer's slice reference {ty:?} carries {other:?} metadata, not a \
                     64-bit length"
                ))),
            }
        }
        (PairOf::SliceRef, _) => Err(mismatch(format!(
            "rustc passes a slice reference, but the producer's type is {ty:?}"
        ))),
        (PairOf::Fields(order), _) => {
            let Some((lanes, offsets)) = aggregate_lanes(p, ty) else {
                return Err(mismatch(format!(
                    "rustc passes a two-field struct or tuple, but the producer's type is {ty:?}"
                )));
            };
            if lanes.len() != 2 {
                return Err(mismatch(format!(
                    "rustc passes a two-field aggregate, but the producer's {ty:?} has {} lane(s)",
                    lanes.len()
                )));
            }
            if *order != [0, 1] && *order != [1, 0] {
                return Err(mismatch(format!("rustc's halves name the fields {order:?}")));
            }
            let mut halves = [Ty::Unit, Ty::Unit];
            for (k, half) in [first, second].into_iter().enumerate() {
                let lane = &lanes[order[k] as usize];
                lane_agrees(lane, half.bits, half.kind)
                    .map_err(|e| e.context(&format!("half {k} (field {})", order[k])))?;
                halves[k] = lane.clone();
            }
            // A struct's recorded offsets must put half 0's field at 0 and half 1's where
            // rustc's `ScalarPair` puts its second scalar: the layout order IS the register
            // order, and a reordered `repr(Rust)` struct passes its fields swapped.
            if let Ty::Struct(_) = ty {
                let (Some(o0), Some(o1)) = (offsets[order[0] as usize], offsets[order[1] as usize])
                else {
                    return Err(outside(format!(
                        "the producer's struct {ty:?} records no offset for a field, so rustc's \
                         half order cannot be cross-checked against it; {LEGAL_NOTE}"
                    )));
                };
                let size0 = u64::from(first.bits / 8);
                let align1 = u64::from(second.bits / 8);
                let expected =
                    if align1 == 0 { None } else { Some(size0.div_ceil(align1) * align1) };
                if o0 != 0 || Some(o1) != expected {
                    return Err(mismatch(format!(
                        "the producer records half 0's field {} at offset {o0} and half 1's field \
                         {} at offset {o1}; rustc's pair puts them at 0 and {expected:?}",
                        order[0], order[1]
                    )));
                }
            }
            Ok(PairLegal::Fields { halves, lanes: *order })
        }
        (PairOf::Enum | PairOf::Other, _) => {
            Err(outside(format!("{ty:?} is passed as {shape:?}; {LEGAL_NOTE}")))
        }
    }
}

/// An `Indirect{on_stack: false}` slot without metadata: a by-value struct with a complete
/// recorded layout (trust-cg reads and writes its memory image through that layout, and the
/// caller laid it out by rustc's).
fn indirect_slot(p: &Module, ty: &Ty, shape: &ArgShape) -> Result<(), AbiDisagreement> {
    let ArgShape::Indirect { on_stack, has_meta, audited } = shape else {
        return Err(outside(format!("{ty:?} is passed as {shape:?}; {LEGAL_NOTE}")));
    };
    if *on_stack {
        return Err(outside(format!("{ty:?} is passed by value on the stack; {LEGAL_NOTE}")));
    }
    if *has_meta {
        return Err(outside(format!(
            "{ty:?} is passed indirectly with metadata (an unsized value); {LEGAL_NOTE}"
        )));
    }
    if !*audited {
        return Err(outside(format!(
            "{ty:?} is passed indirectly but is not a by-value struct of more than 16 bytes with \
             plain attributes (a tuple, array or enum passed indirectly among them); {LEGAL_NOTE}"
        )));
    }
    let Ty::Struct(id) = ty else {
        return Err(mismatch(format!(
            "rustc passes a by-value struct indirectly, but the producer's type is {ty:?}"
        )));
    };
    let Some(def) = p.struct_def(*id) else {
        return Err(mismatch(format!("the producer's {ty:?} names a struct the module lacks")));
    };
    if def.size.is_none() || def.fields.iter().any(|f| f.offset.is_none()) {
        return Err(outside(format!(
            "the producer's struct {ty:?} records no complete layout (its size and every field \
             offset), so the memory image a pointer to it carries is not known to be rustc's; \
             {LEGAL_NOTE}"
        )));
    }
    Ok(())
}

/// An `Ignore` argument: a zero-sized producer type.
fn ignored_slot(p: &Module, ty: &Ty) -> Result<(), AbiDisagreement> {
    let zero_sized = match ty {
        Ty::Unit => true,
        Ty::Tuple(lanes) => lanes.is_empty(),
        Ty::Struct(id) => p.struct_def(*id).is_some_and(|def| def.fields.is_empty()),
        _ => false,
    };
    if zero_sized {
        Ok(())
    } else if producer_scalar(ty).is_some() || aggregate_lanes(p, ty).is_some() {
        Err(mismatch(format!(
            "rustc does not pass this argument (a zero-sized type), but the producer's {ty:?} is \
             not zero-sized"
        )))
    } else {
        Err(outside(format!(
            "rustc does not pass this argument (a zero-sized type); rule 9 drops only `()`, an \
             empty tuple and a fieldless struct, not {ty:?}; {LEGAL_NOTE}"
        )))
    }
}

fn legalize_param(p: &Module, ty: &Ty, shape: &ArgShape) -> Result<ParamLegal, AbiDisagreement> {
    if matches!(ty, Ty::Bool) {
        return Err(outside(
            "a `bool` parameter is refused for all of 5.4 (its caller-side `Zext` promise is not \
             modeled; INC5.4-BOOLRET)",
        ));
    }
    match shape {
        ArgShape::Direct { .. } => Ok(match direct_slot(p, ty, shape)? {
            DirectLegal::Scalar => ParamLegal::Scalar { ty: ty.clone() },
            DirectLegal::Newtype { lane } => ParamLegal::Newtype { agg: ty.clone(), lane },
        }),
        ArgShape::Pair { .. } => Ok(match pair_slot(p, ty, shape)? {
            PairLegal::Fields { halves, lanes } => {
                ParamLegal::PairFields { agg: ty.clone(), halves, lanes }
            }
            PairLegal::Slice { metadata } => ParamLegal::PairSlice { ptr_ty: ty.clone(), metadata },
        }),
        ArgShape::Indirect { .. } => {
            indirect_slot(p, ty, shape)?;
            Ok(ParamLegal::Indirect { agg: ty.clone() })
        }
        ArgShape::Ignore => {
            ignored_slot(p, ty)?;
            Ok(ParamLegal::Ignored { ty: ty.clone() })
        }
        ArgShape::Cast => Err(outside(format!("{ty:?} is passed as `Cast`; {LEGAL_NOTE}"))),
    }
}

fn legalize_result(
    p: &Module,
    returns: &[Ty],
    shape: &ArgShape,
) -> Result<RetLegal, AbiDisagreement> {
    match (returns, shape) {
        ([], ArgShape::Ignore) => Ok(RetLegal::Void),
        (
            [Ty::Bool],
            ArgShape::Direct {
                bits: 8,
                kind: ScalarKind::Int { .. },
                ext: AbiExtension::Zext,
                inreg: false,
                audited: true,
                ..
            },
        ) => Ok(RetLegal::Scalar { ty: Ty::Bool }),
        ([Ty::Bool], shape) => Err(outside(format!(
            "the `bool` result is passed as {shape:?}, not the zero-extended byte INC5.4-BOOLRET \
             admits"
        ))),
        ([ty], ArgShape::Direct { .. }) => Ok(match direct_slot(p, ty, shape)? {
            DirectLegal::Scalar => RetLegal::Scalar { ty: ty.clone() },
            DirectLegal::Newtype { lane } => RetLegal::Newtype { agg: ty.clone(), lane },
        }),
        ([ty], ArgShape::Pair { .. }) => Ok(match pair_slot(p, ty, shape)? {
            PairLegal::Fields { halves, lanes } => {
                RetLegal::PairFields { agg: ty.clone(), halves, lanes }
            }
            PairLegal::Slice { metadata } => RetLegal::PairSlice { ptr_ty: ty.clone(), metadata },
        }),
        ([ty], ArgShape::Indirect { .. }) => {
            indirect_slot(p, ty, shape)?;
            Ok(RetLegal::Sret { agg: ty.clone() })
        }
        ([ty], ArgShape::Cast) => {
            Err(outside(format!("the result {ty:?} is passed as `Cast`; {LEGAL_NOTE}")))
        }
        ([ty], ArgShape::Ignore) => {
            if producer_scalar(ty).is_some() {
                Err(mismatch(format!("rustc returns nothing, but the producer returns {ty:?}")))
            } else {
                Err(outside(format!(
                    "the zero-sized result {ty:?} is not legalized at 5.4.3 (rustc returns \
                     nothing); {LEGAL_NOTE}"
                )))
            }
        }
        ([], shape) => {
            Err(mismatch(format!("the producer returns nothing where rustc passes {shape:?}")))
        }
        (many, shape) => Err(mismatch(format!(
            "the producer returns {many:?} where rustc passes one value ({shape:?})"
        ))),
    }
}

/// Rule 9's attribute side: a legalized signature re-places its parameters, so a producer
/// function with per-parameter attributes (positional) is refused rather than re-mapped.
fn legalizable_attributes(function: &Function, plan: &Legalization) -> Result<(), String> {
    if plan.is_identity() || function.attrs.params.iter().all(ParamAttrs::is_empty) {
        return Ok(());
    }
    Err(format!(
        "the producer function carries per-parameter attributes ({:?}), which a legalized \
         signature would have to re-place; rule 9 refuses them rather than move or drop them",
        function.attrs.params
    ))
}

/// Rule 9's body side, checked before assembly so a refusal drops the callers too: a changed
/// entry needs an entry block no edge re-enters, a rewritten result needs one value at every
/// `Return`, and a dropped (`Ignore`) parameter must be one the body never reads.
fn legalizable_body(function: &Function, plan: &Legalization) -> Result<(), String> {
    if plan.is_identity() || function.is_declaration() {
        return Ok(());
    }
    let Some(entry) = function.blocks.iter().find(|b| b.id == function.entry) else {
        return Err("the body has no entry block".to_string());
    };
    if plan.changes_entry() {
        let reentered = function.blocks.iter().any(|b| {
            b.body
                .iter()
                .any(|n| n.inst.successor_edges().iter().any(|e| e.target == function.entry))
        });
        if reentered {
            return Err(
                "an edge re-enters the entry block, whose parameters rule 9 legalizes; the entry \
                 rebuild would run again on that edge"
                    .to_string(),
            );
        }
    }
    if plan.rewrites_returns() {
        for block in &function.blocks {
            for node in &block.body {
                if let Inst::Return { values } = &node.inst
                    && values.len() != 1
                {
                    return Err(format!(
                        "a `Return` in bb{} carries {} value(s); the legalized result needs one",
                        block.id.index(),
                        values.len()
                    ));
                }
            }
        }
    }
    for ((value, _), param) in entry.params.iter().zip(&plan.params) {
        if !matches!(param, ParamLegal::Ignored { .. }) {
            continue;
        }
        let read = function.blocks.iter().any(|b| b.body.iter().any(|n| n.inst.uses_value(*value)));
        if read {
            return Err(format!(
                "the zero-sized argument %{} is read by the body, but rustc does not pass it and \
                 rule 9 rebuilds no value for it",
                value.index()
            ));
        }
    }
    Ok(())
}

/// Sign `function` (an M_cg copy of `source`) with `plan`'s legalized signature and attributes.
/// An identity plan changes nothing.
fn sign_legalized(
    m_cg: &mut Module,
    function: &mut Function,
    source: &Function,
    p: &Module,
    plan: &Legalization,
) -> Result<(), String> {
    if plan.is_identity() {
        return Ok(());
    }
    let producer_ty = p.func_types.get(source.ty.as_usize()).ok_or_else(|| {
        format!("the function names FuncTy({}), which the module lacks", source.ty.index())
    })?;
    function.ty = m_cg
        .intern_func_type(plan.signature(producer_ty))
        .map_err(|e| format!("the legalized signature has no FuncTy id: {e:?}"))?;
    function.attrs.params = plan.param_attrs();
    Ok(())
}

// ---------------------------------------------------------------------------
// The body rewrite (M_cg's copy only)
// ---------------------------------------------------------------------------

/// The next value id no block parameter or result of `function` defines.
fn first_fresh_value(function: &Function) -> u32 {
    let mut next = 0u32;
    for block in &function.blocks {
        for (value, _) in &block.params {
            next = next.max(value.index().saturating_add(1));
        }
        for node in &block.body {
            for value in &node.results {
                next = next.max(value.index().saturating_add(1));
            }
        }
    }
    next
}

struct Fresh(u32);

impl Fresh {
    fn take(&mut self) -> Result<ValueId, String> {
        let value = ValueId::new(self.0);
        self.0 = self.0.checked_add(1).ok_or("the function's value ids are exhausted")?;
        Ok(value)
    }
}

/// A helper node of the rewrite: no proofs and no call-site proof context; its location is
/// its anchor's (the call or `Return` it serves; none for the entry rebuild).
fn helper(inst: Inst, results: Vec<ValueId>, anchor: Option<&InstrNode>) -> InstrNode {
    let mut node = InstrNode::new(inst);
    node.results = results;
    if let Some(anchor) = anchor {
        node.span = anchor.span.clone();
        node.scope = anchor.scope;
    }
    node
}

/// The aggregate operands a `MakeAggregate` over a two-lane value takes from its two halves.
fn lanes_from_halves(halves: [ValueId; 2], lanes: [u32; 2]) -> Vec<ValueId> {
    let mut fields = halves.to_vec();
    fields[lanes[0] as usize] = halves[0];
    fields[lanes[1] as usize] = halves[1];
    fields
}

/// Rule 9 over M_cg's copy of a body: rebuild the producer's parameters at entry, split the
/// result at every `Return`, and legalize every call site whose callee's plan is not the
/// identity (`callee` answers by PRODUCER callee id; it runs before the remap). A body whose
/// own plan and every callee's plan are the identity is left byte-identical (5.4.2).
fn legalize_body(
    function: &mut Function,
    own: &Legalization,
    callee: &dyn Fn(FuncId) -> Option<Legalization>,
) -> Result<(), String> {
    if function.is_declaration() {
        return Ok(());
    }
    let any_call = function.blocks.iter().any(|b| {
        b.body.iter().any(|n| match &n.inst {
            Inst::Call { callee: c, .. } | Inst::CallCannotUnwind { callee: c, .. } => {
                callee(*c).is_none_or(|plan| !plan.is_identity())
            }
            _ => false,
        })
    });
    if own.is_identity() && !any_call {
        return Ok(());
    }
    let mut fresh = Fresh(first_fresh_value(function));
    let entry_index = function
        .blocks
        .iter()
        .position(|b| b.id == function.entry)
        .ok_or("the body has no entry block")?;

    // ---- the entry: legalized parameters and the rebuild prefix -------------------------
    let mut params: Vec<(ValueId, Ty)> = Vec::new();
    let mut prefix: Vec<InstrNode> = Vec::new();
    let sret = match &own.ret {
        RetLegal::Sret { .. } => {
            let s = fresh.take()?;
            params.push((s, Ty::Ptr));
            Some(s)
        }
        _ => None,
    };
    let entry_params = function.blocks[entry_index].params.clone();
    if entry_params.len() != own.params.len() {
        return Err(format!(
            "the entry block has {} parameter(s) for {} signature parameter(s)",
            entry_params.len(),
            own.params.len()
        ));
    }
    for ((value, ty), param) in entry_params.iter().zip(&own.params) {
        match param {
            ParamLegal::Scalar { .. } => params.push((*value, ty.clone())),
            ParamLegal::Ignored { .. } => {}
            ParamLegal::Newtype { agg, lane } => {
                let s = fresh.take()?;
                params.push((s, lane.clone()));
                prefix.push(helper(
                    Inst::MakeAggregate { ty: agg.clone(), variant: None, fields: vec![s] },
                    vec![*value],
                    None,
                ));
            }
            ParamLegal::PairFields { agg, halves, lanes } => {
                let h = [fresh.take()?, fresh.take()?];
                params.push((h[0], halves[0].clone()));
                params.push((h[1], halves[1].clone()));
                prefix.push(helper(
                    Inst::MakeAggregate {
                        ty: agg.clone(),
                        variant: None,
                        fields: lanes_from_halves(h, *lanes),
                    },
                    vec![*value],
                    None,
                ));
            }
            ParamLegal::PairSlice { ptr_ty, metadata } => {
                let (d, m) = (fresh.take()?, fresh.take()?);
                params.push((d, Ty::Ptr));
                params.push((m, metadata.clone()));
                prefix.push(helper(
                    Inst::PtrFromParts {
                        ptr_ty: ptr_ty.clone(),
                        metadata_ty: metadata.clone(),
                        data: d,
                        metadata: m,
                    },
                    vec![*value],
                    None,
                ));
            }
            ParamLegal::Indirect { agg } => {
                let q = fresh.take()?;
                params.push((q, Ty::Ptr));
                prefix.push(helper(
                    Inst::Load { ty: agg.clone(), ptr: q, volatile: false, align: None },
                    vec![*value],
                    None,
                ));
            }
        }
    }

    // ---- every block: call sites and returns ------------------------------------------
    // Caller-frame slots (an sret buffer, an `Indirect` argument's copy) are hoisted into the
    // entry block, one per site, in site order, so a site in a loop reuses its slot.
    let mut slots: Vec<InstrNode> = Vec::new();
    for block in &mut function.blocks {
        let mut body: Vec<InstrNode> = Vec::with_capacity(block.body.len());
        for node in std::mem::take(&mut block.body) {
            match &node.inst {
                Inst::Call { callee: c, args } | Inst::CallCannotUnwind { callee: c, args } => {
                    let plan = callee(*c).ok_or_else(|| {
                        format!("the callee FuncId({}) has no rule-9 plan", c.index())
                    })?;
                    if plan.is_identity() {
                        body.push(node);
                        continue;
                    }
                    if args.len() != plan.params.len() || node.results.len() > 1 {
                        return Err(format!(
                            "a call in bb{} passes {} argument(s) and takes {} result(s) for a \
                             callee of {} parameter(s)",
                            block.id.index(),
                            args.len(),
                            node.results.len(),
                            plan.params.len()
                        ));
                    }
                    let mut pre: Vec<InstrNode> = Vec::new();
                    let mut legal_args: Vec<ValueId> = Vec::new();
                    let sret_slot = match &plan.ret {
                        RetLegal::Sret { agg } => {
                            let s = fresh.take()?;
                            slots.push(helper(
                                Inst::Alloca { ty: agg.clone(), count: None, align: None },
                                vec![s],
                                None,
                            ));
                            legal_args.push(s);
                            Some((s, agg.clone()))
                        }
                        _ => None,
                    };
                    for (arg, param) in args.iter().zip(&plan.params) {
                        match param {
                            ParamLegal::Scalar { .. } => legal_args.push(*arg),
                            ParamLegal::Ignored { .. } => {}
                            ParamLegal::Newtype { lane, .. } => {
                                let e = fresh.take()?;
                                pre.push(helper(
                                    Inst::ExtractField {
                                        ty: lane.clone(),
                                        aggregate: *arg,
                                        field: 0,
                                    },
                                    vec![e],
                                    Some(&node),
                                ));
                                legal_args.push(e);
                            }
                            ParamLegal::PairFields { halves, lanes, .. } => {
                                for k in 0..2 {
                                    let e = fresh.take()?;
                                    pre.push(helper(
                                        Inst::ExtractField {
                                            ty: halves[k].clone(),
                                            aggregate: *arg,
                                            field: lanes[k],
                                        },
                                        vec![e],
                                        Some(&node),
                                    ));
                                    legal_args.push(e);
                                }
                            }
                            ParamLegal::PairSlice { ptr_ty, metadata } => {
                                let (d, m) = (fresh.take()?, fresh.take()?);
                                pre.push(helper(
                                    Inst::PtrData { ptr_ty: ptr_ty.clone(), ptr: *arg },
                                    vec![d],
                                    Some(&node),
                                ));
                                pre.push(helper(
                                    Inst::PtrMetadata {
                                        ptr_ty: ptr_ty.clone(),
                                        metadata_ty: metadata.clone(),
                                        ptr: *arg,
                                    },
                                    vec![m],
                                    Some(&node),
                                ));
                                legal_args.push(d);
                                legal_args.push(m);
                            }
                            ParamLegal::Indirect { agg } => {
                                let s = fresh.take()?;
                                slots.push(helper(
                                    Inst::Alloca { ty: agg.clone(), count: None, align: None },
                                    vec![s],
                                    None,
                                ));
                                pre.push(helper(
                                    Inst::Store {
                                        ty: agg.clone(),
                                        ptr: s,
                                        value: *arg,
                                        volatile: false,
                                        align: None,
                                    },
                                    Vec::new(),
                                    Some(&node),
                                ));
                                legal_args.push(s);
                            }
                        }
                    }
                    let original = node.results.first().copied();
                    let mut post: Vec<InstrNode> = Vec::new();
                    let results: Vec<ValueId> = match &plan.ret {
                        RetLegal::Void | RetLegal::Scalar { .. } => node.results.clone(),
                        RetLegal::Newtype { agg, .. } => {
                            let n = fresh.take()?;
                            if let Some(r) = original {
                                post.push(helper(
                                    Inst::MakeAggregate {
                                        ty: agg.clone(),
                                        variant: None,
                                        fields: vec![n],
                                    },
                                    vec![r],
                                    Some(&node),
                                ));
                            }
                            vec![n]
                        }
                        RetLegal::PairFields { agg, lanes, .. } => {
                            let h = [fresh.take()?, fresh.take()?];
                            if let Some(r) = original {
                                post.push(helper(
                                    Inst::MakeAggregate {
                                        ty: agg.clone(),
                                        variant: None,
                                        fields: lanes_from_halves(h, *lanes),
                                    },
                                    vec![r],
                                    Some(&node),
                                ));
                            }
                            h.to_vec()
                        }
                        RetLegal::PairSlice { ptr_ty, metadata } => {
                            let (d, m) = (fresh.take()?, fresh.take()?);
                            if let Some(r) = original {
                                post.push(helper(
                                    Inst::PtrFromParts {
                                        ptr_ty: ptr_ty.clone(),
                                        metadata_ty: metadata.clone(),
                                        data: d,
                                        metadata: m,
                                    },
                                    vec![r],
                                    Some(&node),
                                ));
                            }
                            vec![d, m]
                        }
                        RetLegal::Sret { .. } => {
                            if let (Some(r), Some((s, agg))) = (original, &sret_slot) {
                                post.push(helper(
                                    Inst::Load {
                                        ty: agg.clone(),
                                        ptr: *s,
                                        volatile: false,
                                        align: None,
                                    },
                                    vec![r],
                                    Some(&node),
                                ));
                            }
                            Vec::new()
                        }
                    };
                    let mut call = node.clone();
                    match &mut call.inst {
                        Inst::Call { args, .. } | Inst::CallCannotUnwind { args, .. } => {
                            *args = legal_args;
                        }
                        _ => unreachable!("matched a direct call above"),
                    }
                    call.results = results;
                    body.extend(pre);
                    body.push(call);
                    body.extend(post);
                }
                Inst::Return { values } if own.rewrites_returns() => {
                    let [v] = values.as_slice() else {
                        return Err(format!(
                            "a `Return` in bb{} carries {} value(s)",
                            block.id.index(),
                            values.len()
                        ));
                    };
                    let v = *v;
                    let returned: Vec<ValueId> = match &own.ret {
                        RetLegal::Newtype { lane, .. } => {
                            let n = fresh.take()?;
                            body.push(helper(
                                Inst::ExtractField { ty: lane.clone(), aggregate: v, field: 0 },
                                vec![n],
                                Some(&node),
                            ));
                            vec![n]
                        }
                        RetLegal::PairFields { halves, lanes, .. } => {
                            let mut out = Vec::new();
                            for k in 0..2 {
                                let e = fresh.take()?;
                                body.push(helper(
                                    Inst::ExtractField {
                                        ty: halves[k].clone(),
                                        aggregate: v,
                                        field: lanes[k],
                                    },
                                    vec![e],
                                    Some(&node),
                                ));
                                out.push(e);
                            }
                            out
                        }
                        RetLegal::PairSlice { ptr_ty, metadata } => {
                            let (d, m) = (fresh.take()?, fresh.take()?);
                            body.push(helper(
                                Inst::PtrData { ptr_ty: ptr_ty.clone(), ptr: v },
                                vec![d],
                                Some(&node),
                            ));
                            body.push(helper(
                                Inst::PtrMetadata {
                                    ptr_ty: ptr_ty.clone(),
                                    metadata_ty: metadata.clone(),
                                    ptr: v,
                                },
                                vec![m],
                                Some(&node),
                            ));
                            vec![d, m]
                        }
                        RetLegal::Sret { agg } => {
                            let s = sret.ok_or("an sret result with no sret parameter")?;
                            body.push(helper(
                                Inst::Store {
                                    ty: agg.clone(),
                                    ptr: s,
                                    value: v,
                                    volatile: false,
                                    align: None,
                                },
                                Vec::new(),
                                Some(&node),
                            ));
                            Vec::new()
                        }
                        RetLegal::Void | RetLegal::Scalar { .. } => {
                            unreachable!("rewrites_returns excludes these")
                        }
                    };
                    let mut ret = node.clone();
                    ret.inst = Inst::Return { values: returned };
                    body.push(ret);
                }
                _ => body.push(node),
            }
        }
        block.body = body;
    }
    let entry = &mut function.blocks[entry_index];
    entry.params = params;
    let rest = std::mem::take(&mut entry.body);
    entry.body = prefix.into_iter().chain(slots).chain(rest).collect();
    // A dropped argument defines no value any more, so its debug name goes with it (trust-ir's
    // validator refuses a name for an undefined value).
    let dropped = dropped_arguments(&entry_params, own);
    if let Some(names) = &mut function.value_names {
        names.retain(|(value, _)| !dropped.contains(value));
    }
    Ok(())
}

/// The producer values of the entry parameters rule 9 drops (`Ignore`).
fn dropped_arguments(entry_params: &[(ValueId, Ty)], own: &Legalization) -> BTreeSet<ValueId> {
    entry_params
        .iter()
        .zip(&own.params)
        .filter(|(_, param)| matches!(param, ParamLegal::Ignored { .. }))
        .map(|((value, _), _)| *value)
        .collect()
}

/// Rule 10: P for a function whose signature passed rule 9. `None` (no entry) makes the gate
/// grade the function Unknown: an argument past the register file, or a `Pair` result. (The
/// build computes P with [`placement_of`] from the plan it already holds.)
#[cfg(test)]
pub(crate) fn placement(p: &Module, function: &Function, abi: &AbiShape) -> Option<FnPlacement> {
    let ty = p.func_types.get(function.ty.as_usize())?;
    let plan = legalize_signature(p, ty, abi).ok()?;
    placement_of(abi, &plan)
}

/// Rule 10 from rustc's `FnAbi` and the function's rule-9 plan: one entry per PRODUCER
/// parameter.
fn placement_of(abi: &AbiShape, plan: &Legalization) -> Option<FnPlacement> {
    let int_or_pointer =
        |kind: ScalarKind| matches!(kind, ScalarKind::Int { .. } | ScalarKind::Pointer);
    let mut next: u8 = 0;
    let mut params = Vec::with_capacity(abi.params.len());
    for (shape, param) in abi.params.iter().zip(&plan.params) {
        match (shape, param) {
            (_, ParamLegal::Ignored { .. }) => params.push(ParamPlace::Ignore),
            (
                ArgShape::Direct { bits, kind, ext: AbiExtension::None, .. },
                ParamLegal::Scalar { .. } | ParamLegal::Newtype { .. },
            ) => {
                if !int_or_pointer(*kind) {
                    return None;
                }
                if *bits == 128 {
                    next += next % 2;
                    if next + 2 > ARGUMENT_GPRS {
                        return None;
                    }
                    params.push(ParamPlace::Scalar(ScalarPlace {
                        slot: Slot::GprPair { lo: next, hi: next + 1 },
                        width: 128,
                        ext: AbiExt::None,
                    }));
                    next += 2;
                } else {
                    if next >= ARGUMENT_GPRS {
                        return None;
                    }
                    params.push(ParamPlace::Scalar(ScalarPlace::gpr(next, *bits)));
                    next += 1;
                }
            }
            (ArgShape::Pair { first, second, .. }, ParamLegal::PairFields { lanes, .. }) => {
                let halves: [&ScalarShape; 2] = [first, second];
                if halves.iter().any(|h| !int_or_pointer(h.kind) || h.bits > 64) {
                    return None;
                }
                if next + 2 > ARGUMENT_GPRS {
                    return None;
                }
                // P is per FIELD (field 0, then field 1); half k rides X{next+k}.
                let mut by_field = [ScalarPlace::gpr(0, 0); 2];
                for k in 0..2 {
                    by_field[lanes[k] as usize] = ScalarPlace::gpr(next + k as u8, halves[k].bits);
                }
                params.push(ParamPlace::Pair(by_field[0], by_field[1]));
                next += 2;
            }
            (ArgShape::Pair { first, second, .. }, ParamLegal::PairSlice { .. }) => {
                if next + 2 > ARGUMENT_GPRS {
                    return None;
                }
                params.push(ParamPlace::Pair(
                    ScalarPlace::gpr(next, first.bits),
                    ScalarPlace::gpr(next + 1, second.bits),
                ));
                next += 2;
            }
            (ArgShape::Indirect { .. }, ParamLegal::Indirect { .. }) => {
                if next >= ARGUMENT_GPRS {
                    return None;
                }
                params.push(ParamPlace::Scalar(ScalarPlace {
                    slot: Slot::Indirect,
                    width: 64,
                    ext: AbiExt::None,
                }));
                next += 1;
            }
            _ => return None,
        }
    }
    let ret = match (&abi.ret, &plan.ret) {
        (ArgShape::Ignore, RetLegal::Void) => ReturnPlace::Void,
        (ArgShape::Direct { ext: AbiExtension::Zext, .. }, RetLegal::Scalar { ty: Ty::Bool }) => {
            ReturnPlace::Scalar(ScalarPlace { slot: Slot::Gpr(0), width: 32, ext: AbiExt::Zext })
        }
        (
            ArgShape::Direct { bits, kind, ext: AbiExtension::None, .. },
            RetLegal::Scalar { .. } | RetLegal::Newtype { .. },
        ) => {
            if !int_or_pointer(*kind) {
                return None;
            }
            let slot = if *bits == 128 { Slot::GprPair { lo: 0, hi: 1 } } else { Slot::Gpr(0) };
            ReturnPlace::Scalar(ScalarPlace { slot, width: *bits, ext: AbiExt::None })
        }
        // The sret pointer rides X8 (AAPCS64), so it takes no argument register.
        (ArgShape::Indirect { .. }, RetLegal::Sret { .. }) => ReturnPlace::Indirect,
        // P has no Pair result: no entry, so the gate grades the function Unknown.
        _ => return None,
    };
    Some(FnPlacement { params, ret })
}

// ===========================================================================
// RULE 13: THE POSTCONDITION, AND THE FINAL CHECKS
// ===========================================================================

/// Each M_cg direct-call node's producer site: `(M_cg block, index) -> (producer block, index)`.
type SiteMap = BTreeMap<(BlockId, usize), (BlockId, usize)>;

/// A producer function's rule-9 plan, RE-DERIVED from the input (its `AbiShape`: a work item's,
/// a local residue body's, or a declaration's), never read back from what `assemble` built.
fn rederived_plan(input: &CodegenModuleInput<'_>, id: FuncId) -> Result<Legalization, String> {
    let p = input.producer;
    let function = p.function_by_id(id).ok_or("the producer module has no such function")?;
    let ty = p
        .func_types
        .get(function.ty.as_usize())
        .ok_or("the function names a FuncTy the module lacks")?;
    let abi = if function.is_declaration() {
        input.declarations.get(&function.name).ok_or("the declaration was given no FnAbi")?
    } else {
        input
            .items
            .iter()
            .find_map(|item| match &item.state {
                WorkState::Admitted { abi } if item.func == id => Some(abi),
                _ => None,
            })
            .or_else(|| match input.residue.get(&id) {
                Some(ResidueIdentity::Local { abi, .. }) => Some(abi),
                _ => None,
            })
            .ok_or("the body was given no FnAbi")?
    };
    legalize_signature(p, ty, abi).map_err(AbiDisagreement::into_message)
}

fn is_self_edge(p: &Module, id: FuncId) -> bool {
    p.function_by_id(id).is_some_and(|f| f.is_declaration() && f.name.starts_with(SELF_EDGE_PREFIX))
}

/// Rule 13 over an assembled M_cg: every function edge trust-ir's dependency census reports
/// for an M_cg body is an instruction-site edge of `Call`/`CallCannotUnwind` naming `S` of the
/// producer callee at the matching producer site, and the body equals its producer body
/// modulo those callees and exactly rule 9's legalization ([`verify_legalized_body`]). Each
/// M_cg declaration is signed with its legalized signature. The census's refusal list is left
/// for trust-cg's adapter.
pub(crate) fn check_postcondition(
    input: &CodegenModuleInput<'_>,
    assembled: &Assembled,
) -> Vec<FrontendRefusal> {
    let p = input.producer;
    let out = &assembled.output;
    let m_cg = &out.m_cg;
    let mut refusals = Vec::new();
    // S must be injective over the bodies M_cg defines.
    let mut owners: BTreeMap<&str, FuncId> = BTreeMap::new();
    for (producer_id, symbol) in &out.symbols {
        let is_body = p.function_by_id(*producer_id).is_some_and(|f| !f.is_declaration());
        if is_body
            && let Some(previous) = owners.insert(symbol.as_str(), *producer_id)
            && previous != *producer_id
        {
            refusals.push(refusal(symbol, "S maps two producer bodies to this symbol (rule 1)"));
        }
    }
    for (m_id, producer_id) in &assembled.m_to_producer {
        let Some(body) = m_cg.function_by_id(*m_id) else {
            refusals.push(refusal(
                &p.name,
                format!("M_cg lost body FuncId({}) (rule 13)", m_id.index()),
            ));
            continue;
        };
        let symbol = body.name.as_str();
        let Some(source) = p.function_by_id(*producer_id) else {
            refusals.push(refusal(symbol, "its producer body is missing (rule 13)"));
            continue;
        };
        if out.symbols.get(producer_id).map(String::as_str) != Some(symbol) {
            refusals
                .push(refusal(symbol, "the M_cg body is not named S(its producer body) (rule 13)"));
        }
        let own = match rederived_plan(input, *producer_id) {
            Ok(plan) => plan,
            Err(why) => {
                refusals.push(refusal(
                    symbol,
                    format!("its rule-9 plan cannot be re-derived from the input: {why} (rule 13)"),
                ));
                continue;
            }
        };
        let callee_plan = |callee: FuncId| -> Option<Legalization> {
            if callee == *producer_id || is_self_edge(p, callee) {
                return Some(own.clone());
            }
            rederived_plan(input, callee).ok()
        };
        let sites = match verify_legalized_body(m_cg, body, source, p, &own, &callee_plan) {
            Ok(sites) => sites,
            Err(why) => {
                refusals.push(refusal(
                    symbol,
                    format!(
                        "the M_cg body differs from its producer body beyond the callees of \
                         direct calls and rule 9's legalization: {why} (rule 5: the remap \
                         rewrites only those)"
                    ),
                ));
                continue;
            }
        };
        let census = inspect_function_dependencies(m_cg, *m_id);
        for edge in census.edges() {
            let DependencyNode::Function(target) = edge.target else { continue };
            match edge.site {
                DependencySite::Root if target == *m_id => {}
                DependencySite::Instruction { function, block, index } if function == *m_id => {
                    let problem = match sites.get(&(block, index)) {
                        Some(&(producer_block, producer_index)) => call_edge_problem(
                            p,
                            out,
                            body,
                            source,
                            target,
                            (block, index),
                            (producer_block, producer_index),
                        ),
                        None => Some(format!(
                            "the edge at bb{}.{index} is not a direct call site of the producer \
                             body",
                            block.index()
                        )),
                    };
                    if let Some(why) = problem {
                        refusals.push(refusal(symbol, format!("{why} (rule 13)")));
                    }
                }
                // Another body's edge: checked when that body is the root.
                DependencySite::Instruction { .. } => {}
                site => refusals.push(refusal(
                    symbol,
                    format!(
                        "the dependency census reports an edge to FuncId({}) from {site:?}, which \
                         is not a direct call (rule 13, INC5.4-FNREF)",
                        target.index()
                    ),
                )),
            }
        }
    }
    // Rule 3 / rule 9: every M_cg declaration is signed with its legalized signature.
    for decl in m_cg.functions.iter().filter(|f| f.is_declaration()) {
        let name = decl.name.as_str();
        let producer_id = out.symbols.iter().find_map(|(id, s)| {
            (s == name && p.function_by_id(*id).is_some_and(Function::is_declaration))
                .then_some(*id)
        });
        let Some(producer_id) = producer_id else {
            refusals
                .push(refusal(name, "the M_cg declaration names no producer declaration (rule 3)"));
            continue;
        };
        let source = p.function_by_id(producer_id).expect("found above");
        let signed = rederived_plan(input, producer_id).and_then(|plan| {
            let producer_ty = p
                .func_types
                .get(source.ty.as_usize())
                .ok_or("the declaration names a FuncTy the module lacks")?;
            let expected = plan.signature(producer_ty);
            let actual = m_cg.func_types.get(decl.ty.as_usize());
            let attrs_ok = plan.is_identity() || decl.attrs.params == plan.param_attrs();
            if actual == Some(&expected) && attrs_ok {
                Ok(())
            } else {
                Err(format!(
                    "M_cg signs it {actual:?} with parameter attributes {:?}, not the \
                     FnAbi-legalized {expected:?}",
                    decl.attrs.params
                ))
            }
        });
        if let Err(why) = signed {
            refusals.push(FrontendRefusal::CalleeAbiMismatch {
                symbol: name.to_string(),
                detail: format!("the M_cg declaration: {why} (rules 3 and 9)"),
            });
        }
    }
    refusals
}

fn call_edge_problem(
    p: &Module,
    out: &CodegenModuleOutput,
    body: &Function,
    source: &Function,
    target: FuncId,
    (block, index): (BlockId, usize),
    (producer_block, producer_index): (BlockId, usize),
) -> Option<String> {
    fn at(f: &Function, block: BlockId, index: usize) -> Option<&Inst> {
        f.blocks.iter().find(|b| b.id == block).and_then(|b| b.body.get(index)).map(|n| &n.inst)
    }
    let site = format!("bb{}.{index}", block.index());
    let m_callee = match at(body, block, index) {
        Some(Inst::Call { callee, .. } | Inst::CallCannotUnwind { callee, .. }) => *callee,
        other => {
            return Some(format!(
                "the edge at {site} is not a direct call ({:?})",
                other.map(std::mem::discriminant)
            ));
        }
    };
    if m_callee != target {
        return Some(format!("the census edge at {site} does not name the call's callee"));
    }
    let producer_callee = match at(source, producer_block, producer_index) {
        Some(Inst::Call { callee, .. } | Inst::CallCannotUnwind { callee, .. }) => *callee,
        _ => return Some(format!("the producer body has no direct call at {site}")),
    };
    let Some(expected) = out.symbols.get(&producer_callee) else {
        return Some(format!(
            "S does not name the producer callee {} at {site}",
            producer_name(p, producer_callee)
        ));
    };
    let named = out.m_cg.function_by_id(target).map(|f| f.name.as_str());
    if named != Some(expected.as_str()) {
        return Some(format!(
            "the call at {site} names `{}`, but the resolved instance there is `{expected}`",
            named.unwrap_or("<missing>")
        ));
    }
    None
}

/// The values a check of one M_cg body has seen defined fresh (none the producer body defines,
/// each defined once).
struct FreshCheck {
    producer: BTreeSet<ValueId>,
    seen: BTreeSet<ValueId>,
}

impl FreshCheck {
    fn new(source: &Function) -> Self {
        let mut producer = BTreeSet::new();
        for block in &source.blocks {
            producer.extend(block.params.iter().map(|(v, _)| *v));
            for node in &block.body {
                producer.extend(node.results.iter().copied());
            }
        }
        FreshCheck { producer, seen: BTreeSet::new() }
    }

    fn take(&mut self, value: ValueId) -> Result<ValueId, String> {
        if self.producer.contains(&value) || !self.seen.insert(value) {
            return Err(format!("%{} is not a fresh value of the legalization", value.index()));
        }
        Ok(value)
    }
}

/// One node of M_cg's block at a cursor, advancing it.
fn next_node<'a>(block: &'a Block, cursor: &mut usize) -> Result<&'a InstrNode, String> {
    let node = block.body.get(*cursor).ok_or_else(|| {
        format!("M_cg's bb{} ends before rule 9's legalization of it does", block.id.index())
    })?;
    *cursor += 1;
    Ok(node)
}

/// A rule-9 helper node: exactly `inst` defining exactly `results`, with no proofs and no
/// call-site proof context, located at its anchor (none for the entry rebuild).
fn expect_helper(
    node: &InstrNode,
    inst: &Inst,
    results: &[ValueId],
    anchor: Option<&InstrNode>,
) -> Result<(), String> {
    let located = match anchor {
        Some(anchor) => node.span == anchor.span && node.scope == anchor.scope,
        None => node.span.is_none() && node.scope.is_none(),
    };
    if node.inst != *inst
        || node.results != results
        || !node.proofs.is_empty()
        || node.proof_context.is_some()
        || !located
    {
        return Err(format!(
            "rule 9 expects {inst:?} defining {results:?}, but M_cg has {:?} defining {:?}",
            node.inst, node.results
        ));
    }
    Ok(())
}

/// A helper node defining ONE fresh value with `make(value)`'s instruction.
fn expect_fresh_helper(
    block: &Block,
    cursor: &mut usize,
    fresh: &mut FreshCheck,
    anchor: Option<&InstrNode>,
    make: impl FnOnce() -> Inst,
) -> Result<ValueId, String> {
    let node = next_node(block, cursor)?;
    let [value] = node.results.as_slice() else {
        return Err(format!("rule 9 expects one fresh result, M_cg has {:?}", node.results));
    };
    expect_helper(node, &make(), &[*value], anchor)?;
    fresh.take(*value)
}

/// Two nodes equal once a direct call's callee is set aside.
fn same_modulo_callee(a: &InstrNode, b: &InstrNode) -> bool {
    let normalized = |n: &InstrNode| {
        let mut n = n.clone();
        if let Inst::Call { callee, .. } | Inst::CallCannotUnwind { callee, .. } = &mut n.inst {
            *callee = FuncId::new(0);
        }
        n
    };
    normalized(a) == normalized(b)
}

/// THE RULE-9 CHECK: M_cg's `body` is exactly the producer's `source` under `own` (its plan,
/// re-derived) with every call site legalized by its callee's plan (`callee`, by PRODUCER
/// callee id, re-derived), callees set aside. Every legalized parameter, lane index, operand,
/// type and result is compared: a pair's halves swapped, an sret store or load dropped, a slot
/// shared, an extra instruction, all refuse. `Ok` maps each M_cg direct call to its producer
/// site, for the edge check.
fn verify_legalized_body(
    m_cg: &Module,
    body: &Function,
    source: &Function,
    p: &Module,
    own: &Legalization,
    callee: &dyn Fn(FuncId) -> Option<Legalization>,
) -> Result<SiteMap, String> {
    if body.entry != source.entry {
        return Err("the entry block moved".to_string());
    }
    if body.body_gate != source.body_gate {
        return Err("the body gate changed".to_string());
    }
    let producer_ty = p
        .func_types
        .get(source.ty.as_usize())
        .ok_or("the producer body names a FuncTy the module lacks")?;
    if own.is_identity() {
        if body.ty != source.ty {
            return Err("the signature changed under an identity plan".to_string());
        }
        if body.attrs != source.attrs {
            return Err("the attributes changed under an identity plan".to_string());
        }
    } else {
        let expected = own.signature(producer_ty);
        let actual = m_cg.func_types.get(body.ty.as_usize());
        if actual != Some(&expected) {
            return Err(format!("M_cg signs it {actual:?}, not the FnAbi-legalized {expected:?}"));
        }
        let mut attrs = source.attrs.clone();
        attrs.params = own.param_attrs();
        if body.attrs != attrs {
            return Err(format!(
                "M_cg's attributes are {:?}, not the legalized {attrs:?}",
                body.attrs
            ));
        }
    }
    if body.blocks.len() != source.blocks.len()
        || body.blocks.iter().zip(&source.blocks).any(|(a, b)| a.id != b.id)
    {
        return Err("the block structure changed".to_string());
    }
    // Debug names: the producer's, less those of the arguments rule 9 drops.
    let source_entry = source
        .blocks
        .iter()
        .find(|b| b.id == source.entry)
        .ok_or("the producer body has no entry block")?;
    let dropped = dropped_arguments(&source_entry.params, own);
    let names = source.value_names.as_ref().map(|names| {
        names.iter().filter(|(value, _)| !dropped.contains(value)).cloned().collect::<Vec<_>>()
    });
    if body.value_names != names {
        return Err("the value names changed beyond the dropped arguments'".to_string());
    }
    let plan_at = |c: FuncId| {
        callee(c).ok_or_else(|| format!("the callee FuncId({}) has no rule-9 plan", c.index()))
    };
    // The caller-frame slots the legalized call sites take, in site order.
    let mut slot_tys: Vec<Ty> = Vec::new();
    for block in &source.blocks {
        for node in &block.body {
            if let Inst::Call { callee: c, .. } | Inst::CallCannotUnwind { callee: c, .. } =
                &node.inst
            {
                let plan = plan_at(*c)?;
                if !plan.is_identity() {
                    slot_tys.extend(plan.call_slots());
                }
            }
        }
    }
    let mut fresh = FreshCheck::new(source);
    let mut slots: Vec<ValueId> = Vec::new();
    let mut slot_cursor = 0usize;
    let mut sret_param: Option<ValueId> = None;
    let mut sites = SiteMap::new();
    for (lb, sb) in body.blocks.iter().zip(&source.blocks) {
        let mut li = 0usize;
        if sb.id != source.entry && lb.params != sb.params {
            return Err(format!("the parameters of bb{} changed", lb.id.index()));
        }
        if sb.id == source.entry {
            // The legalized parameters, then the rebuild of each producer parameter.
            let mut lparams = lb.params.iter();
            let mut next_param = |ty: &Ty| -> Result<ValueId, String> {
                let (value, actual) =
                    lparams.next().ok_or("the entry block has too few legalized parameters")?;
                if actual != ty {
                    return Err(format!(
                        "an entry parameter is {actual:?}, the legalization needs {ty:?}"
                    ));
                }
                Ok(*value)
            };
            if let RetLegal::Sret { .. } = &own.ret {
                sret_param = Some(fresh.take(next_param(&Ty::Ptr)?)?);
            }
            if sb.params.len() != own.params.len() {
                return Err("the producer's entry block disagrees with its signature".to_string());
            }
            let mut rebuilds: Vec<(ValueId, Inst)> = Vec::new();
            for ((value, ty), param) in sb.params.iter().zip(&own.params) {
                match param {
                    ParamLegal::Scalar { .. } => {
                        if next_param(ty)? != *value {
                            return Err(format!("the scalar parameter %{} changed", value.index()));
                        }
                    }
                    ParamLegal::Ignored { .. } => {}
                    ParamLegal::Newtype { agg, lane } => {
                        let s = fresh.take(next_param(lane)?)?;
                        rebuilds.push((
                            *value,
                            Inst::MakeAggregate { ty: agg.clone(), variant: None, fields: vec![s] },
                        ));
                    }
                    ParamLegal::PairFields { agg, halves, lanes } => {
                        let h0 = fresh.take(next_param(&halves[0])?)?;
                        let h1 = fresh.take(next_param(&halves[1])?)?;
                        rebuilds.push((
                            *value,
                            Inst::MakeAggregate {
                                ty: agg.clone(),
                                variant: None,
                                fields: lanes_from_halves([h0, h1], *lanes),
                            },
                        ));
                    }
                    ParamLegal::PairSlice { ptr_ty, metadata } => {
                        let d = fresh.take(next_param(&Ty::Ptr)?)?;
                        let m = fresh.take(next_param(metadata)?)?;
                        rebuilds.push((
                            *value,
                            Inst::PtrFromParts {
                                ptr_ty: ptr_ty.clone(),
                                metadata_ty: metadata.clone(),
                                data: d,
                                metadata: m,
                            },
                        ));
                    }
                    ParamLegal::Indirect { agg } => {
                        let q = fresh.take(next_param(&Ty::Ptr)?)?;
                        rebuilds.push((
                            *value,
                            Inst::Load { ty: agg.clone(), ptr: q, volatile: false, align: None },
                        ));
                    }
                }
            }
            if lparams.next().is_some() {
                return Err("the entry block has more parameters than the legalization".to_string());
            }
            for (value, inst) in rebuilds {
                expect_helper(next_node(lb, &mut li)?, &inst, &[value], None)?;
            }
            for ty in &slot_tys {
                let ty = ty.clone();
                let s = expect_fresh_helper(lb, &mut li, &mut fresh, None, || Inst::Alloca {
                    ty,
                    count: None,
                    align: None,
                })?;
                slots.push(s);
            }
        }
        for (si, snode) in sb.body.iter().enumerate() {
            match &snode.inst {
                Inst::Call { callee: c, args } | Inst::CallCannotUnwind { callee: c, args } => {
                    let plan = plan_at(*c)?;
                    if plan.is_identity() {
                        let at = li;
                        let lnode = next_node(lb, &mut li)?;
                        if !same_modulo_callee(lnode, snode) {
                            return Err(format!(
                                "M_cg's bb{}.{at} is not the producer's bb{}.{si} modulo its callee",
                                lb.id.index(),
                                sb.id.index()
                            ));
                        }
                        sites.insert((lb.id, at), (sb.id, si));
                        continue;
                    }
                    if args.len() != plan.params.len() || snode.results.len() > 1 {
                        return Err(format!(
                            "the producer's call at bb{}.{si} does not fit its callee's plan",
                            sb.id.index()
                        ));
                    }
                    let mut take_slot = || -> Result<ValueId, String> {
                        let s = *slots.get(slot_cursor).ok_or("a call site lacks its slot")?;
                        slot_cursor += 1;
                        Ok(s)
                    };
                    let mut legal_args: Vec<ValueId> = Vec::new();
                    let sret_slot = match &plan.ret {
                        RetLegal::Sret { .. } => {
                            let s = take_slot()?;
                            legal_args.push(s);
                            Some(s)
                        }
                        _ => None,
                    };
                    for (arg, param) in args.iter().zip(&plan.params) {
                        let anchor = Some(snode);
                        match param {
                            ParamLegal::Scalar { .. } => legal_args.push(*arg),
                            ParamLegal::Ignored { .. } => {}
                            ParamLegal::Newtype { lane, .. } => {
                                let e =
                                    expect_fresh_helper(lb, &mut li, &mut fresh, anchor, || {
                                        Inst::ExtractField {
                                            ty: lane.clone(),
                                            aggregate: *arg,
                                            field: 0,
                                        }
                                    })?;
                                legal_args.push(e);
                            }
                            ParamLegal::PairFields { halves, lanes, .. } => {
                                for k in 0..2 {
                                    let e = expect_fresh_helper(
                                        lb,
                                        &mut li,
                                        &mut fresh,
                                        anchor,
                                        || Inst::ExtractField {
                                            ty: halves[k].clone(),
                                            aggregate: *arg,
                                            field: lanes[k],
                                        },
                                    )?;
                                    legal_args.push(e);
                                }
                            }
                            ParamLegal::PairSlice { ptr_ty, metadata } => {
                                let d =
                                    expect_fresh_helper(lb, &mut li, &mut fresh, anchor, || {
                                        Inst::PtrData { ptr_ty: ptr_ty.clone(), ptr: *arg }
                                    })?;
                                let m =
                                    expect_fresh_helper(lb, &mut li, &mut fresh, anchor, || {
                                        Inst::PtrMetadata {
                                            ptr_ty: ptr_ty.clone(),
                                            metadata_ty: metadata.clone(),
                                            ptr: *arg,
                                        }
                                    })?;
                                legal_args.push(d);
                                legal_args.push(m);
                            }
                            ParamLegal::Indirect { agg } => {
                                let s = take_slot()?;
                                expect_helper(
                                    next_node(lb, &mut li)?,
                                    &Inst::Store {
                                        ty: agg.clone(),
                                        ptr: s,
                                        value: *arg,
                                        volatile: false,
                                        align: None,
                                    },
                                    &[],
                                    anchor,
                                )?;
                                legal_args.push(s);
                            }
                        }
                    }
                    // The call itself: the producer's node with the legalized arguments and
                    // results, its callee set aside.
                    let at = li;
                    let lnode = next_node(lb, &mut li)?;
                    let results: Vec<ValueId> = match &plan.ret {
                        RetLegal::Void | RetLegal::Scalar { .. } => snode.results.clone(),
                        RetLegal::Sret { .. } => Vec::new(),
                        RetLegal::Newtype { .. } => {
                            let [n] = lnode.results.as_slice() else {
                                return Err("a newtype result is one M_cg result".to_string());
                            };
                            vec![fresh.take(*n)?]
                        }
                        RetLegal::PairFields { .. } | RetLegal::PairSlice { .. } => {
                            let [a, b] = lnode.results.as_slice() else {
                                return Err("a pair result is two M_cg results".to_string());
                            };
                            vec![fresh.take(*a)?, fresh.take(*b)?]
                        }
                    };
                    let mut expected = snode.clone();
                    if let Inst::Call { args, .. } | Inst::CallCannotUnwind { args, .. } =
                        &mut expected.inst
                    {
                        *args = legal_args;
                    }
                    expected.results = results.clone();
                    if !same_modulo_callee(lnode, &expected) {
                        return Err(format!(
                            "M_cg's call at bb{}.{at} is not the producer's bb{}.{si} with \
                             rule 9's arguments {:?} and results {results:?}",
                            lb.id.index(),
                            sb.id.index(),
                            match &expected.inst {
                                Inst::Call { args, .. } | Inst::CallCannotUnwind { args, .. } =>
                                    args.clone(),
                                _ => Vec::new(),
                            }
                        ));
                    }
                    sites.insert((lb.id, at), (sb.id, si));
                    if let Some(r) = snode.results.first() {
                        let rebuild = match &plan.ret {
                            RetLegal::Void | RetLegal::Scalar { .. } => None,
                            RetLegal::Newtype { agg, .. } => Some(Inst::MakeAggregate {
                                ty: agg.clone(),
                                variant: None,
                                fields: results.clone(),
                            }),
                            RetLegal::PairFields { agg, lanes, .. } => Some(Inst::MakeAggregate {
                                ty: agg.clone(),
                                variant: None,
                                fields: lanes_from_halves([results[0], results[1]], *lanes),
                            }),
                            RetLegal::PairSlice { ptr_ty, metadata } => Some(Inst::PtrFromParts {
                                ptr_ty: ptr_ty.clone(),
                                metadata_ty: metadata.clone(),
                                data: results[0],
                                metadata: results[1],
                            }),
                            RetLegal::Sret { agg } => Some(Inst::Load {
                                ty: agg.clone(),
                                ptr: sret_slot.ok_or("an sret call without its slot")?,
                                volatile: false,
                                align: None,
                            }),
                        };
                        if let Some(inst) = rebuild {
                            expect_helper(next_node(lb, &mut li)?, &inst, &[*r], Some(snode))?;
                        }
                    }
                }
                Inst::Return { values } if own.rewrites_returns() => {
                    let [v] = values.as_slice() else {
                        return Err(format!(
                            "the producer's `Return` at bb{}.{si} carries {} value(s)",
                            sb.id.index(),
                            values.len()
                        ));
                    };
                    let v = *v;
                    let anchor = Some(snode);
                    let returned: Vec<ValueId> = match &own.ret {
                        RetLegal::Newtype { lane, .. } => {
                            vec![expect_fresh_helper(lb, &mut li, &mut fresh, anchor, || {
                                Inst::ExtractField { ty: lane.clone(), aggregate: v, field: 0 }
                            })?]
                        }
                        RetLegal::PairFields { halves, lanes, .. } => {
                            let mut out = Vec::new();
                            for k in 0..2 {
                                out.push(expect_fresh_helper(
                                    lb,
                                    &mut li,
                                    &mut fresh,
                                    anchor,
                                    || Inst::ExtractField {
                                        ty: halves[k].clone(),
                                        aggregate: v,
                                        field: lanes[k],
                                    },
                                )?);
                            }
                            out
                        }
                        RetLegal::PairSlice { ptr_ty, metadata } => {
                            let d = expect_fresh_helper(lb, &mut li, &mut fresh, anchor, || {
                                Inst::PtrData { ptr_ty: ptr_ty.clone(), ptr: v }
                            })?;
                            let m = expect_fresh_helper(lb, &mut li, &mut fresh, anchor, || {
                                Inst::PtrMetadata {
                                    ptr_ty: ptr_ty.clone(),
                                    metadata_ty: metadata.clone(),
                                    ptr: v,
                                }
                            })?;
                            vec![d, m]
                        }
                        RetLegal::Sret { agg } => {
                            expect_helper(
                                next_node(lb, &mut li)?,
                                &Inst::Store {
                                    ty: agg.clone(),
                                    ptr: sret_param
                                        .ok_or("an sret result without its parameter")?,
                                    value: v,
                                    volatile: false,
                                    align: None,
                                },
                                &[],
                                anchor,
                            )?;
                            Vec::new()
                        }
                        RetLegal::Void | RetLegal::Scalar { .. } => {
                            unreachable!("rewrites_returns excludes these")
                        }
                    };
                    let mut expected = snode.clone();
                    expected.inst = Inst::Return { values: returned };
                    let at = li;
                    if *next_node(lb, &mut li)? != expected {
                        return Err(format!(
                            "M_cg's bb{}.{at} is not the producer's `Return` at bb{}.{si} with \
                             rule 9's result",
                            lb.id.index(),
                            sb.id.index()
                        ));
                    }
                }
                _ => {
                    let at = li;
                    if next_node(lb, &mut li)? != snode {
                        return Err(format!(
                            "M_cg's bb{}.{at} is not the producer's bb{}.{si}",
                            lb.id.index(),
                            sb.id.index()
                        ));
                    }
                }
            }
        }
        if li != lb.body.len() {
            return Err(format!(
                "M_cg's bb{} carries {} instruction(s) rule 9 does not account for",
                lb.id.index(),
                lb.body.len() - li
            ));
        }
    }
    if slot_cursor != slots.len() {
        return Err("a hoisted caller-frame slot is used by no call site".to_string());
    }
    Ok(sites)
}

/// `validate_module` and the table tripwire.
fn final_checks(producer: &Module, m_cg: &Module) -> Vec<FrontendRefusal> {
    let mut refusals = Vec::new();
    let errors = trust_ir_build::validate_module(m_cg);
    if let Some(first) = errors.first() {
        refusals.push(refusal(
            &m_cg.name,
            format!(
                "the codegen module fails `validate_module` ({} error(s)); first: {first}",
                errors.len()
            ),
        ));
    }
    if let Err(why) = super::instance_assembly::tables_unchanged(producer, m_cg) {
        refusals.push(refusal(&m_cg.name, format!("{why} (rule 5)")));
    }
    refusals
}

#[cfg(test)]
mod tests;
