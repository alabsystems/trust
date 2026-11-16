//! Trust (step 2 increment 3 of `docs/plans/2026-09-29-trust-ir-sole-compile-path.md`): the
//! INSTANCE-KEYED codegen module — code generation from trust-ir for a crate that calls a
//! GENERIC function, on the opt-in `-Ztrust-cg-frontend=trust-ir` lane.
//!
//! # What this file decides
//!
//! It computes a SPLICE DECISION: which instance bodies enter the module the trust-ir frontend
//! lowers code from. Under the manifest's own rule (`scripts/frozen-files.txt`, "FROZEN a file
//! that COMPUTES a splice, verdict or flip decision") it is therefore FROZEN, BYTE-IDENTICAL, by
//! owner ruling D17 (2026-09-29, "Yes, and freeze it"; `docs/DECISION_QUEUE.md`, section D17).
//!
//! # What the freeze covers
//!
//! 1. THIS file, which decides the assembly (below);
//! 2. `crates/trust-thir-lower/src/instance_admission.rs`, frozen with it under the manifest's
//!    DELEGATE rule: this file delegates the producer-side admission to it and does not re-derive
//!    it. That file holds the WHOLE THIR route of the instance-keyed producer
//!    (`admit_instance_body`: entry refusals, the lowering on a fail-closed lane, the post-lowering
//!    gate in full, the symbol and calling-convention stamps, the callee declarations — each
//!    `Item` edge RE-DERIVED from its call site — the self-contained check, standalone validation
//!    and fn-pointer freedom), the leaf-callee drop check (`instance_drop_refusal`), the finalize
//!    validator this file runs on its result (`assembled_codegen_validation_errors`), and the
//!    identity of an analysis-time declaration (`declaration_names_instance`). The delegation is
//!    by TYPE: an `InstanceBody` exists only through that route, is READ-ONLY after it (no public
//!    field, shared-reference accessors only), and carries an `Admitted` token.
//!    [`Assembler::lower_and_map`] refuses a body whose token names another instance, and, on
//!    both the append and the relink path, one whose body or declarations are not named by the
//!    link-time symbol of the instance they stand for ([`function_is_named`]).
//!
//! 3. `instance_assembly/closure_source.rs`, the delegated pure authentication
//!    of an existing capturing FnOnce source body. Its closure table, observed
//!    frame, environment-first signature and direct-source license stay intact.
//!
//! NOT covered — the unfrozen inputs, listed as residuals in `scripts/frozen-files.txt` with the
//! test that exercises each and the lane that runs it: the lowering itself (the producer under
//! test, including the `Lowered` flags, tripwire values and call sites it reports); the trust-cg
//! frontend's ROUTING (`trust_ir_frontend::lower_instance` must take every non-upstream item's IR
//! from [`Plan::source`], and nothing else on the codegen path may call the instance-keyed
//! producer); trust-ir's `function_dependencies` census, which the edge, fn-pointer and
//! postcondition checks read (gitlink-pinned); the handoff's own leaf selection
//! (`AssembledCrateModuleForCodegen::exact_instance_body`), which a monomorphic LEAF callee is
//! linked through; and `trust_thir_lower::encode_site_args`, which the declaration-identity check
//! uses to recompute a concrete key. The output-gate policy is NOT an input: [`plan`] reads it
//! from the session itself ([`strict_gate_from`], which the emission path calls too).
//!
//! INHERITED from the handoff lane (docs/KNOWN_HAZARDS.md, OPEN 2026-10-01, abstraction lanes):
//! a monomorphic LEAF callee is linked as its analysis-time handoff body, never re-lowered. Its
//! drops and any `undef` in it are checked here, but an OPAQUE COLLAPSE that leaves no `undef` (a
//! field store that stores nothing, or only an `Option` discriminant) is invisible: the handoff
//! does not carry `Lowered::opaque_collapse` (the frozen `crate_module.rs` discards it). Such a
//! leaf carries the handoff lane's hazard into this lane. Every body this lane LOWERS — an
//! appended generic instance and a relinked monomorphic guest — passes the frozen admission's
//! opaque-collapse and `undef` gates.
//!
//! What THIS file decides:
//!
//! * the LANE of every reachable item ([`plan`]): a concrete GENERIC local item, or a monomorphic
//!   one whose finalize-assembled body reaches a bodyless declaration (and no Clean-origin body),
//!   takes the INSTANCE lane; every other monomorphic item keeps the HANDOFF lane and lowers from
//!   the unmodified finalize-assembled module exactly as before;
//! * which callee body each instance edge links to (`Assembler::slot_for`);
//! * the splice preconditions, the per-edge signature check, the RELINK equality and the
//!   postcondition ([`append_instance_body`], [`relink_monomorphic_body`]);
//! * the whole-module checks on the result ([`tables_unchanged`],
//!   `trust_thir_lower::instance_admission::assembled_codegen_validation_errors`,
//!   [`body_gates_are_stamped`]);
//! * whether the output-gate policy is the strict one, D17's condition for an APPENDED body
//!   ([`strict_gate_from`], read from the session, never passed in).
//!
//! A concrete local FnOnce closure with region-only parent arguments uses
//! its exact conserved source handoff. Its three synthetic closure arguments
//! describe kind, signature and captures; they are not generic substitutions.
//! This route adds no function or table row and invents no adapter or call edge.
//!
//! # The generic-instance decision: splice, not real calls
//!
//! A generic instance's body is lowered at codegen time by the instance-keyed producer
//! (`trust_thir_lower::trust_ir_of_instance_body`) and SPLICED into a private copy (`star`) of the
//! finalize-assembled crate module; its caller's call edge is pointed at it. The existing leaf
//! inliner (`trust_cg_bridge::module_to_lir`, `inline_local_pure_leaf_calls`) then removes the
//! call, and the strict proven-output gate composes the callee from its own trust-ir
//! (`verify_output_trust_ir::eval_ir_call`). No `bl` is emitted between spliced bodies, so the
//! gate never has to compose one — that is increment 5's job (real call edges).
//!
//! The gate refuses a codegen unit whose gate sources disagree on the global and type tables
//! (`canonical_gate_global_module`), so every body this lane appends must add NO table row: the
//! splice is TABLE-FREE by precondition, and [`tables_unchanged`] is the tripwire on the result.
//! A table-bearing instance body needs the crate module's table remap, which lives in the frozen
//! `crate_module.rs`; it is refused here, never approximated.
//!
//! # Structural admission and explicit diagnostic evidence (D17)
//!
//! A GENERIC instance exists only at codegen. Its ordinary admission uses the structural checks
//! below PLUS the strict
//! output gate, without a per-instance MIR comparison, disclosed per function. The explicit
//! default-off TEST-ORACLE additionally compares the real instance lowering; only its successful
//! measurements use `Spliced::AppendedMirCompared`, granting no production or proof authority. Both
//! conditions are enforced: a generic body is APPENDED only when the session's output-gate policy
//! is the strict one ([`strict_gate_from`]; under `allow-unknown` or `off` it is refused
//! `[instance-assembly]`), and every spliced body (generic-instance or relinked-monomorphic) that
//! reaches emitted code is disclosed — after the gate, with its verdict — in a note and in
//! `<out-dir>/<output filestem>.trust-instance-coverage.json` (the per-function coverage artifact,
//! bound to the SHA-256 of the emitted object; [`Plan::spliced`] is its input). MONOMORPHIC
//! callees are never re-lowered into code: they are RELINKED — the handoff body is kept (its seam
//! verdict, if any, does not cover the retargeted call sites), and only its call edges are
//! retargeted after the instance lowering was checked EQUAL to it modulo callee ids, each host
//! declaration checked to name the guest edge's definition and, when its name carries a
//! concrete key, its instance — and a monomorphic callee with NO handoff body is refused, so
//! finalize's vetoes stay binding on callees, not just on work items.
//!
//! # Body gates in `star`
//!
//! Appended bodies carry `BodyGate::Gated { authority: TRUST_INSTANCE_LANE_AUTHORITY }`; relinked
//! bodies keep the gate finalize stamped. `star` also inherits the base's
//! `trust-direct-lane-structural` stamps, and that authority's leg 4 ("the module holds NO
//! body-bearing function outside that set", `crate_module::compute_codegen_license`) is a claim
//! about the BASE module: it is NOT asserted for `star`, which holds the appended bodies too. The
//! default lane does not read `body_gate` (crate-module mode, which does, never sees `star`), and
//! no body of `star` is ever left with no claim ([`body_gates_are_stamped`]).
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::BTreeMap;
use std::sync::Arc;

use rustc_data_structures::fx::FxHashMap;
use rustc_middle::ty::{self, TyCtxt, TypeVisitableExt};
use trust_cg_bridge::codegen_backend as bridge_backend;
use trust_ir::function_dependencies::{
    DependencyNode, DependencyRefusalKind, DependencySite, inspect_function_dependencies,
};
use trust_ir::value::{BlockId, FuncId, SourceSpan};
use trust_ir::{BodyGate, FuncTy, Function, Inst, Module, Producer};

use super::{FrontendRefusal, GenericPolicy, local_body_def, upstream_entry};

mod closure_source;

/// The body-gate AUTHORITY this lane stamps on every body it APPENDS to `star`.
///
/// What the instance lane CHECKED before stamping it — exactly this, and nothing more:
///
/// 1. the instance-keyed producer's gate (`trust_thir_lower::instance_admission`, frozen with
///    this file, whose `Admitted` token the body carries for this very instance): no unsupported
///    shape, no residual parameter (an unreported lane is one), no pending-const sentinel, none of
///    the placeholder lanes (at least those `crate_module::splice_ok` refuses), no elided drop,
///    one body function, and every `Item` callee edge re-derived from its call site;
/// 2. the producer's standalone checks: the instance module is SELF-CONTAINED (the body plus one
///    signed declaration per callee edge, and trust-ir's dependency census refuses nothing else)
///    and passes `trust_ir_build::validate_module` on a target-stamped copy;
/// 3. the splice preconditions ([`guest_splice_preconditions`]): no table of any kind, no
///    function pointer, no instruction outside the set `crate_module::splice_refusal` models
///    (no `Invoke`, no `Drop`), no proof context, no summary, no source provenance, and every
///    function the body names is reached through a direct call to one of its own declarations;
/// 4. every call edge maps to a body whose signature and calling convention equal the
///    declaration's ([`check_edges`]), each such body admitted by this same lane or a
///    handoff body (never re-lowered) that passed the drop check;
/// 5. the postcondition: the spliced body's census call edges equal the guest's, mapped through
///    the edge map;
/// 6. on the whole `star`: [`tables_unchanged`], the finalize validator
///    (`trust_thir_lower::instance_admission::assembled_codegen_validation_errors`) and
///    [`body_gates_are_stamped`];
/// 7. the session's output-gate policy is the strict one ([`strict_gate_from`]).
///
/// What it does NOT assert: any MIR seam differential (D17), any flip, any discharged proof
/// obligation. That the emitted BYTES implement the body is the strict proven-output gate's job,
/// as for every spliced body.
pub(crate) const TRUST_INSTANCE_LANE_AUTHORITY: &str = "trust-instance-lane-structural";

// ===========================================================================
// PURE HALF — no `TyCtxt`; unit-tested in `instance_assembly/tests.rs`.
// ===========================================================================

/// Does any function reachable from `root` lack a body?
pub(crate) fn reaches_declaration(module: &Module, root: FuncId) -> bool {
    inspect_function_dependencies(module, root)
        .refusals()
        .iter()
        .any(|refusal| matches!(refusal.kind, DependencyRefusalKind::BodylessFunction(_)))
}

/// Route only recorded foreign prototypes to the existing compiler-native
/// transport. This chooses no callee body and grants no ABI/proof authority:
/// original Item/FnAbi admission and native physical checking follow it.
fn reaches_only_recorded_foreign_declarations(module: &Module, root: FuncId) -> bool {
    let census = inspect_function_dependencies(module, root);
    !census.refusals().is_empty() && census.refusals().iter().all(|problem| matches!(problem.kind,
        DependencyRefusalKind::BodylessFunction(id)
            if super::native_source_module::foreign_declarations::recorded(module, id)))
}

/// Does the census from `root` reach a `Producer::Clean` function?
pub(crate) fn reaches_clean_body(module: &Module, root: FuncId) -> bool {
    inspect_function_dependencies(module, root).nodes().iter().any(|node| match node {
        DependencyNode::Function(id) => {
            module.function_by_id(*id).is_some_and(|f| f.producer == Some(Producer::Clean))
        }
        _ => false,
    })
}

/// Does `root` CALL nothing — no function but itself is reached, and no instruction names a
/// function, itself included? A self-recursive body is not a leaf: its self edge is a cycle,
/// refused like every other one.
pub(crate) fn is_leaf(module: &Module, root: FuncId) -> bool {
    let census = inspect_function_dependencies(module, root);
    census.nodes().iter().all(|node| !matches!(node, DependencyNode::Function(id) if *id != root))
        && !census.edges().iter().any(|edge| {
            matches!(
                (edge.site, edge.target),
                (DependencySite::Instruction { .. }, DependencyNode::Function(_))
            )
        })
}

/// D17's second condition, decided HERE from the session's own inputs rather than passed in: is
/// the proven-output gate policy the STRICT one? The same three-way match the emission path makes
/// (`output_gate_mode_for_verification` in the crate root): under batteries-on strict
/// verification every accepted `-Ztrust-cg-output-gate` value is strict (`off` is a fatal error
/// there, so it answers `false`); otherwise the flag decides, and only `strict` is strict. An
/// unknown value answers `false`. PURE.
pub(crate) fn strict_gate_from(strict_verification: bool, configured: &str) -> bool {
    match (strict_verification, configured) {
        (true, "strict" | "allow-unknown") => true,
        (false, "strict") => true,
        _ => false,
    }
}

/// [`strict_gate_from`] over this session.
#[allow(rustc::bad_opt_access)]
pub(super) fn session_gate_is_strict(sess: &rustc_session::Session) -> bool {
    strict_gate_from(
        sess.trust_strict_verification_enabled(),
        &sess.opts.unstable_opts.trust_cg_output_gate,
    )
}

/// Does the producer's admission token name the instance the assembler asked for? PURE over any
/// comparable identity (the assembler passes `ty::Instance`s).
pub(crate) fn token_names<T: PartialEq + std::fmt::Debug>(
    token: T,
    asked: T,
) -> Result<(), String> {
    if token == asked {
        Ok(())
    } else {
        Err(format!("the producer's admission token names another instance ({token:?})"))
    }
}

/// Is `module`'s function `id` named exactly `expected` (a link-time symbol)? PURE.
pub(crate) fn function_is_named(module: &Module, id: FuncId, expected: &str) -> Result<(), String> {
    match module.function_by_id(id) {
        Some(function) if function.name == expected => Ok(()),
        Some(function) => Err(format!(
            "FuncId({}) is named `{}`, not `{expected}`, the link-time symbol of the instance it \
             stands for",
            id.index(),
            function.name
        )),
        None => Err(format!("FuncId({}) is missing", id.index())),
    }
}

/// Which lane a reachable item lowers on.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum LaneChoice {
    /// Lowered from `star`, the instance-keyed codegen module.
    Instance,
    /// Lowered from the unmodified finalize-assembled module, exactly as before.
    Handoff,
}

/// THE LANE PREDICATE, decided before any lowering and never by retrying after a failure.
///
/// A concrete generic instance has no handoff body, so it is the instance lane's. A monomorphic
/// item is too exactly when its assembled body reaches a bodyless declaration — a `Call` the leaf
/// inliner cannot remove, which the converter refuses on the handoff lane — unless it reaches a
/// Clean-origin body, which the handoff lane's converter refuses BY NAME and this lane must not
/// launder into an instance-assembly refusal.
pub(crate) fn lane_for(generic: bool, reaches_decl: bool, reaches_clean: bool) -> LaneChoice {
    if generic || (reaches_decl && !reaches_clean) {
        LaneChoice::Instance
    } else {
        LaneChoice::Handoff
    }
}

fn instruction_at(
    module: &Module,
    function: FuncId,
    block: BlockId,
    index: usize,
) -> Option<&Inst> {
    module
        .function_by_id(function)
        .and_then(|f| f.blocks.iter().find(|b| b.id == block))
        .and_then(|b| b.body.get(index))
        .map(|node| &node.inst)
}

/// A direct call. `Invoke` is NOT one here: the handoff's splice refuses it
/// (`SpliceRefusal::Invoke`), and so does [`instruction_is_spliceable`].
fn is_direct_call(inst: Option<&Inst>) -> bool {
    matches!(inst, Some(Inst::Call { .. }))
}

/// Is `inst` one the handoff's splice MODELS? Exactly the variants for which
/// `crate_module::inst_embedded_tys` answers `Some` (anything else is
/// `SpliceRefusal::UnmodeledInstruction`), so the instance lane admits no instruction the handoff
/// splice would refuse. A whitelist: a new `Inst` variant is refused until it is added here, and
/// `Invoke` (refused by name there) and `Drop` (a runtime service, increment 4) are not in it.
pub(crate) fn instruction_is_spliceable(inst: &Inst) -> bool {
    matches!(
        inst,
        Inst::BinOp { .. }
            | Inst::UnOp { .. }
            | Inst::Overflow { .. }
            | Inst::ICmp { .. }
            | Inst::FCmp { .. }
            | Inst::Load { .. }
            | Inst::Store { .. }
            | Inst::Alloca { .. }
            | Inst::ExtractField { .. }
            | Inst::InsertField { .. }
            | Inst::ExtractElement { .. }
            | Inst::InsertElement { .. }
            | Inst::ArraySplat { .. }
            | Inst::Undef { .. }
            | Inst::Copy { .. }
            | Inst::Select { .. }
            | Inst::Cast { .. }
            | Inst::GEP { .. }
            | Inst::PtrData { .. }
            | Inst::PtrMetadata { .. }
            | Inst::PtrFromParts { .. }
            | Inst::Const { .. }
            | Inst::Br { .. }
            | Inst::CondBr { .. }
            | Inst::Switch { .. }
            | Inst::Call { .. }
            | Inst::CallIndirect { .. }
            | Inst::Return { .. }
            | Inst::Assume { .. }
            // Trust (trust-ir v54): lockstep with `inst_embedded_tys` — a SITED assert names a
            // panic entry and location no splice pass remaps, so only a siteless one is admitted.
            | Inst::Assert { site: None, .. }
            | Inst::Unreachable
            | Inst::GlobalAddr { .. }
            | Inst::NullPtr
    )
}

/// The variant name of `inst`, for a refusal message.
fn inst_name(inst: &Inst) -> String {
    let debug = format!("{inst:?}");
    debug.split(|c: char| !c.is_alphanumeric() && c != '_').next().unwrap_or("?").to_string()
}

/// THE SPLICE PRECONDITIONS on a guest instance module with `n` callee declarations.
///
/// Table-freedom is stated EXPLICITLY, table by table, rather than inferred from the dependency
/// census: the census treats an inline `Ty::Tuple` as a leaf while the producer pends a `types`
/// row and a tuple-layout descriptor for it, and it does not model predicates, universes, spec
/// modules, imports, proof tables or completeness at all. The census is used for EDGES only.
pub(crate) fn guest_splice_preconditions(
    guest: &Module,
    n: usize,
    fn_pointer_free: bool,
) -> Result<(), String> {
    let tables: [(&str, bool); 17] = [
        ("structs", guest.structs.is_empty()),
        ("enums", guest.enums.is_empty()),
        ("records", guest.records.is_empty()),
        ("closure_types", guest.closure_types.is_empty()),
        ("globals", guest.globals.is_empty()),
        ("types", guest.types.is_empty()),
        ("tuple_layouts", guest.tuple_layouts.is_empty()),
        ("predicates", guest.predicates.is_empty()),
        ("universes", guest.universes.is_empty()),
        ("spec_modules", guest.spec_modules.is_empty()),
        ("imports", guest.imports.is_empty()),
        ("global_asm", guest.global_asm.is_empty()),
        ("proof_obligations", guest.proof_obligations.is_empty()),
        ("proof_certificates", guest.proof_certificates.is_empty()),
        ("obligation_diagnostics", guest.obligation_diagnostics.is_empty()),
        // Trust (trust-ir v55): the drop-glue table keys glue functions by type.
        ("drop_glue", guest.drop_glue.is_empty()),
        // Trust (trust-ir v58): the closure-frame table keys frames by `ClosureTyId`.
        ("closure_layouts", guest.closure_layouts.is_empty()),
    ];
    for (table, empty) in tables {
        if !empty {
            return Err(format!(
                "the instance module carries a `{table}` table; a table-bearing body needs the \
                 crate module's table remap, which the instance lane does not have"
            ));
        }
    }
    if guest.completeness.is_some() {
        return Err("the instance module carries a completeness claim".to_string());
    }
    if !fn_pointer_free {
        return Err("the instance body names a function pointer (a first-class function value \
                    or an indirect-call signature); only direct calls are spliceable"
            .to_string());
    }
    if guest.functions.len() != n + 1 {
        return Err(format!(
            "the instance module holds {} function(s) where the body plus {n} declaration(s) \
             were expected",
            guest.functions.len()
        ));
    }
    for (position, function) in guest.functions.iter().enumerate() {
        if function.id != FuncId::new(position as u32) {
            return Err(format!("the instance module's ids are not dense at position {position}"));
        }
        if (position == 0) == function.blocks.is_empty() {
            return Err(format!(
                "FuncId({position}) of the instance module is not a {}",
                if position == 0 { "body" } else { "declaration" }
            ));
        }
    }
    let body = &guest.functions[0];
    if body.summary.is_some() {
        return Err("the instance body carries a separate-compilation summary".to_string());
    }
    if body.source_provenance.is_some() {
        return Err("the instance body carries sealed source provenance, whose digests a \
                    callee rewrite would falsify"
            .to_string());
    }
    for block in &body.blocks {
        for node in &block.body {
            if !instruction_is_spliceable(&node.inst) {
                return Err(format!(
                    "the instance body carries an instruction the handoff's splice does not \
                     model ({}); an `Invoke`, a `Drop` (increment 4), memory intrinsics, atomics, \
                     borrows, aggregates, heap, frame and unwind operations are refused",
                    inst_name(&node.inst)
                ));
            }
            if node.proof_context.is_some() {
                return Err("the instance body carries a call-site proof context naming \
                            obligations the splice does not carry"
                    .to_string());
            }
        }
    }
    let census = inspect_function_dependencies(guest, FuncId::new(0));
    for edge in census.edges() {
        let admitted = match (edge.site, edge.target) {
            (DependencySite::Root, DependencyNode::Function(id)) => id == FuncId::new(0),
            (
                DependencySite::Definition(DependencyNode::Function(function)),
                DependencyNode::FunctionType(signature),
            ) => guest.function_by_id(function).is_some_and(|f| f.ty == signature),
            (
                DependencySite::Instruction { function, block, index },
                DependencyNode::Function(target),
            ) => {
                function == FuncId::new(0)
                    && (1..=n).contains(&(target.index() as usize))
                    && is_direct_call(instruction_at(guest, function, block, index))
            }
            _ => false,
        };
        if !admitted {
            return Err(format!(
                "the instance body names {:?} from {:?}; only direct calls to its own callee \
                 declarations are spliceable",
                edge.target, edge.site
            ));
        }
    }
    for refusal in census.refusals() {
        match &refusal.kind {
            DependencyRefusalKind::BodylessFunction(id)
                if (1..=n).contains(&(id.index() as usize)) => {}
            other => return Err(format!("the dependency census refuses {other:?}")),
        }
    }
    Ok(())
}

/// THE PER-EDGE SIGNATURE CHECK: every declaration `FuncId(k)`, `1 <= k <= n`, of `guest` maps
/// through `edges` to a BODY of `host` whose signature — parameters, result arity and types,
/// variadicity — and calling convention equal the declaration's.
///
/// A declaration's signature is the CALLER's view (the callee's `fn_sig` at the instance plus the
/// result type its call sites bind), so this is what makes the caller's call instructions
/// well-typed against the body they now name. A mismatch refuses THIS caller, naming the edge.
pub(crate) fn check_edges(
    host: &Module,
    guest: &Module,
    n: usize,
    edges: &BTreeMap<FuncId, FuncId>,
) -> Result<(), String> {
    if edges.len() != n || edges.keys().any(|k| !(1..=n).contains(&(k.index() as usize))) {
        return Err(format!(
            "the edge map covers {:?} but the instance module declares FuncId(1..={n})",
            edges.keys().map(|k| k.index()).collect::<Vec<_>>()
        ));
    }
    for k in 1..=n {
        let key = FuncId::new(k as u32);
        let declaration = guest
            .function_by_id(key)
            .ok_or_else(|| format!("the instance module has no declaration FuncId({k})"))?;
        let target = edges[&key];
        let body = host.function_by_id(target).ok_or_else(|| {
            format!(
                "edge FuncId({k}) `{}` maps to FuncId({}), which the codegen module lacks",
                declaration.name,
                target.index()
            )
        })?;
        if body.blocks.is_empty() {
            return Err(format!(
                "edge FuncId({k}) `{}` maps to the bodyless declaration FuncId({}) `{}`",
                declaration.name,
                target.index(),
                body.name
            ));
        }
        if body.producer == Some(Producer::Clean) {
            return Err(format!(
                "edge FuncId({k}) `{}` maps to the Clean-origin body `{}`",
                declaration.name, body.name
            ));
        }
        let declared = guest
            .func_types
            .get(declaration.ty.as_usize())
            .ok_or_else(|| format!("declaration `{}` names a missing FuncTy", declaration.name))?;
        let actual = host
            .func_types
            .get(body.ty.as_usize())
            .ok_or_else(|| format!("body `{}` names a missing FuncTy", body.name))?;
        if declared != actual || declaration.calling_conv != body.calling_conv {
            return Err(format!(
                "signature mismatch on edge FuncId({k}) `{}` -> FuncId({}) `{}`: the call site \
                 declares {declared:?} ({:?}) but the body is {actual:?} ({:?})",
                declaration.name,
                target.index(),
                body.name,
                declaration.calling_conv,
                body.calling_conv
            ));
        }
    }
    Ok(())
}

/// Guest file index -> host file index, plus the file names the host must append.
struct FilePlan {
    map: Vec<u32>,
    appended: Vec<String>,
}

fn plan_files(host_files: &[String], guest_files: &[String]) -> Result<FilePlan, String> {
    let mut map = Vec::with_capacity(guest_files.len());
    let mut appended: Vec<String> = Vec::new();
    for name in guest_files {
        let index = match host_files.iter().position(|h| h == name) {
            Some(i) => i,
            None => match appended.iter().position(|a| a == name) {
                Some(i) => host_files.len() + i,
                None => {
                    appended.push(name.clone());
                    host_files.len() + appended.len() - 1
                }
            },
        };
        map.push(u32::try_from(index).map_err(|_| "file table exceeds u32".to_string())?);
    }
    Ok(FilePlan { map, appended })
}

fn remap_span(span: &mut SourceSpan, map: &[u32]) -> Result<(), String> {
    span.file = *map.get(span.file as usize).ok_or_else(|| {
        format!("a span names file #{} the instance module does not carry", span.file)
    })?;
    Ok(())
}

/// Re-intern every `SourceSpan.file` of `function` (instruction spans and the scope tree) through
/// `map`. A dangling file index refuses.
fn remap_function_spans(function: &mut Function, map: &[u32]) -> Result<(), String> {
    for block in &mut function.blocks {
        for node in &mut block.body {
            if let Some(span) = node.span.as_mut() {
                remap_span(span, map)?;
            }
        }
    }
    if let Some(scopes) = function.scopes.as_mut() {
        for scope in scopes {
            if let Some(span) = scope.span.as_mut() {
                remap_span(span, map)?;
            }
            if let Some(inlined) = scope.inlined_at.as_mut() {
                remap_span(&mut inlined.span, map)?;
            }
        }
    }
    Ok(())
}

/// Point every `Call` of `function` through `edges`. An unmapped callee refuses.
fn remap_calls(function: &mut Function, edges: &BTreeMap<FuncId, FuncId>) -> Result<(), String> {
    for block in &mut function.blocks {
        for node in &mut block.body {
            if let Inst::Call { callee, .. } = &mut node.inst {
                *callee = *edges.get(callee).ok_or_else(|| {
                    format!(
                        "the instance body calls FuncId({}), which no edge maps",
                        callee.index()
                    )
                })?;
            }
        }
    }
    Ok(())
}

/// `(block, index, callee)` of every instruction-site FUNCTION edge of `root`, in trust-ir's own
/// census order — the exhaustive instruction walker, not a hand-written list.
fn instruction_function_edges(module: &Module, root: FuncId) -> Vec<(BlockId, usize, FuncId)> {
    inspect_function_dependencies(module, root)
        .edges()
        .iter()
        .filter_map(|edge| match (edge.site, edge.target) {
            (
                DependencySite::Instruction { function, block, index },
                DependencyNode::Function(t),
            ) if function == root => Some((block, index, t)),
            _ => None,
        })
        .collect()
}

/// THE POSTCONDITION: the census of `host` from `spliced` finds exactly the guest body's
/// instruction-site function edges, element by element, mapped through `edges`. A rewrite the
/// splice missed (or one it made that it should not have) fails here.
fn call_edges_match(
    host: &Module,
    spliced: FuncId,
    guest: &Module,
    edges: &BTreeMap<FuncId, FuncId>,
) -> Result<(), String> {
    let actual = instruction_function_edges(host, spliced);
    let expected: Vec<(BlockId, usize, Option<FuncId>)> =
        instruction_function_edges(guest, FuncId::new(0))
            .into_iter()
            .map(|(block, index, target)| (block, index, edges.get(&target).copied()))
            .collect();
    let actual: Vec<(BlockId, usize, Option<FuncId>)> =
        actual.into_iter().map(|(block, index, target)| (block, index, Some(target))).collect();
    if actual != expected {
        return Err(format!(
            "postcondition: the spliced body's call edges {actual:?} are not the instance body's \
             edges mapped through the edge map {expected:?}"
        ));
    }
    Ok(())
}

/// Lengths of the tables a splice appends to, so a failed postcondition can undo the commit.
struct Snapshot {
    files: usize,
    func_types: usize,
    functions: usize,
    proof_obligations: usize,
}

impl Snapshot {
    fn of(module: &Module) -> Self {
        Self {
            files: module.files.len(),
            func_types: module.func_types.len(),
            functions: module.functions.len(),
            proof_obligations: module.proof_obligations.len(),
        }
    }

    fn restore(self, module: &mut Module) {
        module.files.truncate(self.files);
        module.func_types.truncate(self.func_types);
        module.functions.truncate(self.functions);
        module.proof_obligations.truncate(self.proof_obligations);
    }
}

/// Install a concrete instance body through the existing sole appender.
/// Unbound inputs append at a fresh ID. Only a private actual-handoff R binding
/// may fill its exact original declaration ID; an unbound symbol collision refuses.
///
/// TRANSACTIONAL: every check runs before any mutation, and a failed postcondition or a refused
/// table door (trust-ir D1b) undoes the commit. The body keeps the guest's name (the instance's
/// mangled symbol), producer and calling convention; its destination ID is set BEFORE
/// `Module::try_add_function` or its fallible synthesis half, whose synthesized
/// obligations key on it), its call edges pointed through `edges`, its spans re-interned through
/// the host's file table, its signature interned into the host's (deduplicated by equality), and
/// the [`TRUST_INSTANCE_LANE_AUTHORITY`] body gate. Annotation claims synthesize only
/// Pending obligations; no global/type table remap or proof authority is inferred.
pub(crate) fn append_instance_body(
    binding: Option<&declaration_binding::BoundDeclaration>,
    host: &mut Module,
    guest: &Module,
    n: usize,
    fn_pointer_free: bool,
    edges: &BTreeMap<FuncId, FuncId>,
) -> Result<FuncId, String> {
    guest_splice_preconditions(guest, n, fn_pointer_free)?;
    check_edges(host, guest, n, edges)?;
    let body = &guest.functions[0];
    let replaced = if let Some(clash) = host.functions.iter().find(|f| f.name == body.name) {
        let Some(binding) = binding else {
            return Err(format!(
                "the codegen module already holds FuncId({}) named `{}`",
                clash.id.index(), body.name
            ));
        };
        if binding.slot(host, guest)? != clash.id {
            return Err("bound upstream declaration names another installation slot".into());
        }
        Some(clash.clone())
    } else {
        if binding.is_some() {
            return Err("bound upstream declaration is absent from the current image".into());
        }
        None
    };
    if host.functions.iter().enumerate().any(|(i, f)| f.id.as_usize() != i) {
        return Err("the codegen module's function ids are not dense".to_string());
    }
    let new_id = match &replaced {
        Some(original) => original.id,
        None => FuncId::new(u32::try_from(host.functions.len()).map_err(|_| "function table exceeds u32")?),
    };
    let signature = guest
        .func_types
        .get(body.ty.as_usize())
        .cloned()
        .ok_or("the instance body names a missing FuncTy")?;
    let files = plan_files(&host.files, &guest.files)?;
    let mut function = body.clone();
    function.id = new_id;
    remap_calls(&mut function, edges)?;
    remap_function_spans(&mut function, &files.map)?;
    function.body_gate = Some(BodyGate::Gated {
        authority: TRUST_INSTANCE_LANE_AUTHORITY.to_string(),
        evidence: None,
    });

    let snapshot = Snapshot::of(host);
    host.files.extend(files.appended);
    function.ty = match host.intern_func_type(signature) {
        Ok(func_ty) => func_ty,
        Err(refusal) => {
            snapshot.restore(host);
            return Err(refusal.to_string());
        }
    };
    if replaced.is_some() {
        // The same annotation-obligation synthesis as try_add_function's
        // append door. Reusing an ID must never skip a claim or mint a proof.
        if let Err(refusal) = host.synthesize_function_obligations(&function) {
            snapshot.restore(host);
            return Err(refusal.to_string());
        }
        host.functions[new_id.as_usize()] = function;
    } else {
        if let Err(refusal) = host.try_add_function(function) {
            snapshot.restore(host);
            return Err(refusal.to_string());
        }
    }
    if let Err(error) = call_edges_match(host, new_id, guest, edges) {
        snapshot.restore(host);
        if let Some(original) = replaced {
            host.functions[new_id.as_usize()] = original;
        }
        return Err(error);
    }
    Ok(new_id)
}

fn resolved_span<'a>(
    files: &'a [String],
    span: &Option<SourceSpan>,
) -> Result<Option<(&'a str, u32, u32)>, String> {
    match span {
        None => Ok(None),
        Some(span) => files
            .get(span.file as usize)
            .map(|file| Some((file.as_str(), span.line, span.col)))
            .ok_or_else(|| format!("a span names dangling file #{}", span.file)),
    }
}

/// `(callee, the instruction with its callee blanked)` for a direct call, `None` otherwise.
fn call_parts(inst: &Inst) -> Option<(FuncId, Inst)> {
    let mut blanked = inst.clone();
    match &mut blanked {
        Inst::Call { callee, .. } | Inst::Invoke { callee, .. } => {
            let original = *callee;
            *callee = FuncId::new(0);
            Some((original, blanked))
        }
        _ => None,
    }
}

/// THE RELINK EQUALITY: is `guest`'s body the SAME body as `host`'s, modulo the ids its direct
/// calls name and the numbering of source files?
///
/// Compared: entry, every block's id, parameters and instructions (results, instruction-level
/// proof annotations, proof context, scope, span resolved to `(file, line, col)`, and the
/// instruction itself with only a direct call's callee blanked), value names and the scope tree.
/// Returns the `(host callee, guest callee)` pair of every direct call, in body order; the pairing
/// must be a BIJECTION, or one guest edge would stand for two host callees.
pub(crate) fn body_correspondence(
    host: &Function,
    host_files: &[String],
    guest: &Function,
    guest_files: &[String],
) -> Result<Vec<(FuncId, FuncId)>, String> {
    if host.entry != guest.entry {
        return Err("the entry blocks differ".to_string());
    }
    if host.blocks.len() != guest.blocks.len() {
        return Err(format!("{} blocks against {}", host.blocks.len(), guest.blocks.len()));
    }
    let mut pairs = Vec::new();
    let mut by_guest: BTreeMap<FuncId, FuncId> = BTreeMap::new();
    let mut by_host: BTreeMap<FuncId, FuncId> = BTreeMap::new();
    for (hb, gb) in host.blocks.iter().zip(&guest.blocks) {
        if hb.id != gb.id || hb.params != gb.params || hb.body.len() != gb.body.len() {
            return Err(format!("block {} differs in id, parameters or length", hb.id.index()));
        }
        for (index, (hn, gn)) in hb.body.iter().zip(&gb.body).enumerate() {
            let at = format!("block {} instruction {index}", hb.id.index());
            if hn.results != gn.results
                || hn.proofs != gn.proofs
                || hn.proof_context != gn.proof_context
                || hn.scope != gn.scope
            {
                return Err(format!("{at}: results, proofs, proof context or scope differ"));
            }
            if resolved_span(host_files, &hn.span)? != resolved_span(guest_files, &gn.span)? {
                return Err(format!("{at}: source spans differ"));
            }
            match (call_parts(&hn.inst), call_parts(&gn.inst)) {
                (Some((h, hi)), Some((g, gi))) => {
                    if hi != gi {
                        return Err(format!("{at}: the calls differ beyond their callee"));
                    }
                    if *by_guest.entry(g).or_insert(h) != h || *by_host.entry(h).or_insert(g) != g {
                        return Err(format!(
                            "{at}: callee FuncId({}) of the instance body and FuncId({}) of the \
                             assembled body do not correspond one to one",
                            g.index(),
                            h.index()
                        ));
                    }
                    pairs.push((h, g));
                }
                (None, None) => {
                    if hn.inst != gn.inst {
                        return Err(format!("{at}: the instructions differ"));
                    }
                }
                _ => return Err(format!("{at}: only one side is a direct call")),
            }
        }
    }
    if host.value_names != guest.value_names {
        return Err("the value names differ".to_string());
    }
    match (&host.scopes, &guest.scopes) {
        (None, None) => {}
        (Some(hs), Some(gs)) if hs.len() == gs.len() => {
            for (h, g) in hs.iter().zip(gs) {
                let same_inlined = match (&h.inlined_at, &g.inlined_at) {
                    (None, None) => true,
                    (Some(hi), Some(gi)) => {
                        hi.callee == gi.callee
                            && resolved_span(host_files, &Some(hi.span))?
                                == resolved_span(guest_files, &Some(gi.span))?
                    }
                    _ => false,
                };
                if h.parent != g.parent
                    || resolved_span(host_files, &h.span)? != resolved_span(guest_files, &g.span)?
                    || !same_inlined
                {
                    return Err("the scope trees differ".to_string());
                }
            }
        }
        _ => return Err("the scope trees differ".to_string()),
    }
    Ok(pairs)
}

/// RELINK a MONOMORPHIC slot of `host`: keep the handoff's body — name, signature, body gate,
/// proofs, obligations, lineage — and retarget only its direct calls.
///
/// The instance lowering `guest` must be the SAME body ([`body_correspondence`]) with the same
/// signature, or the relink refuses with "instance lowering diverges from the assembled body":
/// nothing lowered on the instance lane replaces a finalize-assembled body. A host callee that is
/// already a BODY must be exactly the body the edge map names; only a bodyless declaration is
/// retargeted, and only after `decl_names_edge(host declaration name, guest callee id)` confirms
/// the declaration names the guest edge's definition and, when the name carries a concrete key,
/// its instance (`declaration_names_instance`) — the pairing is by position and bijection, and
/// the identity check is what makes it more than position. TRANSACTIONAL, like
/// [`append_instance_body`].
pub(crate) fn relink_monomorphic_body(
    host: &mut Module,
    slot: FuncId,
    guest: &Module,
    n: usize,
    fn_pointer_free: bool,
    edges: &BTreeMap<FuncId, FuncId>,
    decl_names_edge: &dyn Fn(&str, FuncId) -> Result<(), String>,
) -> Result<(), String> {
    guest_splice_preconditions(guest, n, fn_pointer_free)?;
    check_edges(host, guest, n, edges)?;
    let host_body = host
        .function_by_id(slot)
        .ok_or_else(|| format!("the codegen module has no FuncId({})", slot.index()))?;
    if host_body.blocks.is_empty() {
        return Err(format!("FuncId({}) `{}` is a declaration", slot.index(), host_body.name));
    }
    let guest_body = &guest.functions[0];
    let host_signature = host.func_types.get(host_body.ty.as_usize());
    let guest_signature = guest.func_types.get(guest_body.ty.as_usize());
    if host_signature.is_none() || host_signature != guest_signature {
        return Err(format!(
            "instance lowering diverges from the assembled body `{}`: signature \
             {guest_signature:?} against {host_signature:?}",
            host_body.name
        ));
    }
    let pairs =
        body_correspondence(host_body, &host.files, guest_body, &guest.files).map_err(|why| {
            format!(
                "instance lowering diverges from the assembled body `{}`: {why}",
                host_body.name
            )
        })?;
    let mut targets = Vec::with_capacity(pairs.len());
    for (host_callee, guest_callee) in pairs {
        let target = *edges.get(&guest_callee).ok_or_else(|| {
            format!("guest callee FuncId({}) is not in the edge map", guest_callee.index())
        })?;
        let existing = host.function_by_id(host_callee).ok_or_else(|| {
            format!("the assembled body names missing FuncId({})", host_callee.index())
        })?;
        if !existing.blocks.is_empty() && host_callee != target {
            return Err(format!(
                "the assembled body `{}` links the BODY FuncId({}) `{}`, but the instance lane \
                 resolves that edge to FuncId({}); a linked body edge is never retargeted",
                host_body.name,
                host_callee.index(),
                existing.name,
                target.index()
            ));
        }
        if existing.blocks.is_empty() {
            decl_names_edge(&existing.name, guest_callee).map_err(|why| {
                format!(
                    "the assembled body `{}` calls the declaration FuncId({}) `{}`, which does \
                     not name the instance its guest edge FuncId({}) resolved to: {why}",
                    host_body.name,
                    host_callee.index(),
                    existing.name,
                    guest_callee.index()
                )
            })?;
        }
        targets.push(target);
    }

    let original = host_body.clone();
    let function = host.function_by_id_mut(slot).ok_or("the slot vanished")?;
    let mut next = targets.into_iter();
    for block in &mut function.blocks {
        for node in &mut block.body {
            if let Inst::Call { callee, .. } | Inst::Invoke { callee, .. } = &mut node.inst {
                // `body_correspondence` paired every direct call, so the counts agree.
                if let Some(target) = next.next() {
                    *callee = target;
                }
            }
        }
    }
    if let Err(error) = call_edges_match(host, slot, guest, edges) {
        if let Some(function) = host.function_by_id_mut(slot) {
            *function = original;
        }
        return Err(error);
    }
    Ok(())
}

/// THE TABLE TRIPWIRE: `star` carries exactly `base`'s global and type tables — the fields the
/// proven-output gate compares across gate sources (`canonical_gate_global_module`), plus the
/// tuple layouts it does not yet compare.
pub(crate) fn tables_unchanged(base: &Module, star: &Module) -> Result<(), String> {
    let same = [
        ("globals", base.globals == star.globals),
        ("types", base.types == star.types),
        ("structs", base.structs == star.structs),
        ("enums", base.enums == star.enums),
        ("records", base.records == star.records),
        ("closure_types", base.closure_types == star.closure_types),
        ("closure_layouts", base.closure_layouts == star.closure_layouts),
        ("target_info", base.target_info == star.target_info),
        ("tuple_layouts", base.tuple_layouts == star.tuple_layouts),
    ];
    match same.iter().find(|(_, equal)| !equal) {
        Some((table, _)) => Err(format!(
            "the instance-keyed codegen module's `{table}` table differs from the assembled \
             module's; every gate source must share one table image"
        )),
        None => Ok(()),
    }
}

/// No body-bearing function of `star` makes NO licensing claim: an absent `body_gate` is the
/// laundering state trust-ir's contract forbids a transform to produce.
pub(crate) fn body_gates_are_stamped(star: &Module) -> Result<(), String> {
    match star.functions.iter().find(|f| !f.blocks.is_empty() && f.body_gate.is_none()) {
        Some(f) => Err(format!(
            "body FuncId({}) `{}` of the instance-keyed codegen module carries no body gate",
            f.id.index(),
            f.name
        )),
        None => Ok(()),
    }
}

// ===========================================================================
// RUSTC HALF — the instance-keyed codegen module.
// ===========================================================================

/// Why a slot was refused. `producer` is the instance-keyed producer's own refusal of THIS
/// instance's body (the census classifies it by variant); `None` is the assembler's refusal
/// (class `instance-assembly`).
#[derive(Debug, Clone)]
struct SlotRefusal {
    producer: Option<trust_thir_lower::InstanceRefusal>,
    upstream: Option<upstream_entry::Refusal>,
    detail: String,
}

fn assembly(detail: String) -> SlotRefusal {
    SlotRefusal { producer: None, upstream: None, detail }
}

fn callee_refusal(mut refusal: SlotRefusal, caller: &str, callee: &str) -> SlotRefusal {
    let detail = format!("`{caller}`'s callee `{callee}` is refused: {}", refusal.detail);
    if let Some(upstream) = refusal.upstream.take() {
        refusal.upstream = Some(upstream.called_from());
        refusal.detail = detail;
        refusal
    } else {
        assembly(detail)
    }
}

/// Select a concrete by-value source closure through its conserved definition
/// identity. The closure's synthetic type arguments never turn a generic parent
/// into a monomorphic source body: only region-only parent arguments qualify.
fn source_closure_handoff<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: ty::Instance<'tcx>,
    symbol: &str,
) -> Result<Option<trust_thir_lower::ExactAssembledBodyForCodegen>, SlotRefusal> {
    let ty::InstanceKind::Item(def) = instance.def else {
        return Ok(None);
    };
    if tcx.def_kind(def) != rustc_hir::def::DefKind::Closure {
        return Ok(None);
    }
    let refuse = |why: String| assembly(format!("source closure `{symbol}`: {why}"));
    let Some(local) = def.as_local() else {
        return Err(refuse("no local source definition".into()));
    };
    if tcx.is_coroutine(def) || instance.args.has_non_region_param() || instance.args.has_infer() {
        return Err(refuse("requires a concrete non-coroutine source closure".into()));
    }
    let closure = instance.args.as_closure();
    if !closure.parent_args().iter().all(|arg| arg.as_region().is_some()) {
        return Err(refuse(
            "a type/const-instantiated parent has no identity-keyed source body".into(),
        ));
    }
    if closure.kind() != ty::ClosureKind::FnOnce || closure.upvar_tys().is_empty() {
        return Err(refuse(
            "only a capturing FnOnce value has the typed source environment convention".into(),
        ));
    }
    let selected = tcx
        .sess
        .with_trust_compiler_state::<trust_thir_lower::AssembledCrateModuleForCodegen, _>(
            |handoff| handoff.exact_body(tcx, local),
        )
        .map_err(|error| refuse(format!("exact source handoff refused: {error:?}")))?;
    closure_source::validate(
        &selected.module,
        selected.func_id,
        symbol,
        closure.upvar_tys().len(),
        trust_thir_lower::crate_module::TRUST_DIRECT_LANE_AUTHORITY,
    )
    .map_err(refuse)?;
    if reaches_clean_body(&selected.module, selected.func_id)
        || reaches_declaration(&selected.module, selected.func_id)
    {
        return Err(refuse(
            "source body reaches an unadmitted Clean body or bodyless call edge".into(),
        ));
    }
    trust_thir_lower::instance_admission::instance_drop_refusal(tcx, instance)
        .map_err(|error| refuse(format!("source drop check refused: {error:?}")))?;
    if selected
        .module
        .function_by_id(selected.func_id)
        .is_none_or(trust_thir_lower::instance_admission::function_has_undef_placeholder)
    {
        return Err(refuse("source body contains an undef placeholder".into()));
    }
    Ok(Some(selected))
}

/// One instance's state in the assembler. Keyed on `ty::Instance`, so `pick::<u8>` and
/// `pick::<u16>` are two slots.
enum Slot {
    InProgress,
    Done(FuncId),
    /// D40: completed actual upstream import, retaining its original/rebound identities.
    Upstream {
        id: FuncId,
        disclosure: upstream_entry::Disclosure,
    },
    Refused(SlotRefusal),
}

enum CompletedSlot {
    Local(FuncId),
    Upstream { id: FuncId, disclosure: upstream_entry::Disclosure },
}
impl CompletedSlot {
    fn id(&self) -> FuncId {
        match self {
            Self::Local(id) | Self::Upstream { id, .. } => *id,
        }
    }
}

/// How a spliced body entered `star`, for the per-function disclosure.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Spliced {
    /// A generic instance body, appended on structural admission under the strict gate (D17): no
    /// MIR seam differential.
    Appended,
    /// Same structural admission, additionally compared in the explicit MIR TEST-ORACLE lane.
    /// No proof authority or new production input follows from this diagnostic measurement.
    AppendedMirCompared,
    /// A monomorphic handoff body whose direct calls were retargeted. The body is the
    /// finalize-assembled one; its seam verdict, if it has one, does not cover the retargeted
    /// call sites.
    Relinked,
    /// D39/D40: metadata body with consumer-side conservation and identity binding.
    UpstreamEntry(upstream_entry::Disclosure),
}

pub(crate) mod declaration_binding;

struct UpstreamAssemblyInput<'tcx> {
    installed: FuncId,
    /// Present only when the sole appender filled an authenticated original
    /// declaration. Keep its exact installation premise with the sealed body;
    /// an appended body without a binding gains no replacement authority.
    declaration_binding: Option<declaration_binding::BoundDeclaration>,
    input: upstream_entry::UpstreamBody<'tcx>,
    edges: BTreeMap<FuncId, FuncId>,
    installed_image: Function,
    installed_signature: FuncTy,
}

impl UpstreamAssemblyInput<'_> {
    fn check(&self, base: &Module, module: &Module) -> Result<(), String> {
        if let Some(binding) = &self.declaration_binding {
            binding.check_retained(base, self.input.module(), self.installed)?;
        }
        if self.input.original_module().functions.len() != self.input.module().functions.len()
            || self.input.retained_evidence().ledger.len() != self.edges.len()
        {
            return Err("retained upstream original/evidence/edge population differs".into());
        }
        if module.function_by_id(self.installed) != Some(&self.installed_image)
            || module.func_type(self.installed_image.ty) != Some(&self.installed_signature)
        {
            return Err("installed upstream body differs from its retained exact image".into());
        }
        call_edges_match(module, self.installed, self.input.module(), &self.edges)
    }
}

/// Opaque, borrowed evidence for exact authenticated declaration installation.
/// Only the successful retained Plan projects these entries. Borrowing its
/// immutable payloads keeps their genuine sealed owners alive; codegen cannot
/// supply a constructor, name resolver, approval bit or replacement whitelist.
/// This licenses no body: ordinary producer/gate/ABI checks still apply.
pub(crate) struct HandoffDeclarationExtensions<'a> {
    base: &'a Module,
    star: &'a Module,
    installations: Vec<RetainedDeclarationInstallation<'a>>,
}

struct RetainedDeclarationInstallation<'a> {
    binding: &'a declaration_binding::BoundDeclaration,
    original: &'a Module,
    guest: &'a Module,
    evidence: &'a trust_thir_lower::rmeta_entry::Evidence,
    installed: FuncId,
    image: &'a Function,
    signature: &'a FuncTy,
    edges: &'a BTreeMap<FuncId, FuncId>,
}

impl std::fmt::Debug for HandoffDeclarationExtensions<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("HandoffDeclarationExtensions").finish_non_exhaustive()
    }
}

impl HandoffDeclarationExtensions<'_> {
    /// Recheck one changed original declaration against the ACTUAL input images.
    /// The producer may be the compiler's content-identical clone of star; the
    /// original base allocation must itself be retained. A transformed producer
    /// needs its own checked transformation relation and does not pass here.
    pub(crate) fn check(
        &self,
        base: &Module,
        producer: &Module,
        id: FuncId,
    ) -> Result<(), String> {
        if !std::ptr::eq(self.base, base) || self.star != producer {
            return Err("declaration extension names another original base or producer image".into());
        }
        let mut matching = self.installations.iter().filter(|entry| entry.installed == id);
        let entry = matching.next().ok_or("no authenticated declaration installation for this slot")?;
        if matching.next().is_some() {
            return Err("ambiguous authenticated declaration installations for this slot".into());
        }
        entry.binding.check_retained(base, entry.guest, id)?;
        if entry.original.functions.len() != entry.guest.functions.len()
            || entry.evidence.ledger.len() != entry.edges.len()
            || entry.image.is_declaration()
            || producer.function_by_id(id) != Some(entry.image)
            || producer.func_type(entry.image.ty) != Some(entry.signature)
        {
            return Err("retained declaration extension body, signature or sealed input population differs".into());
        }
        call_edges_match(producer, id, entry.guest, entry.edges)
    }
}

struct Assembler<'tcx> {
    base: Arc<Module>,
    star: Module,
    slots: FxHashMap<ty::Instance<'tcx>, Slot>,
    spliced: Vec<(String, FuncId, Spliced)>,
    /// The session's output-gate policy is the strict one ([`strict_gate_from`]): D17's second
    /// condition for an APPENDED body.
    strict_gate: bool,
    /// Preserve the actual sealed inputs after installation. These are source
    /// provenance, not a native adapter licence or a conserved-ID extension.
    upstream_inputs: Vec<UpstreamAssemblyInput<'tcx>>,
}

impl<'tcx> Assembler<'tcx> {
    /// The post-order DFS: the slot of `instance`, assembling it (and, first, every callee it
    /// splices) on a miss. Memoized; bounded by cycle detection and `tcx.recursion_limit()`, not
    /// by the MIR inventory (which the MIR inliner can shrink at -O).
    fn slot_for(
        &mut self,
        tcx: TyCtxt<'tcx>,
        instance: ty::Instance<'tcx>,
        depth: usize,
    ) -> Result<FuncId, SlotRefusal> {
        match self.slots.get(&instance) {
            Some(Slot::Done(id) | Slot::Upstream { id, .. }) => return Ok(*id),
            Some(Slot::Refused(refusal)) => return Err(refusal.clone()),
            Some(Slot::InProgress) => {
                return Err(assembly(format!(
                    "instance cycle: `{}` is already being assembled; recursion needs real call \
                     edges (increment 5)",
                    tcx.symbol_name(instance).name
                )));
            }
            None => {}
        }
        let result = self.assemble(tcx, instance, depth);
        let slot = match &result {
            Ok(CompletedSlot::Local(id)) => Slot::Done(*id),
            Ok(CompletedSlot::Upstream { id, disclosure }) => {
                Slot::Upstream { id: *id, disclosure: *disclosure }
            }
            Err(refusal) => Slot::Refused(refusal.clone()),
        };
        self.slots.insert(instance, slot);
        result.map(|completed| completed.id())
    }

    fn assemble(
        &mut self,
        tcx: TyCtxt<'tcx>,
        instance: ty::Instance<'tcx>,
        depth: usize,
    ) -> Result<CompletedSlot, SlotRefusal> {
        let symbol = tcx.symbol_name(instance).name.to_string();
        if !tcx.recursion_limit().value_within_limit(depth) {
            return Err(assembly(format!(
                "`{symbol}` is nested deeper than the recursion limit on the instance lane"
            )));
        }
        let ty::InstanceKind::Item(def_id) = instance.def else {
            return Err(assembly(format!(
                "`{symbol}` is a compiler-synthesized instance ({:?}); the instance lane splices \
                 only plain items",
                instance.def
            )));
        };
        if !def_id.is_local() {
            return self.assemble_upstream(tcx, instance, &symbol, depth);
        }
        if tcx.is_foreign_item(def_id) {
            return Err(assembly(format!(
                "`{symbol}` is a foreign declaration with no body anywhere in this crate; calling \
                 it needs real call edges (increment 5)"
            )));
        }
        // Trust: the three synthetic closure arguments are its kind, signature
        // and captures, not substitutions for a generic parent. An authenticated
        // concrete source closure stays in the original module, including its
        // observed tables and real call edges; it is never appended/re-lowered.
        if let Some(selected) = source_closure_handoff(tcx, instance, &symbol)? {
            if !Arc::ptr_eq(&selected.module, &self.base) {
                return Err(assembly(format!(
                    "source closure `{symbol}` came from another handoff module"
                )));
            }
            return Ok(CompletedSlot::Local(selected.func_id));
        }
        let def_kind = tcx.def_kind(def_id);
        if !matches!(def_kind, rustc_hir::def::DefKind::Fn | rustc_hir::def::DefKind::AssocFn) {
            return Err(assembly(format!(
                "`{symbol}` is a {def_kind:?}; the instance lane splices only fn and associated-fn \
                 items; source FnOnce closures require the exact typed source handoff checked above"
            )));
        }
        let monomorphic = instance.args.iter().all(|arg| arg.as_region().is_some());
        if !monomorphic {
            // D17 admits a GENERIC body on structural admission PLUS the strict output gate; with
            // the gate relaxed, neither leg of the evidence would hold for it.
            if !self.strict_gate {
                return Err(assembly(format!(
                    "`{symbol}` is a generic instance body; owner ruling D17 admits one only under \
                     the STRICT proven-output gate, and this compilation's output-gate policy is \
                     not strict (-Ztrust-cg-output-gate)"
                )));
            }
            self.slots.insert(instance, Slot::InProgress);
            let (guest, edges) = self.lower_and_map(tcx, instance, &symbol, depth)?;
            let id = append_instance_body(None,
                &mut self.star,
                guest.module(),
                guest.callees().len(),
                guest.fn_pointer_free(),
                &edges,
            )
            .map_err(|why| assembly(format!("`{symbol}`: {why}")))?;
            let disclosure = if guest.mir_seam_compared() {
                Spliced::AppendedMirCompared
            } else {
                Spliced::Appended
            };
            self.spliced.push((symbol, id, disclosure));
            return Ok(CompletedSlot::Local(id));
        }

        // MONOMORPHIC: never lowered into code on this lane. No handoff body — finalize vetoed
        // or never spliced it — is a refusal, so finalize's vetoes bind on callees too.
        let selected = tcx
            .sess
            .with_trust_compiler_state::<trust_thir_lower::AssembledCrateModuleForCodegen, _>(
                |handoff| handoff.exact_instance_body(tcx, instance),
            )
            .map_err(|error| {
                assembly(format!(
                    "monomorphic callee `{symbol}` has no assembled handoff body ({error:?}); a \
                     body finalize did not splice is never re-lowered on the instance lane"
                ))
            })?;
        if !Arc::ptr_eq(&selected.module, &self.base) {
            return Err(assembly(format!(
                "the handoff answered `{symbol}` from a module other than the assembled one"
            )));
        }
        let slot = selected.func_id;
        if reaches_clean_body(&self.base, slot) {
            return Err(assembly(format!(
                "monomorphic callee `{symbol}` reaches a Clean-origin body, which is not admitted \
                 to codegen"
            )));
        }
        if !reaches_declaration(&self.base, slot) && is_leaf(&self.base, slot) {
            // A LEAF handoff body is linked as it is, tables native to the module; its own drops
            // and any `undef` placeholder in it are checked here because nothing re-lowers it.
            // An opaque collapse that leaves no `undef` is invisible here: the handoff does not
            // carry `opaque_collapse` (the module header, "INHERITED"). A non-leaf is relinked
            // below, which checks every body it reaches in turn.
            trust_thir_lower::instance_admission::instance_drop_refusal(tcx, instance).map_err(
                |refusal| assembly(format!("monomorphic leaf callee `{symbol}`: {refusal:?}")),
            )?;
            // Trust (2026-10-01, the instance lane's placeholder gate): fail-closed on a body the
            // handoff answered without one.
            let leaf_has_undef = self.base.function_by_id(slot).is_none_or(|leaf| {
                trust_thir_lower::instance_admission::function_has_undef_placeholder(leaf)
            });
            if leaf_has_undef {
                return Err(assembly(format!(
                    "monomorphic leaf callee `{symbol}`: LaneRefused(\"undef placeholder\")"
                )));
            }
            return Ok(CompletedSlot::Local(slot));
        }
        self.slots.insert(instance, Slot::InProgress);
        let (guest, edges) = self.lower_and_map(tcx, instance, &symbol, depth)?;
        let resolved: BTreeMap<FuncId, ty::Instance<'tcx>> = guest
            .callees()
            .iter()
            .filter_map(|callee| callee.instance().map(|target| (callee.func_id(), target)))
            .collect();
        let decl_names_edge = |name: &str, guest_callee: FuncId| -> Result<(), String> {
            let Some(&target) = resolved.get(&guest_callee) else {
                return Err("the guest edge resolved to no instance".to_string());
            };
            trust_thir_lower::instance_admission::declaration_names_instance(tcx, name, target)
        };
        relink_monomorphic_body(
            &mut self.star,
            slot,
            guest.module(),
            guest.callees().len(),
            guest.fn_pointer_free(),
            &edges,
            &decl_names_edge,
        )
        .map_err(|why| assembly(format!("`{symbol}`: {why}")))?;
        self.spliced.push((symbol, slot, Spliced::Relinked));
        Ok(CompletedSlot::Local(slot))
    }

    /// D39/D40 upstream input, through the same appender and all existing edge/postconditions.
    fn assemble_upstream(
        &mut self,
        tcx: TyCtxt<'tcx>,
        instance: ty::Instance<'tcx>,
        symbol: &str,
        depth: usize,
    ) -> Result<CompletedSlot, SlotRefusal> {
        self.slots.insert(instance, Slot::InProgress);
        let guest = upstream_entry::admit(tcx, instance).map_err(|refusal| SlotRefusal {
            detail: format!("upstream `{symbol}`: {refusal}"),
            producer: None,
            upstream: Some(refusal),
        })?;
        token_names(guest.admitted().instance(), instance)
            .map_err(|e| assembly(format!("upstream `{symbol}`: {e}")))?;
        function_is_named(guest.module(), FuncId::new(0), symbol)
            .map_err(|e| assembly(format!("upstream body: {e}")))?;
        let mut edges = BTreeMap::new();
        for (position, callee) in guest.callees().iter().enumerate() {
            let id = FuncId::new(position as u32 + 1);
            let target = callee.instance();
            if callee.id() != id || target == instance {
                return Err(assembly(format!(
                    "upstream `{symbol}` has a non-dense or recursive edge"
                )));
            }
            if !target.def_id().is_local() && !tcx.should_codegen_locally(target) {
                return Err(assembly(format!(
                    "upstream `{symbol}` calls a linked external instance `{}`; linked-slot admission (5.6) is still required",
                    tcx.symbol_name(target).name
                )));
            }
            function_is_named(guest.module(), id, tcx.symbol_name(target).name)
                .map_err(|e| assembly(format!("upstream declaration: {e}")))?;
            let target_id = self
                .slot_for(tcx, target, depth + 1)
                .map_err(|e| callee_refusal(e, symbol, tcx.symbol_name(target).name))?;
            edges.insert(id, target_id);
        }
        let binding = declaration_binding::bind_upstream(tcx, &self.base, &self.star, &guest)
            .map_err(|e| assembly(format!("upstream `{symbol}` declaration binding: {e}")))?;
        let id = append_instance_body(binding.as_ref(),
            &mut self.star,
            guest.module(),
            guest.callees().len(),
            guest.fn_pointer_free(),
            &edges,
        )
        .map_err(|e| assembly(format!("upstream `{symbol}`: {e}")))?;
        let disclosure = guest.disclosure();
        let installed_image = self.star.function_by_id(id)
            .cloned().ok_or_else(|| assembly("installed upstream body vanished".into()))?;
        let installed_signature = self.star.func_type(installed_image.ty)
            .cloned().ok_or_else(|| assembly("installed upstream signature vanished".into()))?;
        self.upstream_inputs.push(UpstreamAssemblyInput {
            installed: id, declaration_binding: binding, input: guest, edges,
            installed_image, installed_signature,
        });
        self.spliced.push((symbol.into(), id, Spliced::UpstreamEntry(disclosure)));
        Ok(CompletedSlot::Upstream { id, disclosure })
    }

    /// Lower `instance` on the instance-keyed producer and resolve each of its callee edges to a
    /// slot. A self edge or an unresolved edge refuses; a refused callee refuses its caller.
    fn lower_and_map(
        &mut self,
        tcx: TyCtxt<'tcx>,
        instance: ty::Instance<'tcx>,
        symbol: &str,
        depth: usize,
    ) -> Result<(trust_thir_lower::InstanceBody<'tcx>, BTreeMap<FuncId, FuncId>), SlotRefusal> {
        let guest =
            trust_thir_lower::trust_ir_of_instance_body(tcx, instance).map_err(|refusal| {
                SlotRefusal {
                    detail: format!("producer refused `{symbol}`: {refusal:?}"),
                    producer: Some(refusal),
                    upstream: None,
                }
            })?;
        // REQUIRED: the frozen admission's token, for THIS instance. A body exists only through
        // `instance_admission::admit_instance_body`, is read-only after it, and the token says
        // which instance its gate admitted.
        token_names(guest.admitted().instance(), instance)
            .map_err(|why| assembly(format!("`{symbol}`: {why}")))?;
        // CONTENT, on BOTH the append and the relink path: the body is named by this instance's
        // link-time symbol, and each declaration `FuncId(k)` by the symbol of the instance
        // `callees[k - 1]` stands for, in dense order.
        let module = guest.module();
        function_is_named(module, FuncId::new(0), symbol)
            .map_err(|why| assembly(format!("`{symbol}`'s body: {why}")))?;
        let mut edges = BTreeMap::new();
        for (position, callee) in guest.callees().iter().enumerate() {
            let k = FuncId::new(position as u32 + 1);
            if callee.func_id() != k {
                return Err(assembly(format!(
                    "`{symbol}`'s callee table is not dense: position {} holds FuncId({})",
                    k.index(),
                    callee.func_id().index()
                )));
            }
            let name = module.function_by_id(k).map_or_else(|| "?".to_string(), |f| f.name.clone());
            let Some(target) = callee.instance() else {
                return Err(assembly(format!(
                    "`{symbol}`'s edge FuncId({}) `{name}` is an unresolved callee (a closure or \
                     rust-call edge, a reified shim, dyn dispatch, or a havoc edge with no concrete \
                     key); there is no body to splice before real call edges (increment 5)",
                    k.index()
                )));
            };
            if target == instance {
                return Err(assembly(format!(
                    "`{symbol}` calls itself: recursion needs real call edges (increment 5)"
                )));
            }
            function_is_named(module, k, tcx.symbol_name(target).name)
                .map_err(|why| assembly(format!("`{symbol}`'s declaration: {why}")))?;
            let id = self
                .slot_for(tcx, target, depth + 1)
                .map_err(|refusal| callee_refusal(refusal, symbol, &name))?;
            edges.insert(k, id);
        }
        Ok((guest, edges))
    }
}

/// Where one reachable item's IR comes from.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum OriginChoice {
    Local,
    Upstream,
    Linked,
}

/// D40's locality decision; its inputs in plan() come only from actual Rust instance metadata.
pub(crate) fn origin_for(upstream: bool, codegen_locally: bool) -> OriginChoice {
    match (upstream, codegen_locally) {
        (false, _) => OriginChoice::Local,
        (true, true) => OriginChoice::Upstream,
        (true, false) => OriginChoice::Linked,
    }
}

enum ItemPlan {
    /// Refused before any lowering. `None` once [`Plan::source`] has handed the refusal out.
    Refused(Option<FrontendRefusal>),
    /// The unmodified finalize-assembled module, exactly as before this increment.
    Handoff(trust_thir_lower::ExactAssembledBodyForCodegen),
    /// The instance-keyed codegen module `star`.
    Instance,
}

/// The lanes of one codegen unit's inventory, decided once before any item is lowered, plus the
/// instance-keyed codegen module the instance-lane items lower from.
pub(crate) struct Plan<'tcx> {
    items: Vec<ItemPlan>,
    instances: Vec<ty::Instance<'tcx>>,
    /// Built only if some item takes the instance lane; otherwise every item lowers exactly as
    /// before this increment and the output is byte-identical.
    assembler: Option<Assembler<'tcx>>,
    /// Set when the whole-module checks on `star` failed: every instance-lane item is refused
    /// with it, and `star` is never lowered from.
    star_refused: Option<String>,
}

impl<'tcx> Plan<'tcx> {
    /// The module and function item `index` lowers from, or its refusal. Bound to the INSTANCE,
    /// not the index alone: the caller names what it is lowering, and a plan that holds another
    /// instance at `index` refuses.
    pub(crate) fn source(
        &mut self,
        index: usize,
        instance: ty::Instance<'tcx>,
        symbol: &str,
    ) -> Result<(&Module, FuncId), FrontendRefusal> {
        let refused = |detail: String| FrontendRefusal::InstanceAssembly {
            symbol: symbol.to_string(),
            detail,
        };
        match self.instances.get(index) {
            Some(planned) if *planned == instance => {}
            planned => {
                return Err(refused(format!(
                    "internal: planned {planned:?} at {index}, asked for {instance:?}"
                )));
            }
        }
        let instance = Some(instance);
        match self.items.get_mut(index) {
            None => Err(refused("internal: this item was not planned".to_string())),
            Some(ItemPlan::Refused(refusal)) => Err(refusal
                .take()
                .unwrap_or_else(|| refused("internal: refusal handed out twice".to_string()))),
            Some(ItemPlan::Handoff(selected)) => Ok((&*selected.module, selected.func_id)),
            Some(ItemPlan::Instance) => {
                if let Some(detail) = &self.star_refused {
                    return Err(refused(detail.clone()));
                }
                let (Some(assembler), Some(instance)) = (self.assembler.as_ref(), instance) else {
                    return Err(refused("internal: no instance-keyed module".to_string()));
                };
                match assembler.slots.get(&instance) {
                    Some(Slot::Done(id) | Slot::Upstream { id, .. }) => Ok((&assembler.star, *id)),
                    Some(Slot::Refused(SlotRefusal {
                        producer: Some(refusal), detail, ..
                    })) => Err(FrontendRefusal::InstanceProducerRefused {
                        symbol: symbol.to_string(),
                        reason: detail.clone(),
                        refusal: refusal.clone(),
                    }),
                    Some(Slot::Refused(SlotRefusal { upstream: Some(refusal), .. })) => {
                        Err(refusal.frontend(symbol))
                    }
                    Some(Slot::Refused(refusal)) => Err(refused(refusal.detail.clone())),
                    Some(Slot::InProgress) | None => {
                        Err(refused("internal: slot left unassembled".to_string()))
                    }
                }
            }
        }
    }

    /// The bodies the instance lane spliced into the codegen module, in splice order: the input of
    /// the per-function DISCLOSURE (D17), which the frontend prints — and writes to the coverage
    /// artifact — only for bodies that reach EMITTED code, after the gate. Empty when no module was
    /// built or its whole-module checks refused it.
    pub(crate) fn spliced(&self) -> Vec<(String, FuncId, Spliced)> {
        match (&self.assembler, &self.star_refused) {
            (Some(assembler), None) => assembler.spliced.clone(),
            _ => Vec::new(),
        }
    }

    /// The instance-keyed codegen module, when one was built and survived its whole-module checks.
    pub(crate) fn instance_module(&self) -> Option<&Module> {
        match (&self.assembler, &self.star_refused) {
            (Some(assembler), None) => Some(&assembler.star),
            _ => None,
        }
    }

    /// Project private installation witnesses only from a successfully checked
    /// assembler. Every reference for an entry comes from that same retained
    /// upstream input; callers cannot choose or replace any of its premises.
    pub(crate) fn handoff_declaration_extensions(&self) -> Option<HandoffDeclarationExtensions<'_>> {
        let (Some(assembler), None) = (&self.assembler, &self.star_refused) else {
            return None;
        };
        let installations = assembler.upstream_inputs.iter().filter_map(|entry| {
            Some(RetainedDeclarationInstallation {
                binding: entry.declaration_binding.as_ref()?,
                original: entry.input.original_module(),
                guest: entry.input.module(),
                evidence: entry.input.retained_evidence(),
                installed: entry.installed,
                image: &entry.installed_image,
                signature: &entry.installed_signature,
                edges: &entry.edges,
            })
        }).collect::<Vec<_>>();
        if installations.is_empty() {
            return None;
        }
        Some(HandoffDeclarationExtensions {
            base: &assembler.base,
            star: &assembler.star,
            installations,
        })
    }

    /// Whether item `index` lowers from the instance-keyed codegen module.
    pub(crate) fn is_instance_item(&self, index: usize) -> bool {
        matches!(self.items.get(index), Some(ItemPlan::Instance))
    }
}

/// Decide the lane of every reachable item and, if any takes the instance lane, assemble the
/// instance-keyed codegen module.
///
/// `instances` is the production inventory (`collect_production_mono_instances`), unchanged and
/// in order; the returned plan is index-aligned with it. Whether the output-gate policy is the
/// strict one — D17's condition for appending a generic body — is read from the session here.
pub(crate) fn plan<'tcx>(
    tcx: TyCtxt<'tcx>,
    instances: &[(String, ty::Instance<'tcx>, bridge_backend::FunctionLinkage)],
) -> Plan<'tcx> {
    let mut items = Vec::with_capacity(instances.len());
    let mut any_instance = false;
    for (_, instance, _) in instances {
        let instance = *instance;
        let symbol = tcx.symbol_name(instance).name.to_string();
        let upstream = matches!(instance.def, ty::InstanceKind::Item(def) if !def.is_local());
        let origin = origin_for(upstream, !upstream || tcx.should_codegen_locally(instance));
        let item = if origin == OriginChoice::Upstream {
            ItemPlan::Instance
        } else if origin == OriginChoice::Linked {
            ItemPlan::Refused(Some(FrontendRefusal::UpstreamEntry {
                symbol: symbol.clone(), check: "locality",
                detail: "Rustc links this upstream instance externally; it is never imported as a local copy".into(),
            }))
        } else {
            match local_body_def(tcx, instance, &symbol, GenericPolicy::AdmitConcrete) {
            Err(refusal) => ItemPlan::Refused(Some(refusal)),
            Ok(_) if tcx.def_kind(instance.def_id()) == rustc_hir::def::DefKind::Closure => {
                match source_closure_handoff(tcx, instance, &symbol) {
                    Ok(Some(selected)) => ItemPlan::Handoff(selected),
                    Ok(None) => ItemPlan::Refused(Some(FrontendRefusal::InstanceAssembly {
                        symbol,
                        detail: "source closure route did not classify this item".into(),
                    })),
                    Err(refusal) => ItemPlan::Refused(Some(FrontendRefusal::InstanceAssembly {
                        symbol,
                        detail: refusal.detail,
                    })),
                }
            }
            Ok(_) if !instance.args.iter().all(|arg| arg.as_region().is_some()) => {
                ItemPlan::Instance
            }
            Ok(_) => match tcx
                .sess
                .with_trust_compiler_state::<trust_thir_lower::AssembledCrateModuleForCodegen, _>(
                    |handoff| handoff.exact_instance_body(tcx, instance),
                ) {
                Ok(selected) => {
                    let module = &*selected.module;
                    match lane_for(
                        false,
                        reaches_declaration(module, selected.func_id)
                            && !(tcx.sess.trust_cg_f1_backend_is_compiler()
                                && reaches_only_recorded_foreign_declarations(module, selected.func_id)),
                        reaches_clean_body(module, selected.func_id),
                    ) {
                        LaneChoice::Instance => ItemPlan::Instance,
                        LaneChoice::Handoff => ItemPlan::Handoff(selected),
                    }
                }
                Err(trust_thir_lower::AssembledBodyLookupError::HandoffUnavailable) => {
                    ItemPlan::Refused(Some(FrontendRefusal::AssembledHandoffUnavailable { symbol }))
                }
                Err(trust_thir_lower::AssembledBodyLookupError::ExactBodyAbsent {
                    def_index,
                    definition,
                }) => ItemPlan::Refused(Some(FrontendRefusal::ExactAssembledBodyAbsent {
                    symbol,
                    def_index,
                    definition,
                })),
                Err(trust_thir_lower::AssembledBodyLookupError::NotMonomorphicLocalItem {
                    instance,
                }) => ItemPlan::Refused(Some(FrontendRefusal::InstanceAssembly {
                    symbol,
                    detail: format!("the handoff does not key `{instance}` as a monomorphic item"),
                })),
                // Trust (effect conservation, D28): the handoff hands out only bodies the
                // effect-conservation check judged conserved; a withdrawn body, or a handoff the
                // check never ran over, is refused here exactly as on the handoff lane.
                Err(trust_thir_lower::AssembledBodyLookupError::ConservationUnchecked {
                    def_index,
                }) => ItemPlan::Refused(Some(FrontendRefusal::EffectNotConserved {
                    symbol,
                    detail: format!(
                        "DefIndex({def_index}): the effect-conservation check never ran over the \
                         assembled handoff, so no body in it is known to be the program"
                    ),
                })),
                Err(trust_thir_lower::AssembledBodyLookupError::NotConserved {
                    def_index,
                    func_id,
                    tags,
                }) => ItemPlan::Refused(Some(FrontendRefusal::EffectNotConserved {
                    symbol,
                    detail: format!("DefIndex({def_index}), FuncId({func_id}): {tags}"),
                })),
            },
        }
        };
        any_instance |= matches!(item, ItemPlan::Instance);
        items.push(item);
    }
    let instances: Vec<ty::Instance<'tcx>> = instances.iter().map(|(_, i, _)| *i).collect();
    if !any_instance {
        return Plan { items, instances, assembler: None, star_refused: None };
    }

    let base = match tcx
        .sess
        .with_trust_compiler_state::<trust_thir_lower::AssembledCrateModuleForCodegen, _>(
            |handoff| handoff.assembled_module(),
        ) {
        Ok(base) => base,
        Err(_) => {
            for (item, instance) in items.iter_mut().zip(&instances) {
                if matches!(item, ItemPlan::Instance) {
                    let symbol = tcx.symbol_name(*instance).name.to_string();
                    *item = ItemPlan::Refused(Some(FrontendRefusal::AssembledHandoffUnavailable {
                        symbol,
                    }));
                }
            }
            return Plan { items, instances, assembler: None, star_refused: None };
        }
    };
    let mut assembler = Assembler {
        star: (*base).clone(),
        base,
        slots: FxHashMap::default(),
        spliced: Vec::new(),
        strict_gate: session_gate_is_strict(tcx.sess),
        upstream_inputs: Vec::new(),
    };
    for (item, instance) in items.iter().zip(&instances) {
        if matches!(item, ItemPlan::Instance) {
            // The outcome is recorded in the slot; `Plan::source` reads it per item.
            let _ = assembler.slot_for(tcx, *instance, 0);
        }
    }

    // The whole-module checks, only if something entered `star`: every gate source must share
    // one table image, the result must pass the validator the base passed at finalization, and
    // no body may be left without a claim.
    let mut star_refused = None;
    if !assembler.spliced.is_empty() {
        if let Err(why) = tables_unchanged(&assembler.base, &assembler.star) {
            star_refused = Some(why);
        } else {
            let errors = trust_thir_lower::instance_admission::assembled_codegen_validation_errors(
                &assembler.star,
            );
            if let Some(first) = errors.first() {
                star_refused = Some(format!(
                    "the instance-keyed codegen module fails the finalize validator ({} \
                     error(s)): {first}",
                    errors.len()
                ));
            } else if let Err(why) = body_gates_are_stamped(&assembler.star) {
                star_refused = Some(why);
            }
        }
        if star_refused.is_none() {
            for retained in &assembler.upstream_inputs {
                if let Err(why) = retained.check(&assembler.base, &assembler.star) {
                    star_refused = Some(why);
                    break;
                }
            }
        }
    }
    if star_refused.is_some() {
        // Dropped: nothing is ever lowered from a module that failed these checks.
        assembler.star = Module::new(assembler.base.name.clone());
    }
    Plan { items, instances, assembler: Some(assembler), star_refused }
}

#[cfg(test)]
mod tests;
