//! Trust (step 2 increment 3 of `docs/plans/2026-09-29-trust-ir-sole-compile-path.md`, owner
//! ruling D17): the INSTANCE LANE's ADMISSION — the whole THIR route of the instance-keyed
//! producer, from its entry refusals to the self-contained, validated module the codegen-time
//! assembler (`compiler/rustc_codegen_trust_cg/src/trust_ir_frontend/instance_assembly.rs`) may
//! splice.
//!
//! # Why this file is FROZEN
//!
//! Ordinary D17 admission is structural. The explicit diagnostic test-oracle is additional;
//! it grants no authority and never supplies production IR. The ordinary path has no differential: the oracle that
//! judges the producer's output everywhere else does not judge it here. The frozen assembler
//! DELEGATES admission to this file and does not re-derive it, so under the manifest's delegate
//! rule (`scripts/frozen-files.txt`, "a frozen gate delegates its decision to it and does not
//! re-derive the answer") this file is frozen with it, BYTE-IDENTICAL.
//!
//! The delegation is enforced by TYPE. An [`InstanceBody`] carries an [`Admitted`] token; only
//! [`mono_thir_result_admits`] mints one, over [`MonoLoweringFacts`] that only [`lowering_facts`]
//! builds, and all three are private to this file. Every field of [`InstanceBody`] and
//! [`InstanceCallee`] is private too, with shared-reference accessors only, so no code between
//! this route and the assembler (`lib.rs`'s dispatch, which passes the body by value) can rewrite
//! the module, the callee table or the flags after the gate; the one consuming accessor,
//! [`InstanceBody::into_module`], is for measurement and drops the token. So the one way to hand
//! the assembler a body is [`admit_instance_body`], which runs every leg below in order; the
//! assembler refuses a body whose token names another instance, and re-checks that the body and
//! every declaration are named by the link-time symbol of the instance they stand for.
//!
//! What this file decides:
//!
//! * the ORCHESTRATION ([`admit_instance_body`]): the entry refusals, the THIR fetch, the lowering
//!   on a fail-closed lane, the facts, the gate, the symbol and calling-convention stamps, the
//!   callee declarations, the standalone validation and fn-pointer freedom, in that order;
//! * the lane channel ([`MonoLane`]): only this file makes one; it starts UNREPORTED, and an
//!   unreported lane reads as a residual parameter, so a lowering that never reports its
//!   tripwires is refused;
//! * [`mono_thir_result_admits`], in full, over facts read from an EXHAUSTIVE destructure of
//!   `Lowered`, from the lane's report, and from the elided-drop predicate: coverage, the
//!   monomorphization tripwires, the pending-const sentinel, every placeholder lane — including
//!   the tag-free OPAQUE COLLAPSE (`Lowered::opaque_collapse`) and any `undef` the body module
//!   holds ([`function_has_undef_placeholder`]), the two abstraction lanes that can store
//!   nothing, only a discriminant, or `undef` where the program stores a value
//!   (docs/KNOWN_HAZARDS.md, OPEN 2026-10-01, abstraction lanes) — the elided-drop leg and the
//!   stamp's one-function precondition. Every `Lowered` field is classified in
//!   [`lowering_facts`]: what can leave a placeholder for a real value GATES, and what is left
//!   unread says why it cannot. The GATE is frozen; the `Lowered` flags it reads are the
//!   lowering's own report (see the residuals below);
//! * the entry refusals ([`instance_entry`]), the elided-drop predicate
//!   ([`thir_instance_needs_drop`]), the leaf-callee drop check ([`instance_drop_refusal`]) and
//!   the `undef` scan ([`function_has_undef_placeholder`]) the assembler also runs on a leaf;
//! * WHICH INSTANCE EACH CALLEE EDGE NAMES: the producer's `(def, args)` for an edge is recorded
//!   with the RAW call SITE it came from (the THIR callee operand, not instantiated at the lane's
//!   args; [`record_callee_instance`], called from `LowerCx::admit_concrete_callee_site`), every
//!   distinct record kept; [`append_instance_callee_declarations`] RE-DERIVES each `Item` record
//!   from its site ([`resolve_site`]: instantiated at the instance's args, normalized at
//!   `fully_monomorphized()`, resolved with `Instance::try_resolve` as codegen resolves a callee
//!   operand) and refuses the body when a site resolves elsewhere, to a non-item (an intrinsic),
//!   or when two records of one edge disagree ([`decide_edge`]); it then names and signs the
//!   declarations ([`declaration_func_ty`]);
//! * the self-contained check and the standalone validation ([`validate_instance_module`]),
//!   fn-pointer freedom ([`instance_body_is_fn_pointer_free`]), and the finalize validator the
//!   assembler runs on the module it extends ([`assembled_codegen_validation_errors`]);
//! * the identity of an analysis-time declaration ([`declaration_names_instance`]): the
//!   definition always, and the instance whenever the name carries a concrete key.
//!
//! What it does NOT cover — the unfrozen inputs, each listed as a residual in
//! `scripts/frozen-files.txt` with the test that exercises it and the lane that runs it: the
//! LOWERING itself (`lower_module_inner` and everything under it: the producer under test),
//! including the flags it reports in `Lowered` (`unsupported`, `pending_consts`, `symbolic`,
//! `opaque_collapse`, the union and enum-param lanes, `fnptr_adapter`, `place_path_carrier`,
//! `zst_closure_arg`, `coroutine_frame_ptr`, `body_kind` — under D17 no oracle checks them), the
//! tripwire values it reports, and the call SITES it records; trust-ir's `function_dependencies`
//! census, which the self-contained check and fn-pointer freedom read (gitlink-pinned, not
//! frozen); `crate::encode_site_args`, which [`declaration_names_instance`] uses to recompute a
//! concrete key; the handoff's own leaf selection (`AssembledCrateModuleForCodegen::
//! exact_instance_body`); and the dispatch in `lib.rs` (`trust_ir_of_instance_body`), which can
//! refuse but cannot build or change a body.
//!
//! INHERITED, not decided here: a monomorphic LEAF callee is linked as its analysis-time HANDOFF
//! body, never re-lowered, so this file sees neither its `Lowered` flags nor its lowering. Its
//! drops are checked ([`instance_drop_refusal`]) and so is any `undef` in it (the assembler runs
//! [`function_has_undef_placeholder`] on the linked body), but an OPAQUE COLLAPSE that leaves no
//! `undef` (the opaque `()` lane storing nothing; the `Option`-discriminant lane storing only a
//! discriminant) is invisible: the handoff does not carry `opaque_collapse` (the frozen
//! `crate_module.rs` discards it), so such a leaf is linked with the handoff lane's own hazard,
//! docs/KNOWN_HAZARDS.md, OPEN 2026-10-01, abstraction lanes. A RELINKED (non-leaf) monomorphic
//! callee is not exposed: its guest is re-lowered through [`admit_instance_body`], so it passes
//! this gate, and the assembler requires the handoff body to equal it.
//!
//! Its tests live in `instance_admission/tests.rs` and are not frozen.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use rustc_middle::thir::Thir;
use rustc_middle::ty::{self, TyCtxt, TypeVisitableExt};
use rustc_span::def_id::{DefId, LocalDefId};
use trust_ir::value::{BlockId, FuncId};
use trust_ir::{Function, Inst, Linkage, Ty};

use crate::{BodyKind, CalleeRef, InstanceInput, InstanceRefusal, Lowered, ParamSignature};

// ===========================================================================
// What the assembler receives
// ===========================================================================

/// Evidence, by type, that [`mono_thir_result_admits`] admitted the lowering of one instance.
/// Its field is private to this file and only the gate mints one; the assembler checks that the
/// token names the instance it asked for. The token binds the INSTANCE; the CONTENT is bound by
/// [`InstanceBody`] having no public field and no `&mut` accessor — what the frozen route built is
/// what the assembler reads.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Admitted<'tcx> {
    instance: ty::Instance<'tcx>,
}

impl<'tcx> Admitted<'tcx> {
    /// The instance the gate admitted.
    pub fn instance(&self) -> ty::Instance<'tcx> {
        self.instance
    }
}

/// Step 2 increment 3: one instance's SELF-CONTAINED module, as the codegen-time assembler
/// consumes it. Built ONLY by [`admit_instance_body`], and READ-ONLY after it: every field is
/// private to this file, the accessors return shared references, and the one consuming accessor
/// ([`InstanceBody::into_module`], for measurement) drops the token. So no code between the frozen
/// route and the frozen assembler — `lib.rs`'s dispatch — can rewrite the module, the callee
/// table or the flags the route computed.
///
/// `module` holds the instance body at `FuncId(0)`, named by `tcx.symbol_name(instance)`, and
/// one bodyless, SIGNED declaration at each `FuncId(k)`, `1 <= k <= n`, for the callee the body
/// names there, named by `tcx.symbol_name` of the instance `callees[k - 1]` stands for.
pub struct InstanceBody<'tcx> {
    module: trust_ir::Module,
    input: InstanceInput,
    callees: Vec<InstanceCallee<'tcx>>,
    /// Derived from the dependency census, never from the table sizes: no `FunctionType` edge
    /// other than each function's own signature row, and no instruction-site function edge other
    /// than a direct call. See [`instance_body_is_fn_pointer_free`].
    fn_pointer_free: bool,
    /// `Lowered::opaque_collapse` of the lowering, as the gate read it. The gate refuses a body
    /// that sets it, so it is `false` for every body that exists; it is carried so a measurement
    /// reports the route's own fact rather than an assumption about the gate.
    opaque_collapse: bool,
    admitted: Admitted<'tcx>,
    /// A diagnostic measurement, minted only by the explicit test-oracle comparison.
    mir_seam_compared: bool,
}

impl<'tcx> InstanceBody<'tcx> {
    /// The self-contained instance module.
    pub fn module(&self) -> &trust_ir::Module {
        &self.module
    }

    /// Which producer input the module was lowered from.
    pub fn input(&self) -> InstanceInput {
        self.input
    }

    /// What each callee declaration `FuncId(k)` stands for, `k = 1..=n`, in order.
    pub fn callees(&self) -> &[InstanceCallee<'tcx>] {
        &self.callees
    }

    /// See [`instance_body_is_fn_pointer_free`].
    pub fn fn_pointer_free(&self) -> bool {
        self.fn_pointer_free
    }

    /// The gate's token for this body.
    pub fn admitted(&self) -> Admitted<'tcx> {
        self.admitted
    }

    /// Whether the lowering took a tag-free opaque collapse. Always `false`: the gate refuses
    /// such a body ([`InstanceRefusal::LaneRefused`]`("opaque collapse")`). For measurement
    /// (probe channel C), which reports the route's own fact.
    pub fn opaque_collapse(&self) -> bool {
        self.opaque_collapse
    }

    /// Whether the exact source-produced lowering passed the explicit per-instance MIR
    /// TEST-ORACLE. This is measurement only; the structural token and proof grades are unchanged.
    pub fn mir_seam_compared(&self) -> bool {
        self.mir_seam_compared
    }

    /// The module and its input, for MEASUREMENT (`trust_ir_of_instance_explained`, the census).
    /// Consumes the body and DROPS the token, so what comes out can never be handed to the
    /// assembler again.
    pub fn into_module(self) -> (trust_ir::Module, InstanceInput) {
        (self.module, self.input)
    }
}

/// Step 2 increment 3: what one callee declaration of an [`InstanceBody`] stands for. Built only
/// by [`append_instance_callee_declarations`]; read-only.
pub struct InstanceCallee<'tcx> {
    func_id: FuncId,
    instance: Option<ty::Instance<'tcx>>,
}

impl<'tcx> InstanceCallee<'tcx> {
    /// The declaration's id in the instance module, `1..=n`.
    pub fn func_id(&self) -> FuncId {
        self.func_id
    }

    /// The concrete `InstanceKind::Item` the edge resolved to, re-derived from its call site at
    /// `TypingEnv::fully_monomorphized()`. `None` for an edge that is not a concretely keyed plain
    /// item: an `admit_havoc_callee` edge (no concrete key), a closure or rust-call edge, a
    /// reified shim, dyn dispatch. The assembler refuses those. A concretely keyed `Item` edge the
    /// analysis-time lowering forced BODYLESS (`force_havoc`: every generic callee, and a
    /// signature that is not instantiation-invariant) DOES resolve here: the instance lane links
    /// it to the callee's own instance-lowered body, guarded by the assembler's per-edge
    /// signature and calling-convention check.
    pub fn instance(&self) -> Option<ty::Instance<'tcx>> {
        self.instance
    }
}

// ===========================================================================
// The THIR route, whole
// ===========================================================================

/// THE THIR ROUTE of the instance-keyed producer: a LOCAL plain item body, lowered at
/// `instance.args`, admitted or refused. Every leg runs here, in this order, and the result is
/// the only way an [`InstanceBody`] comes to exist.
pub(crate) fn admit_instance_body<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: ty::Instance<'tcx>,
) -> Result<InstanceBody<'tcx>, InstanceRefusal> {
    let def = instance_entry(tcx, instance)?;
    let Ok((thir, root)) = tcx.thir_body(def) else {
        return Err(InstanceRefusal::ThirUnavailable);
    };
    if thir.is_stolen() {
        return Err(InstanceRefusal::ThirStolen);
    }
    let thir = thir.borrow();
    let mut lane = MonoLane::new(instance.args);
    // An instance lowering is not the mainline `mir_built` registrar, so it never registers
    // direct-obligation rows (the last argument; see `register_direct_obligations`).
    let lowered = crate::lower_module_inner(tcx, def, &thir, root, false, Some(&mut lane), false);
    let facts = lowering_facts(tcx, instance, &thir, &lowered, &lane);
    let admitted = mono_thir_result_admits(&facts)?;
    // The ordinary path returns without querying MIR. In the explicit diagnostic lane compare
    // this real lowering, not a hook-time generic lowering or a second source reconstruction.
    let mir_seam_compared = crate::instance_seam_test::compare(tcx, instance, &lowered)?;
    let Lowered { mut module, callees, .. } = lowered;
    let opaque_collapse = facts.opaque_collapse;
    stamp_instance_symbol(tcx, instance, &mut module)?;
    stamp_instance_calling_conv(tcx, def, &mut module)?;
    let callees = append_instance_callee_declarations(
        tcx,
        instance,
        &mut module,
        &callees,
        lane.callee_instances(),
    )?;
    validate_instance_module(tcx, &module, callees.len())?;
    let fn_pointer_free = instance_body_is_fn_pointer_free(&module);
    Ok(InstanceBody {
        module,
        input: InstanceInput::Thir,
        callees,
        fn_pointer_free,
        opaque_collapse,
        admitted,
        mir_seam_compared,
    })
}

/// GAP G1: stamp the LINK-TIME identity onto the body function.
///
/// Both routes name the body `FuncId::new(0)` from something that is only a LABEL — the THIR
/// route from `def_path_str`, the MIR route from the oracle's `func.name`. The object's symbol
/// table is not a label, so the mangled symbol is stamped here, which is exactly what the
/// trust-cg frontend's `lower_instance` keys on.
pub(crate) fn stamp_instance_symbol<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: ty::Instance<'tcx>,
    module: &mut trust_ir::Module,
) -> Result<(), InstanceRefusal> {
    let symbol = tcx.symbol_name(instance).name.to_string();
    let Some(function) = module.function_by_id_mut(FuncId::new(0)) else {
        return Err(InstanceRefusal::NoBodyFunction);
    };
    function.name = symbol;
    Ok(())
}

// ===========================================================================
// The lane channel
// ===========================================================================

/// GAP G1: the instance lane's in/out channel through `lower_module_inner`.
///
/// `args` goes IN (it becomes `LowerCx::mono_args`); the lowering's REPORT comes OUT — the two
/// monomorphization tripwires and the callee-instance records. The lane starts UNREPORTED and
/// only [`MonoLane::report`] sets the outputs, so a lowering that never reports (its report call
/// removed, or an early return) reads as a residual parameter and is refused, never as fully
/// monomorphized. Not `Lowered` fields on purpose: `crate_module::record` destructures `Lowered`
/// field-explicitly in a frozen file, and these are facts about the LANE, not about the body.
pub(crate) struct MonoLane<'tcx> {
    args: ty::GenericArgs<'tcx>,
    report: Option<LaneReport<'tcx>>,
}

struct LaneReport<'tcx> {
    residual: bool,
    param_arm_hits: u32,
    callee_instances: Vec<CalleeInstanceRecord<'tcx>>,
}

impl<'tcx> MonoLane<'tcx> {
    /// A lane at `args`, UNREPORTED (fail-closed). PRIVATE to this file: only the frozen route
    /// makes a lane, so no lowering can substitute one of its own.
    fn new(args: ty::GenericArgs<'tcx>) -> Self {
        MonoLane { args, report: None }
    }

    /// The instance args the lowering threads through the type mapper.
    pub(crate) fn args(&self) -> ty::GenericArgs<'tcx> {
        self.args
    }

    /// The lowering's report, made once at the end of `lower_module_inner`. A second report is a
    /// desync and arms the tripwire.
    pub(crate) fn report(
        &mut self,
        residual: bool,
        param_arm_hits: u32,
        callee_instances: Vec<CalleeInstanceRecord<'tcx>>,
    ) {
        let second = self.report.is_some();
        self.report =
            Some(LaneReport { residual: residual || second, param_arm_hits, callee_instances });
    }

    fn callee_instances(&self) -> &[CalleeInstanceRecord<'tcx>] {
        self.report.as_ref().map_or(&[], |report| &report.callee_instances)
    }
}

/// The lane's two tripwires as the gate reads them: `(residual, param_arm_hits)`. An UNREPORTED
/// lane is a residual. PURE.
fn lane_tripwires(lane: &MonoLane<'_>) -> (bool, u32) {
    match &lane.report {
        None => (true, 0),
        Some(report) => (report.residual, report.param_arm_hits),
    }
}

// ===========================================================================
// The post-lowering gate
// ===========================================================================

/// GAP G1: the facts the THIR route's post-lowering gate reads. Built only by [`lowering_facts`]
/// (no field is visible outside this file), so the gate cannot be fed a hand-made fact set.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct MonoLoweringFacts<'tcx> {
    /// The instance the facts are about; the token the gate mints names it.
    instance: ty::Instance<'tcx>,
    /// The class tag of `Lowered::unsupported`'s FIRST entry, or `None` when it is empty.
    /// Trust (fix10/core-refusals): the tag rides on the refusal so channel C names why the
    /// producer declined (634 of `core`'s 864 refused rows read a bare `ProducerDeclined`).
    first_unsupported: Option<&'static str>,
    /// `Lowered::symbolic`.
    symbolic: bool,
    /// `Lowered::opaque_collapse`: a LIVE value took a tag-free opaque placeholder (the
    /// `struct_ty_rmw_opaque` `()` sibling lane, the `Option`-discriminant `bool` lane, a wave-EL
    /// data-enum lane). Such a body can store nothing, or only a discriminant, where the program
    /// stores a value. MEASUREMENT ONLY on the handoff lane (its splice does not refuse it); it
    /// GATES here, because under D17 no seam differential judges an instance body.
    opaque_collapse: bool,
    /// The body module holds an `Inst::Undef` ([`function_has_undef_placeholder`]): an arbitrary
    /// value standing in for a real one (a whole-value store of a non-plain value, a variant test
    /// on an opaque value, a havoc'd local). GATES for the same reason.
    undef_placeholder: bool,
    /// How many times `map_ty`'s `ty::Param` arm fired. MUST be zero on this lane.
    param_arm_hits: u32,
    /// An instantiation left a residual parameter, a resolution-site param guard fired, a
    /// callee record desynced, or the lane was never reported.
    mono_residual: bool,
    /// `Lowered::union_lane`.
    union_lane: bool,
    /// `Lowered::enum_param_lane`.
    enum_param_lane: bool,
    /// `Lowered::fnptr_adapter`.
    fnptr_adapter: bool,
    /// `Lowered::pending_consts.len()`. Non-zero means the module still carries a
    /// finalizer-only const SENTINEL.
    pending_consts: usize,
    /// `Lowered::place_path_carrier`. STRICTER than `crate_module::splice_ok`, which has no leg
    /// for it (it only skips the seam differential for such a body).
    place_path_carrier: bool,
    /// `Lowered::zst_closure_arg` (`crate_module::splice_ok` refuses it too).
    zst_closure_arg: bool,
    /// `Lowered::coroutine_frame_ptr` (`crate_module::splice_ok` refuses it too).
    coroutine_frame_ptr: bool,
    /// `Lowered::body_kind != BodyKind::Fn`: a const/static INITIALIZER body is not a callable
    /// function body. STRICTER than `crate_module::splice_ok`, which splices initializer bodies.
    non_fn_body: bool,
    /// Until increment 4 lands (drops, faithfully): [`thir_instance_needs_drop`]. The producer
    /// elides implicit drops today, so such a body's module is not the instance's semantics.
    drop_bearing: bool,
    /// `Module::functions.len()` of the BODY-ONLY module, counted BEFORE the callee declarations
    /// are appended. The stamp convention (`stamp_instance_symbol` names `FuncId(0)`) needs
    /// exactly one function here.
    functions: usize,
}

/// GAP G1: the THIR route's POST-LOWERING gate, and the only minter of [`Admitted`].
///
/// Strictly stronger than `trust_ir_of`'s (which admits on `unsupported.is_empty()` alone and
/// leaves the placeholder-lane refusals to `crate_module::splice_ok`), and at least as strict as
/// the handoff's splice on every flag the splice reads: a pending-const SENTINEL is refused, and
/// so are the ZST closure/fn-item stand-in and the coroutine frame-pointer convention (which
/// `splice_ok` refuses too), the opaque collapse, an `undef` placeholder, the place-path carrier
/// and an initializer body (STRICTER than `splice_ok`), and, until increment 4, a body with an
/// elided drop. The order is the diagnosis:
/// coverage, then the lane's own tripwires, then the sentinel, then the placeholder lanes, then
/// drops, then the stamp's one-function precondition.
///
/// `param_arm_hits != 0` is the operational form of claim (b): if normalizing at
/// `fully_monomorphized()` really removes the `ty::Param` arm's precondition this never fires;
/// if it does, the answer is a refusal, not a `Ty::Unit` standing in for `T`.
fn mono_thir_result_admits<'tcx>(
    facts: &MonoLoweringFacts<'tcx>,
) -> Result<Admitted<'tcx>, InstanceRefusal> {
    if let Some(tag) = facts.first_unsupported {
        return Err(InstanceRefusal::ProducerDeclined(tag));
    }
    if facts.mono_residual || facts.param_arm_hits != 0 {
        return Err(InstanceRefusal::MonoIncomplete);
    }
    if facts.pending_consts != 0 {
        return Err(InstanceRefusal::PendingConsts);
    }
    if facts.symbolic {
        return Err(InstanceRefusal::LaneRefused("symbolic"));
    }
    if facts.opaque_collapse {
        return Err(InstanceRefusal::LaneRefused("opaque collapse"));
    }
    if facts.undef_placeholder {
        return Err(InstanceRefusal::LaneRefused("undef placeholder"));
    }
    if facts.union_lane {
        return Err(InstanceRefusal::LaneRefused("union lane"));
    }
    if facts.enum_param_lane {
        return Err(InstanceRefusal::LaneRefused("enum param lane"));
    }
    if facts.fnptr_adapter {
        return Err(InstanceRefusal::LaneRefused("fn-ptr adapter"));
    }
    if facts.place_path_carrier {
        return Err(InstanceRefusal::LaneRefused("place-path carrier"));
    }
    if facts.zst_closure_arg {
        return Err(InstanceRefusal::LaneRefused("zst closure arg"));
    }
    if facts.coroutine_frame_ptr {
        return Err(InstanceRefusal::LaneRefused("coroutine frame ptr"));
    }
    if facts.non_fn_body {
        return Err(InstanceRefusal::LaneRefused("initializer body"));
    }
    if facts.drop_bearing {
        return Err(InstanceRefusal::LaneRefused("drop-bearing"));
    }
    // Counts the BODY-ONLY module: the declarations are appended after the stamp, which is
    // exactly what this precondition protects.
    if facts.functions != 1 {
        return Err(InstanceRefusal::NoBodyFunction);
    }
    Ok(Admitted { instance: facts.instance })
}

/// The gate's facts: an EXHAUSTIVE destructure of `Lowered` — no `..` — so a new field on
/// `Lowered` does not compile here until it is classified (gated below, or named as not
/// gating); the lane's tripwires ([`lane_tripwires`]: an unreported lane is a residual); the
/// `undef` scan of the body module; and the elided-drop predicate, asked here of the same THIR
/// the body was lowered from. Nothing is taken on trust from the caller.
///
/// THE RULE for a field: anything that can leave a PLACEHOLDER for a real value GATES on this
/// lane, because under D17 no seam differential judges an instance body. A field left unread
/// below says why it cannot.
fn lowering_facts<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: ty::Instance<'tcx>,
    thir: &Thir<'tcx>,
    lowered: &Lowered,
    lane: &MonoLane<'tcx>,
) -> MonoLoweringFacts<'tcx> {
    let Lowered {
        // GATES: the `undef` scan and the one-function precondition read it.
        module,
        // Not a placeholder: a global's identity; a body with a global row is refused by the
        // assembler's TABLE-FREE splice precondition anyway.
        global_origins: _,
        // GATES (initializer body).
        body_kind,
        // GATES (2026-10-01): a tag-free opaque placeholder for a live value.
        opaque_collapse,
        // Not a placeholder: a census of `register_enum` declines (empty unless the census env
        // is set); its CONSEQUENCE, the opaque lane, sets `opaque_collapse`, which gates.
        enum_declines: _,
        // GATES.
        union_lane,
        // Not a placeholder: a record, never a licence; a withheld layout reaches a struct row the
        // table-free splice precondition refuses anyway.
        layout_withheld_structs: _,
        // GATES.
        enum_param_lane,
        // GATES.
        symbolic,
        // GATES through symbolic defensively; actual instance lowering never sets this fact.
        unsubstituted_opaque_return,
        // GATES (coverage).
        unsupported,
        // Not a placeholder: interpretation eligibility. Its writers that do place a stand-in
        // (`undef`, the opaque lanes, the union lane) are gated through their own facts.
        contains_call: _,
        // GATES.
        place_path_carrier,
        // GATES.
        zst_closure_arg,
        // GATES.
        coroutine_frame_ptr,
        // GATES.
        fnptr_adapter,
        // Not a placeholder: flip-only gates. A thin or `&mut` reborrow arm emits no instruction
        // and binds the reborrowed value itself (see the field docs).
        thin_reborrows: _,
        mut_reborrows: _,
        // Not a placeholder: the edges, read by `append_instance_callee_declarations`.
        callees: _,
        // GATES (the pending-const sentinel).
        pending_consts,
        // Not a placeholder: flip reshaping evidence only.
        enum_fold_switch_blocks: _,
    } = lowered;
    let (mono_residual, param_arm_hits) = lane_tripwires(lane);
    MonoLoweringFacts {
        instance,
        first_unsupported: unsupported.first().map(|(_, tag)| *tag),
        symbolic: *symbolic || *unsubstituted_opaque_return,
        opaque_collapse: *opaque_collapse,
        undef_placeholder: module.functions.iter().any(function_has_undef_placeholder),
        param_arm_hits,
        mono_residual,
        union_lane: *union_lane,
        enum_param_lane: *enum_param_lane,
        fnptr_adapter: *fnptr_adapter,
        pending_consts: pending_consts.len(),
        place_path_carrier: *place_path_carrier,
        zst_closure_arg: *zst_closure_arg,
        coroutine_frame_ptr: *coroutine_frame_ptr,
        non_fn_body: *body_kind != BodyKind::Fn,
        drop_bearing: thir_instance_needs_drop(tcx, instance, thir),
        functions: module.functions.len(),
    }
}

// ===========================================================================
// Entry refusals
// ===========================================================================

/// Refuse when this thread is inside a producer lowering (the `mir_built` hook). Everything the
/// instance lane issues — `thir_body`, `needs_drop` and normalization at
/// `fully_monomorphized()`, `tcx.symbol_name`, `Instance::try_resolve` — is a codegen-time
/// query that could close an `E0391` cycle there, so the refusal comes BEFORE any query.
pub(crate) fn refuse_inside_producer_lowering() -> Result<(), InstanceRefusal> {
    if crate::LOWERING_BODIES.with(|s| !s.borrow().is_empty()) {
        return Err(InstanceRefusal::Reentrant);
    }
    Ok(())
}

/// Whether `def` is a Clean-origin definition (its body is Clean's, not a THIR body this producer
/// owns). The same registry `admit_callee_inner` reads.
fn is_clean_origin_def(tcx: TyCtxt<'_>, def: LocalDefId) -> bool {
    tcx.resolutions(()).clean_origin_defs.iter().any(|&(clean_def, _, _)| clean_def == def)
}

/// The entry refusals of the THIR route, in order, before any query that touches the body:
/// inside a producer lowering; not a local item; a Clean-origin definition (the assembled handoff
/// refuses `Producer::Clean` rows); a synthetic coroutine body (`trust_ir_of` refuses it; it has
/// no HIR/THIR); a body already on this thread's lowering stack.
pub(crate) fn instance_entry(
    tcx: TyCtxt<'_>,
    instance: ty::Instance<'_>,
) -> Result<LocalDefId, InstanceRefusal> {
    refuse_inside_producer_lowering()?;
    let def_id = instance.def_id();
    let Some(def) = def_id.as_local() else {
        return Err(InstanceRefusal::ThirUnavailable);
    };
    if is_clean_origin_def(tcx, def) {
        return Err(InstanceRefusal::LaneRefused("clean-origin"));
    }
    if tcx.def_kind(def) == rustc_hir::def::DefKind::SyntheticCoroutineBody {
        return Err(InstanceRefusal::LaneRefused("synthetic coroutine body"));
    }
    if crate::would_reenter_lowering(def_id) {
        return Err(InstanceRefusal::Reentrant);
    }
    Ok(def)
}

/// Whether an instance is a MONOMORPHIC LOCAL plain item — the only instances the assembled
/// handoff can answer (`AssembledCrateModuleForCodegen::exact_instance_body`). PURE.
pub fn is_monomorphic_local_item(
    is_item: bool,
    def_is_local: bool,
    args_all_regions: bool,
) -> bool {
    is_item && def_is_local && args_all_regions
}

// ===========================================================================
// Drops (until increment 4)
// ===========================================================================

/// Does any parameter, local or temporary of `instance` have a type that NEEDS DROP?
///
/// Every value a body holds is a parameter or the result of some expression — a local's value
/// comes from its initializer or scrutinee expression, whose type contains the binding's type,
/// and `needs_drop` is structural — so the parameter types plus every expression type is the
/// whole set. Each is instantiated at the instance and normalized at
/// `TypingEnv::fully_monomorphized()`; a failed or incomplete instantiation answers TRUE
/// (fail-closed), never "no drop".
pub fn thir_instance_needs_drop<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: ty::Instance<'tcx>,
    thir: &Thir<'tcx>,
) -> bool {
    let typing_env = ty::TypingEnv::fully_monomorphized();
    let mut seen: trust_types::fx::FxHashSet<ty::Ty<'tcx>> = Default::default();
    let tys = thir.params.iter().map(|param| param.ty).chain(thir.exprs.iter().map(|e| e.ty));
    for rty in tys {
        if !seen.insert(rty) {
            continue;
        }
        let needs = match tcx.try_instantiate_and_normalize_erasing_regions(
            instance.args,
            typing_env,
            ty::EarlyBinder::bind(tcx, rty),
        ) {
            Ok(out) if !out.has_non_region_param() => out.needs_drop(tcx, typing_env),
            Ok(_) | Err(_) => true,
        };
        if needs {
            return true;
        }
    }
    false
}

/// The drop-bearing check for an instance the assembler LINKS to without re-lowering it (a
/// monomorphic LEAF callee's handoff body). `Err(LaneRefused("drop-bearing"))` when its body
/// elides a drop; any other `Err` means the question could not be asked, which the caller
/// refuses too.
pub fn instance_drop_refusal<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: ty::Instance<'tcx>,
) -> Result<(), InstanceRefusal> {
    let def = instance_entry(tcx, instance)?;
    let Ok((thir, _root)) = tcx.thir_body(def) else {
        return Err(InstanceRefusal::ThirUnavailable);
    };
    if thir.is_stolen() {
        return Err(InstanceRefusal::ThirStolen);
    }
    let thir = thir.borrow();
    if thir_instance_needs_drop(tcx, instance, &thir) {
        return Err(InstanceRefusal::LaneRefused("drop-bearing"));
    }
    Ok(())
}

// ===========================================================================
// Placeholders the module shows
// ===========================================================================

/// Does `f` hold an `Inst::Undef`? Every `undef` the direct producer emits stands in for a value
/// it did not model — the whole-value store of a non-plain value, a variant test on an opaque
/// value, a local havoc'd across a suspend — and no instance lowering may carry one: the gate
/// refuses it as [`InstanceRefusal::LaneRefused`]`("undef placeholder")`. The assembler runs the
/// same scan on a monomorphic LEAF callee's handoff body, which nothing re-lowers. PURE.
pub fn function_has_undef_placeholder(f: &Function) -> bool {
    f.blocks.iter().flat_map(|b| b.body.iter()).any(|node| matches!(node.inst, Inst::Undef { .. }))
}

// ===========================================================================
// Which instance each callee edge names
// ===========================================================================

/// One concretely keyed callee admission on the instance lane: the dense id, the producer's
/// resolved definition and args, whether the instance kind was a plain `Item`, and the RAW call
/// SITE the pair was resolved from — the callee operand `FnDef(site_def, site_args)` as the
/// body's THIR spells it, NOT instantiated at the lane's args. The re-derivation
/// ([`resolve_site`]) instantiates it itself, so it does not inherit the lowering's own
/// instantiation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct CalleeInstanceRecord<'tcx> {
    pub(crate) func_id: FuncId,
    pub(crate) def: DefId,
    pub(crate) args: ty::GenericArgs<'tcx>,
    pub(crate) is_item: bool,
    pub(crate) site_def: DefId,
    pub(crate) site_args: ty::GenericArgs<'tcx>,
}

/// THE RECORDING: called by `LowerCx::admit_concrete_callee_site` for EVERY concretely keyed
/// callee admission. On the instance lane (`lane_active`) it keeps every DISTINCT record — every
/// site, and every conflicting pair too — so [`decide_edge`] judges each one. Two records for one
/// id that disagree on `(def, args, is_item)` are a ledger desync: they arm the monomorphization
/// tripwire (`residual`) AND stay recorded, so the declarations refuse the edge
/// (`CalleeMisresolved`) whatever the lowering reports. `FuncId(0)` is the exhausted-id-space
/// sentinel, whose own tag already refuses the body.
pub(crate) fn record_callee_instance<'tcx>(
    records: &mut Vec<CalleeInstanceRecord<'tcx>>,
    residual: &mut bool,
    lane_active: bool,
    record: CalleeInstanceRecord<'tcx>,
) {
    if !lane_active || record.func_id == FuncId::new(0) {
        return;
    }
    let desync = records.iter().any(|r| {
        r.func_id == record.func_id
            && (r.def != record.def || r.args != record.args || r.is_item != record.is_item)
    });
    if desync {
        *residual = true;
    }
    if !records.contains(&record) {
        records.push(record);
    }
}

/// What the re-derivation found at one record's call site.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SiteResolution<'tcx> {
    /// The record is not an `Item` edge (a shim kind): nothing to re-derive; the edge stays
    /// unresolved, which the assembler refuses.
    NotAnItemRecord,
    /// The site resolved, as codegen resolves a callee operand, to this instance.
    Resolved(ty::Instance<'tcx>),
    /// The site's args did not instantiate to concrete args at this instance, or did not resolve.
    Unresolvable(&'static str),
}

/// THE RE-DERIVATION of one record from its RAW call site, as codegen resolves a callee operand
/// `FnDef(site_def, site_args)` of this instance's body: instantiate `site_args` at the
/// instance's args, normalize at `TypingEnv::fully_monomorphized()`, `Instance::try_resolve`.
fn resolve_site<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: ty::Instance<'tcx>,
    record: &CalleeInstanceRecord<'tcx>,
) -> SiteResolution<'tcx> {
    if !record.is_item {
        return SiteResolution::NotAnItemRecord;
    }
    let typing_env = ty::TypingEnv::fully_monomorphized();
    let Ok(site_args) = tcx.try_instantiate_and_normalize_erasing_regions(
        instance.args,
        typing_env,
        ty::EarlyBinder::bind(tcx, record.site_args),
    ) else {
        return SiteResolution::Unresolvable(
            "its call site's args do not normalize at this instance",
        );
    };
    if site_args.has_non_region_param() || site_args.has_infer() {
        return SiteResolution::Unresolvable(
            "its call site's args are not concrete at this instance",
        );
    }
    match ty::Instance::try_resolve(tcx, typing_env, record.site_def, site_args) {
        Ok(Some(site)) => SiteResolution::Resolved(site),
        Ok(None) | Err(_) => SiteResolution::Unresolvable("its call site does not resolve"),
    }
}

/// Why [`decide_edge`] refused an edge.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum EdgeRefusal<'tcx> {
    /// A concretely keyed edge the lowering never recorded.
    Unrecorded,
    /// Two records for one id name different instances.
    Conflicting(CalleeInstanceRecord<'tcx>, CalleeInstanceRecord<'tcx>),
    /// The site resolves to an instance that is not a plain item — an intrinsic, a virtual
    /// call, a shim — though the lowering linked it as one (the free-fn fast path records a
    /// `DefKind::Fn` callee as an item without resolving it).
    NotAnItem(CalleeInstanceRecord<'tcx>, ty::Instance<'tcx>),
    /// The site resolves to another plain item, or to the same item at other args.
    Misresolved(CalleeInstanceRecord<'tcx>, ty::Instance<'tcx>),
    /// The site could not be re-derived.
    Unresolvable(CalleeInstanceRecord<'tcx>, &'static str),
}

/// THE FROZEN DECISION for one callee edge, over the records the lowering reported for it and
/// what [`resolve_site`] found at each (index-aligned). PURE, so it is unit-tested without a
/// `TyCtxt`. The edge is ADMITTED as the first record's pair only when: it is recorded if it is
/// concretely keyed; every record names the same `(def, args, is_item)`; and every `Item`
/// record's site resolves to exactly `Item(def)` at `args`. `Ok(None)`: an edge with nothing to
/// link (not recorded and not concretely keyed, or a shim kind), which the assembler refuses.
fn decide_edge<'tcx>(
    concretely_keyed: bool,
    records: &[CalleeInstanceRecord<'tcx>],
    sites: &[SiteResolution<'tcx>],
) -> Result<Option<CalleeInstanceRecord<'tcx>>, EdgeRefusal<'tcx>> {
    let Some(&first) = records.first() else {
        return if concretely_keyed { Err(EdgeRefusal::Unrecorded) } else { Ok(None) };
    };
    if let Some(&other) = records
        .iter()
        .find(|r| r.def != first.def || r.args != first.args || r.is_item != first.is_item)
    {
        return Err(EdgeRefusal::Conflicting(first, other));
    }
    if sites.len() != records.len() {
        return Err(EdgeRefusal::Unresolvable(first, "a recorded site was not re-derived"));
    }
    for (&record, &site) in records.iter().zip(sites) {
        match site {
            SiteResolution::NotAnItemRecord if !record.is_item => {}
            SiteResolution::NotAnItemRecord => {
                return Err(EdgeRefusal::Unresolvable(record, "an item record was not re-derived"));
            }
            SiteResolution::Resolved(site)
                if site.def == ty::InstanceKind::Item(record.def) && site.args == record.args => {}
            SiteResolution::Resolved(site) if !matches!(site.def, ty::InstanceKind::Item(_)) => {
                return Err(EdgeRefusal::NotAnItem(record, site));
            }
            SiteResolution::Resolved(site) => return Err(EdgeRefusal::Misresolved(record, site)),
            SiteResolution::Unresolvable(why) => {
                return Err(EdgeRefusal::Unresolvable(record, why));
            }
        }
    }
    Ok(first.is_item.then_some(first))
}

/// The refusal an [`EdgeRefusal`] becomes, with the edge named.
fn edge_refusal_text<'tcx>(
    tcx: TyCtxt<'tcx>,
    k: usize,
    def_path: &str,
    refusal: EdgeRefusal<'tcx>,
) -> InstanceRefusal {
    let pair = |r: CalleeInstanceRecord<'tcx>| tcx.def_path_str_with_args(r.def, r.args);
    match refusal {
        EdgeRefusal::Unrecorded => InstanceRefusal::NotSelfContained(format!(
            "callee FuncId({k}) `{def_path}` carries a concrete key but its instance was never \
             recorded"
        )),
        EdgeRefusal::Conflicting(a, b) => InstanceRefusal::CalleeMisresolved(format!(
            "callee FuncId({k}) `{def_path}`: the lowering recorded two different instances for \
             one edge (`{}` and `{}`)",
            pair(a),
            pair(b)
        )),
        EdgeRefusal::NotAnItem(r, site) => InstanceRefusal::CalleeMisresolved(format!(
            "callee FuncId({k}) `{def_path}`: its call site resolves to `{site}`, which is not a \
             plain item (an intrinsic, a virtual call or a shim has no body the instance lane can \
             splice), though the lowering linked it as the item `{}`",
            pair(r)
        )),
        EdgeRefusal::Misresolved(r, site) => InstanceRefusal::CalleeMisresolved(format!(
            "callee FuncId({k}) `{def_path}`: the lowering linked `{}` but its call site \
             resolves to `{site}`",
            pair(r)
        )),
        EdgeRefusal::Unresolvable(r, why) => InstanceRefusal::CalleeMisresolved(format!(
            "callee FuncId({k}) `{def_path}`: the lowering linked `{}` but {why}",
            pair(r)
        )),
    }
}

/// The signature a callee DECLARATION of an instance module carries, or why it has none. PURE.
///
/// `params` is ground truth from the callee's `fn_sig` at the resolved instance
/// ([`CalleeRef::params`]); `ret` is the result type the call sites bind ([`CalleeRef::ret_ty`];
/// `None` = no site binds one, which is the `returns: []` spelling). REFUSED: an unsigned or
/// withdrawn parameter list, a result type two sites disagreed on, and an edge with NO call site
/// at all (a reify-only edge: nothing observed its result, so `returns: []` would be a false
/// claim for a non-unit callee). Never spelled `is_vararg: true`, the v41-refused
/// unknown-signature smuggling pattern.
pub fn declaration_func_ty(
    params: &ParamSignature,
    ret: Option<Ty>,
    ret_conflict: bool,
    has_call_site: bool,
) -> Result<trust_ir::FuncTy, &'static str> {
    if ret_conflict {
        return Err("call sites disagree on the result type");
    }
    if !has_call_site {
        return Err("no call site binds the result (a reify-only edge)");
    }
    match params {
        ParamSignature::Signed(tys) => Ok(trust_ir::FuncTy {
            params: tys.clone(),
            returns: ret.into_iter().collect(),
            is_vararg: false,
            abi: None,
        }),
        ParamSignature::Unsigned => Err("parameter list unsigned"),
        ParamSignature::Withdrawn => Err("parameter list withdrawn"),
    }
}

/// Stamp the exact source convention through the same typed mapping as declarations and rmeta.
/// Unsupported source protocols refuse, including ordinary rust-call's missing tuple adapter.
pub(crate) fn stamp_instance_calling_conv(
    tcx: TyCtxt<'_>,
    def: LocalDefId,
    module: &mut trust_ir::Module,
) -> Result<(), InstanceRefusal> {
    let abi = crate::calling_convention::FunctionAbi::of_definition(tcx, def.to_def_id());
    let convention = abi.calling_conv().map_err(InstanceRefusal::LaneRefused)?;
    let Some(function) = module.function_by_id_mut(FuncId::new(0)) else {
        return Err(InstanceRefusal::NoBodyFunction);
    };
    function.calling_conv = convention;
    Ok(())
}

fn body_calls(module: &trust_ir::Module, callee: FuncId) -> bool {
    module.function_by_id(FuncId::new(0)).is_some_and(|body| {
        body.blocks.iter().flat_map(|b| b.body.iter()).any(|node| {
            matches!(&node.inst, Inst::Call { callee: c, .. } | Inst::Invoke { callee: c, .. } if *c == callee)
        })
    })
}

/// Append one SIGNED bodyless declaration per callee edge, so the instance module names nothing
/// it does not carry.
///
/// Runs AFTER `stamp_instance_symbol`, which relies on the body being the module's only function.
/// Each edge `FuncId(k)` (the ledger is dense `1..=n`, checked) becomes a declaration named by the
/// LINK-TIME identity of the instance it resolved to — `tcx.symbol_name(J)` — or by a reserved
/// `!trust_self_edge::{k}` / `!trust_unresolved_callee::{k}` name no Rust symbol can spell.
///
/// FAIL-CLOSED ON A MISSING RECORD: an edge whose ledger row carries a concrete key was admitted
/// through `admit_concrete_callee_site`, which must have recorded it
/// ([`record_callee_instance`]); a concretely keyed edge with no record refuses the module
/// (`NotSelfContained`), so removing the recording plumbing cannot quietly unresolve edges.
///
/// RE-DERIVED, NOT TRUSTED: every recorded site of an `Item` edge is resolved again from its RAW
/// call site ([`resolve_site`]) and must name the pair the lowering linked, and all records of
/// one edge must agree ([`decide_edge`]); otherwise the body is refused (`CalleeMisresolved`).
/// The pair is then re-resolved at the fully-monomorphized env and kept only as the SAME plain
/// item; anything else stays unresolved (which the assembler refuses).
pub(crate) fn append_instance_callee_declarations<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: ty::Instance<'tcx>,
    module: &mut trust_ir::Module,
    callees: &[CalleeRef],
    recorded: &[CalleeInstanceRecord<'tcx>],
) -> Result<Vec<InstanceCallee<'tcx>>, InstanceRefusal> {
    refuse_inside_producer_lowering()?;
    let typing_env = ty::TypingEnv::fully_monomorphized();
    let mut out = Vec::with_capacity(callees.len());
    for (position, callee) in callees.iter().enumerate() {
        let k = position + 1;
        if callee.func_id != FuncId::new(k as u32) {
            return Err(InstanceRefusal::NotSelfContained(format!(
                "the callee ledger is not dense: position {k} holds FuncId({})",
                callee.func_id.index()
            )));
        }
        let records: Vec<CalleeInstanceRecord<'tcx>> =
            recorded.iter().filter(|r| r.func_id == callee.func_id).copied().collect();
        let sites: Vec<SiteResolution<'tcx>> =
            records.iter().map(|record| resolve_site(tcx, instance, record)).collect();
        let admitted = decide_edge(callee.concrete_key.is_some(), &records, &sites)
            .map_err(|refusal| edge_refusal_text(tcx, k, &callee.def_path, refusal))?;
        let resolved = admitted.and_then(|r| {
            match ty::Instance::try_resolve(tcx, typing_env, r.def, r.args) {
                Ok(Some(j)) if j.def == ty::InstanceKind::Item(r.def) => Some(j),
                _ => None,
            }
        });
        let name = match resolved {
            Some(j) if j == instance => format!("!trust_self_edge::{k}"),
            Some(j) => tcx.symbol_name(j).name.to_string(),
            None => format!("!trust_unresolved_callee::{k}"),
        };
        let func_ty = if let Some(exact) = crate::foreign_signature::read(tcx, callee) {
            crate::foreign_signature::check_observation(&exact, callee.abi, &callee.params,
                callee.ret_ty.as_ref(), callee.ret_ty_conflict, body_calls(module, callee.func_id))
                .map_err(|why| InstanceRefusal::UnsignableCallee(format!("`{name}`: {why}")))?;
            let source = crate::foreign_signature::ForeignSource::capture(tcx, callee)
                .ok_or_else(|| InstanceRefusal::UnsignableCallee("foreign source identity is not reconstructible".into()))?;
            let actual = source.recheck(tcx, &exact)
                .map_err(InstanceRefusal::UnsignableCallee)?;
            if resolved != Some(actual) {
                return Err(InstanceRefusal::UnsignableCallee("foreign prototype names another resolved call-site instance".into()));
            }
            exact
        } else { declaration_func_ty(
            &callee.params,
            callee.ret_ty.clone(),
            callee.ret_ty_conflict,
            body_calls(module, callee.func_id),
        )
        .map_err(|why| InstanceRefusal::UnsignableCallee(format!("`{name}`: {why}")))? };
        // trust-ir D1b: a refused table door refuses the instance, never panics.
        let foreign_prototype = func_ty.abi.is_some();
        let ty = module
            .intern_func_type(func_ty)
            .map_err(|refusal| InstanceRefusal::UnsignableCallee(format!("`{name}`: {refusal}")))?;
        let mut declaration = Function::new(callee.func_id, name, ty, BlockId::new(0))
            .with_producer(trust_ir::Producer::TRust);
        if foreign_prototype { declaration.producer = None; }
        declaration.linkage = Linkage::External;
        declaration.calling_conv = callee.abi.calling_conv()
            .map_err(|why| InstanceRefusal::UnsignableCallee(why.to_string()))?;
        module
            .try_add_function(declaration)
            .map_err(|refusal| InstanceRefusal::UnsignableCallee(refusal.to_string()))?;
        out.push(InstanceCallee { func_id: callee.func_id, instance: resolved });
    }
    Ok(out)
}

// ===========================================================================
// The module's shape
// ===========================================================================

/// Is `module` a SELF-CONTAINED instance module with `n` callee declarations? PURE. `Err` names
/// the first violation.
///
/// * exactly `1 + n` functions, with dense ids `0..=n` in position;
/// * `FuncId(0)` is the only body; `FuncId(1..=n)` are bodyless declarations;
/// * no two functions share a name (the link-time identity);
/// * trust-ir's own exhaustive dependency census from `FuncId(0)` refuses NOTHING except the `n`
///   bodyless declarations — so every function the body names is present, and no indirect call,
///   opaque type, dialect op or unresolved symbol is reachable.
pub fn instance_module_is_self_contained(
    module: &trust_ir::Module,
    n: usize,
) -> Result<(), String> {
    use trust_ir::function_dependencies::{DependencyRefusalKind, inspect_function_dependencies};
    if module.functions.len() != n + 1 {
        return Err(format!(
            "{} function(s) where the body plus {n} declaration(s) were expected",
            module.functions.len()
        ));
    }
    for (position, function) in module.functions.iter().enumerate() {
        if function.id != FuncId::new(position as u32) {
            return Err(format!(
                "position {position} holds FuncId({}); ids must be dense",
                function.id.index()
            ));
        }
        let bodied = !function.blocks.is_empty();
        if position == 0 && !bodied {
            return Err("FuncId(0) carries no body".to_string());
        }
        if position != 0 && bodied {
            return Err(format!(
                "declaration FuncId({position}) `{}` carries a body",
                function.name
            ));
        }
    }
    let mut names = std::collections::BTreeSet::new();
    for function in &module.functions {
        if !names.insert(function.name.as_str()) {
            return Err(format!("two functions are named `{}`", function.name));
        }
    }
    let census = inspect_function_dependencies(module, FuncId::new(0));
    for refusal in census.refusals() {
        match &refusal.kind {
            DependencyRefusalKind::BodylessFunction(id)
                if (1..=n).contains(&(id.index() as usize)) => {}
            other => return Err(format!("dependency census refuses {other:?}")),
        }
    }
    Ok(())
}

/// The instance module is self-contained ([`instance_module_is_self_contained`]) and passes
/// `trust_ir_build::validate_module` STANDALONE, on a copy carrying the target (a bodyless
/// external declaration demands a pinned target, `TargetInfoRequired`); the module itself stays
/// exactly what the producer emitted. A bad edge refuses this instance only.
pub(crate) fn validate_instance_module(
    tcx: TyCtxt<'_>,
    module: &trust_ir::Module,
    n: usize,
) -> Result<(), InstanceRefusal> {
    instance_module_is_self_contained(module, n).map_err(InstanceRefusal::NotSelfContained)?;
    let mut stamped = module.clone();
    if stamped.target_info.is_none() {
        stamped.target_info = Some(crate::crate_module::source_target_info(tcx));
    }
    if let Some(first) = trust_ir_build::validate_module(&stamped).first() {
        return Err(InstanceRefusal::NotSelfContained(format!("validate_module: {first:?}")));
    }
    Ok(())
}

/// The FINAL validator crate finalization runs on the assembled module
/// (`trust_ir_build::validate_module` plus duplicate function names), which the codegen-time
/// assembler runs on the module it EXTENDS, so that module is held to the check the base passed.
/// Here, beside the other admission legs, rather than behind an unfrozen forwarder.
pub fn assembled_codegen_validation_errors(module: &trust_ir::Module) -> Vec<String> {
    crate::crate_module::final_module_validation_errors(module)
}

/// Does the body at `FuncId(0)` name NO function pointer? PURE.
///
/// Read off trust-ir's dependency census, never the table sizes (`func_types.len() == 1` is
/// neither sufficient — a `FnDef` whose signature equals the body's dedups to the body's own row
/// — nor necessary — interning callee signatures grows the table with no fn pointer at all):
///
/// * the ONLY `FunctionType` edge admitted is a function's definition naming its own `ty` row;
///   any other one — an instruction's `Ty::Func` value or `CallIndirect` signature, or a
///   `Ty::Func` inside a signature or a block parameter — is a fn pointer;
/// * every function an instruction reaches must be the callee of a direct `Call`/`Invoke`; a
///   `Constant::FnDef` / `Constant::Closure`, a `SeqMap` map function or a `Switch` case naming a
///   function is a first-class function value.
pub fn instance_body_is_fn_pointer_free(module: &trust_ir::Module) -> bool {
    use trust_ir::function_dependencies::{
        DependencyNode, DependencySite, inspect_function_dependencies,
    };
    let census = inspect_function_dependencies(module, FuncId::new(0));
    census.edges().iter().all(|edge| match (edge.site, edge.target) {
        (
            DependencySite::Definition(DependencyNode::Function(function)),
            DependencyNode::FunctionType(signature),
        ) => module.function_by_id(function).is_some_and(|f| f.ty == signature),
        (_, DependencyNode::FunctionType(_)) => false,
        (DependencySite::Instruction { function, block, index }, DependencyNode::Function(_)) => {
            module
                .function_by_id(function)
                .and_then(|f| f.blocks.iter().find(|b| b.id == block))
                .and_then(|b| b.body.get(index))
                .is_some_and(|node| matches!(node.inst, Inst::Call { .. } | Inst::Invoke { .. }))
        }
        _ => true,
    })
}

// ===========================================================================
// The identity of an analysis-time declaration
// ===========================================================================

/// Does the analysis-time declaration `decl_name` of the assembled module name `instance`?
///
/// Crate finalization names a declaration of a callee by its display path
/// (`with_no_trimmed_paths!(def_path_str)`), and — when another definition or declaration shares
/// that path — `!trust_bodyless_instance::<path>::<definition>-<hex(key)>`, where `<definition>`
/// is the callee's stable `DefinitionIdentity` and `key` is `<class>:<path>|concrete-v1:<concrete
/// key>`. What is checked is exactly what the name carries: the bare path names the guest edge's
/// DEFINITION (the one declaration of that definition in the module; it carries no instance key,
/// so two instances of one definition with one signature are told apart there only by the
/// relink's instruction equality); the collision form is checked in full — the path, the
/// definition identity, and the concrete key recomputed from the instance the guest edge
/// resolved to (`ConcreteCalleeKey` over the instance's own args). Anything else is `Err`: the
/// relink refuses rather than trust the position alone.
pub fn declaration_names_instance<'tcx>(
    tcx: TyCtxt<'tcx>,
    decl_name: &str,
    instance: ty::Instance<'tcx>,
) -> Result<(), String> {
    let ty::InstanceKind::Item(def) = instance.def else {
        return Err(format!("`{decl_name}`: the guest edge is not a plain item"));
    };
    let path = rustc_middle::ty::print::with_no_trimmed_paths!(tcx.def_path_str(def));
    let definition = crate::lineage::DefinitionIdentity::from_def_id(tcx, def).symbol_suffix();
    let Some(args) = crate::encode_site_args(tcx, instance.args) else {
        return Err(format!("`{path}`: the instance's args are not encodable"));
    };
    let concrete = crate::lineage::ConcreteCalleeKey::from_site_args(
        tcx,
        def,
        crate::lineage::ConcreteInstanceKind::Item,
        &args,
    )
    .symbol_suffix();
    declaration_name_matches(decl_name, &path, &definition, &concrete)
}

/// The PURE half of [`declaration_names_instance`]: does `decl_name` name the definition at
/// display path `path` with stable identity `definition`, at the instance whose concrete key
/// renders as `concrete`? The bare path is the one declaration of that definition in the
/// module; the collision form is checked in full.
pub fn declaration_name_matches(
    decl_name: &str,
    path: &str,
    definition: &str,
    concrete: &str,
) -> Result<(), String> {
    if decl_name == path {
        return Ok(());
    }
    let Some(rest) = decl_name
        .strip_prefix("!trust_bodyless_instance::")
        .and_then(|rest| rest.strip_prefix(path))
        .and_then(|rest| rest.strip_prefix("::"))
    else {
        return Err(format!("the declaration `{decl_name}` does not name `{path}`"));
    };
    let Some(hex) = rest.strip_prefix(definition).and_then(|r| r.strip_prefix('-')) else {
        return Err(format!(
            "the declaration `{decl_name}` names another definition than `{path}`"
        ));
    };
    let Some(key) = decode_hex_text(hex) else {
        return Err(format!("the declaration `{decl_name}` carries an undecodable key"));
    };
    let expected_tail = format!("{path}|concrete-v1:{concrete}");
    match key.split_once(':') {
        Some((class, tail)) if !class.is_empty() && tail == expected_tail => Ok(()),
        _ => Err(format!(
            "the declaration `{decl_name}` keys another instance of `{path}` than the one the \
             edge resolved to"
        )),
    }
}

fn decode_hex_text(hex: &str) -> Option<String> {
    if !hex.len().is_multiple_of(2) {
        return None;
    }
    let bytes: Option<Vec<u8>> = (0..hex.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(hex.get(i..i + 2)?, 16).ok())
        .collect();
    String::from_utf8(bytes?).ok()
}

#[cfg(test)]
mod tests;
