//! Trust: WALL-A INSTANCE-FLIP PROBE — measurement only, off by default.
//!
//! Behind `-Ztrust-instance-flip-probe=<filter>` (`*` matches every body; any other
//! value is a def-path substring). The driver's option-domain gate additionally
//! requires `-Ztrust-verify=off -Ztrust-ir-lower` and refuses every `-Ztrust-dump`
//! sink, so this probe can never run in an evidence or artifact-publication lane.
//!
//! # What it measures, and why
//!
//! Wall A (`shim: abi rederive: generic fn signature`, `to_mir::rederive_abi_sig`):
//! a generic body's derived-vs-built differential reaches `agreed` at the
//! `mir_built` hook (`SigSource::Provided`, both sides polymorphic), but the FLIP
//! cannot re-derive a concrete ABI at the `LocalDefId` seam, so the body never
//! compiles from trust-ir. The priced fix is an Instance-level (post-mono) flip
//! seam. This probe answers that design's load-bearing unknowns WITHOUT building
//! the seam:
//!
//! * **Channel A (`TRUST-WALLA-PROBE A`, at the `mir_built` hook)** — for a
//!   generic `agreed` body that is a TRAIT DEFAULT METHOD, enumerate the crate's
//!   local concrete impls, `Instance::try_resolve` each one, and then:
//!   (a) instantiate rustc's OWN freshly built body at the instance's args with
//!   rustc's own `try_instantiate_mir_and_normalize_erasing_regions` — the
//!   incumbent, per instance; (b) re-derive the ABI signature from `tcx` alone at
//!   the instance's args — the exact computation `rederive_abi_sig` refuses at
//!   identity args, now with a concrete answer, checked EXACTLY against the
//!   instantiated built body's ABI locals (the flip's two-independent-derivations
//!   evidence, transplanted to the instance seam); and (c) hand the instantiated
//!   built body to the FROZEN comparator `mir_differential::compare_derived`,
//!   which re-lowers the recorded trust-ir Module against it and reaches a
//!   verdict. `DerivedAgreed` here means: the untouched oracle, comparing the
//!   derived body it would flip against rustc's own instantiation of its own
//!   MIR, agrees at the instance level.
//! * **Channel B (`TRUST-WALLA-PROBE B`, after `codegen_crate`)** — for every
//!   stashed generic body, walk the mono partition codegen ACTUALLY demanded and,
//!   per concrete instance: does the instance-level ABI rederivation succeed, does
//!   `to_mir::lower_ir_to_mir` produce the derived body at those concrete anchors
//!   (i.e. does the flip's product exist), and do the derived body's ABI locals
//!   EXACTLY equal rustc's instantiated `optimized_mir`'s? Bodies with no mono
//!   instance in this crate are reported too — a per-instance flip has nothing to
//!   flip for them here, and that is a population fact the design must state.
//! * **Channel C (`TRUST-WALLA-PROBE C`, after `codegen_crate`)** — the scoreboard of
//!   step 2 of docs/plans/2026-09-29-trust-ir-sole-compile-path.md ("trust-ir is the only
//!   codegen input"): every `MonoItem::Fn` the collector handed codegen goes through the
//!   instance-keyed producer's routing rule, and the source-first (THIR) route through the
//!   producer itself. One row per instance (`route=thir|mir|pre-route`, `result=ok(..)|
//!   refused(<class>)|assembly-refused(<why>)|erased(<what>)|not-conserved(<what>)|
//!   abstracted(<what>)|residue`), then a summary and a per-class table. Only `route=thir
//!   result=ok` is coverage, and since 2026-10-01 it means lowered AND spliced into the
//!   published crate module with every MIR loop nest still a loop, every effect of the MIR
//!   census carried (the effect-conservation gate, `effect_conservation`) and no abstraction the
//!   gate or the probe can see (an elided drop, an `undef`, an opaque placeholder lane) — see
//!   `assembly_state` for what it cannot see;
//!   `route=mir` (upstream items, shims) is residue and is not lowered here, because MIR is
//!   not a production input under that plan.
//!
//! # What it deliberately does NOT do
//!
//! It installs nothing, flips nothing, and changes no emitted code. Channel A
//! calls `compare_derived` a second time for probed bodies, which bumps the
//! session-wide `DerivedSessionStats` tally that rides DEBUG log events — that is
//! why the option-domain gate refuses `-Ztrust-dump`: a probe compile must never
//! double-count inside a published artifact (the artifact itself is built from
//! per-body records, not from that tally, but the gate closes the question).
//!
//! Output: `eprintln!` lines prefixed `TRUST-WALLA-PROBE`, deliberately
//! independent of `RUSTC_LOG` filtering.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com> | Copyright 2026 | License: MIT OR Apache-2.0

use std::collections::{HashMap, HashSet};

use rustc_hir::def::DefKind;
use rustc_middle::mir::{Body, Local};
use rustc_middle::mono::MonoItem;
use rustc_middle::ty::{self, TyCtxt, TypeVisitableExt};
use rustc_span::def_id::LocalDefId;

use crate::{Lowered, mir_differential, to_mir};

/// Session-owned stash: one entry per flag-matched generic `agreed` body.
/// Bounded by the wall-A population (tens of bodies), and holds only
/// lifetime-free values (the same clones `flip_registry` itself stores).
#[derive(Default)]
struct ProbeStash {
    entries: HashMap<u32, StashEntry>,
}

struct StashEntry {
    def_path: String,
    module: trust_ir::Module,
    callees: Vec<crate::CalleeRef>,
    enum_fold_switch_blocks: HashSet<trust_ir::BlockId>,
}

impl Clone for StashEntry {
    fn clone(&self) -> Self {
        StashEntry {
            def_path: self.def_path.clone(),
            module: self.module.clone(),
            callees: self.callees.clone(),
            enum_fold_switch_blocks: self.enum_fold_switch_blocks.clone(),
        }
    }
}

fn probe_filter(tcx: TyCtxt<'_>) -> Option<String> {
    tcx.sess.opts.unstable_opts.trust_instance_flip_probe.clone()
}

/// The wall-A membership test: the same predicate `rederive_abi_sig` refuses on,
/// applied to the body's identity signature.
fn identity_sig_is_generic(tcx: TyCtxt<'_>, def: LocalDefId) -> bool {
    match tcx.def_kind(def) {
        DefKind::Fn { .. } | DefKind::AssocFn { .. } => tcx
            .fn_sig(def)
            .instantiate_identity()
            .skip_normalization()
            .skip_binder()
            .has_non_region_param(),
        DefKind::Closure { .. } => {
            tcx.type_of(def).instantiate_identity().skip_normalization().has_non_region_param()
        }
        _ => false,
    }
}

/// Mirror of `to_mir::rederive_abi_sig`, at the INSTANCE's args instead of
/// identity args: compute the ABI-boundary rustc types from `tcx` alone —
/// `fn_sig`/`type_of` instantiated at concrete args, regions erased, normalized
/// in the fully-monomorphized typing env. Fail-closed: any residual param is an
/// error string, never a wrong answer.
fn rederive_abi_sig_at_instance<'tcx>(
    tcx: TyCtxt<'tcx>,
    def: LocalDefId,
    args: ty::GenericArgs<'tcx>,
) -> Result<(Vec<ty::Ty<'tcx>>, ty::Ty<'tcx>), String> {
    let typing_env = ty::TypingEnv::fully_monomorphized();
    match tcx.def_kind(def) {
        DefKind::Fn { .. } | DefKind::AssocFn { .. } => {
            let sig = tcx.fn_sig(def).instantiate(tcx, args).skip_normalization();
            if sig.skip_binder().has_non_region_param() {
                return Err("instance sig still generic after instantiation".into());
            }
            let sig = tcx.normalize_erasing_late_bound_regions(typing_env, sig);
            Ok((sig.inputs().to_vec(), sig.output()))
        }
        DefKind::Closure { .. } => {
            let closure_ty = tcx.type_of(def).instantiate(tcx, args).skip_normalization();
            if closure_ty.has_non_region_param() {
                return Err("instance closure ty still generic after instantiation".into());
            }
            let ty::Closure(_, cargs) = closure_ty.kind() else {
                return Err("non-plain-closure body".into());
            };
            let closure_args = cargs.as_closure();
            let env_ty =
                tcx.closure_env_ty(closure_ty, closure_args.kind(), tcx.lifetimes.re_erased);
            let sig = tcx.normalize_erasing_late_bound_regions(typing_env, closure_args.sig());
            let ty::Tuple(arg_tys) = sig.inputs()[0].kind() else {
                return Err("untupled closure sig".into());
            };
            let mut inputs = vec![env_ty];
            inputs.extend(arg_tys.iter());
            Ok((inputs, sig.output()))
        }
        other => Err(format!("{other:?} body outside probe fragment")),
    }
}

/// EXACT ABI comparison: `(inputs, output)` against a body's `_0..=arg_count`
/// local types — the flip's ABI-gate discipline (never a layout argument).
fn abi_exact<'tcx>(
    inputs: &[ty::Ty<'tcx>],
    output: ty::Ty<'tcx>,
    body: &Body<'tcx>,
) -> Result<(), String> {
    if inputs.len() != body.arg_count {
        return Err(format!("arg count {} vs body {}", inputs.len(), body.arg_count));
    }
    for (i, t) in inputs.iter().enumerate() {
        let b = body.local_decls[Local::from_usize(i + 1)].ty;
        if *t != b {
            return Err(format!("arg{i}: rederived `{t:?}` vs `{b:?}`"));
        }
    }
    let b0 = body.local_decls[Local::from_usize(0)].ty;
    if output != b0 {
        return Err(format!("ret: rederived `{output:?}` vs `{b0:?}`"));
    }
    Ok(())
}

/// Channel A + the stash write. Called from the `mir_built` hook, AFTER the real
/// differential/record_green and BEFORE `crate_module::record` consumes `lowered`.
pub fn hook_probe<'tcx>(
    tcx: TyCtxt<'tcx>,
    def: LocalDefId,
    lowered: &Lowered,
    built: &Body<'tcx>,
    agreed: bool,
) {
    let Some(filter) = probe_filter(tcx) else { return };
    if !agreed || !lowered.unsupported.is_empty() {
        return;
    }
    if !identity_sig_is_generic(tcx, def) {
        return;
    }
    // `with_no_trimmed_paths!` here and on every probe label below: these strings are a
    // FILTER KEY and measurement labels, never diagnostic text. A bare `def_path_str` runs the
    // `trimmed_def_paths` query, which arms rustc's `must_produce_diag` — a probed crate that
    // compiles without emitting a diagnostic then ICEs at `DiagCtxt` teardown — and it makes
    // the `contains(filter)` test depend on which other names happen to be in scope.
    let def_path =
        rustc_middle::ty::print::with_no_trimmed_paths!(tcx.def_path_str(def.to_def_id()));
    if filter != "*" && !def_path.contains(filter.as_str()) {
        return;
    }
    let def_index = def.to_def_id().index.as_u32();
    let entry = StashEntry {
        def_path: def_path.clone(),
        module: lowered.module.clone(),
        callees: lowered.callees.clone(),
        enum_fold_switch_blocks: lowered.enum_fold_switch_blocks.clone(),
    };
    tcx.sess.with_trust_compiler_state::<ProbeStash, _>(|stash| {
        stash.entries.insert(def_index, entry);
    });
    eprintln!("TRUST-WALLA-PROBE stash def_index={def_index} def={def_path}");

    // Channel A needs locally enumerable concrete instantiations: a trait default
    // method with concrete local impls. Everything else is measured per real mono
    // instance in channel B.
    let Some(trait_id) = tcx.trait_of_assoc(def.to_def_id()) else {
        eprintln!(
            "TRUST-WALLA-PROBE A def={def_path} skip=not-a-trait-default-method \
             (instances measured in channel B)"
        );
        return;
    };
    if !tcx.generics_of(def).own_params.is_empty() {
        eprintln!("TRUST-WALLA-PROBE A def={def_path} skip=method-has-own-generics");
        return;
    }
    let impls = tcx.trait_impls_of(trait_id);
    let all_impls: Vec<_> = impls
        .blanket_impls()
        .iter()
        .copied()
        .chain(impls.non_blanket_impls().values().flat_map(|v| v.iter().copied()))
        .collect();
    for imp in all_impls {
        if !imp.is_local() {
            continue;
        }
        let trait_ref = tcx.impl_trait_ref(imp).instantiate_identity().skip_normalization();
        let args = tcx.erase_and_anonymize_regions(trait_ref.args);
        if args.has_non_region_param() {
            eprintln!(
                "TRUST-WALLA-PROBE A def={def_path} impl={} skip=generic-impl",
                rustc_middle::ty::print::with_no_trimmed_paths!(tcx.def_path_str(imp))
            );
            continue;
        }
        let resolved = ty::Instance::try_resolve(
            tcx,
            ty::TypingEnv::fully_monomorphized(),
            def.to_def_id(),
            args,
        );
        let inst = match resolved {
            Ok(Some(inst)) => inst,
            Ok(None) => {
                eprintln!(
                    "TRUST-WALLA-PROBE A def={def_path} impl={} resolve=ambiguous",
                    rustc_middle::ty::print::with_no_trimmed_paths!(tcx.def_path_str(imp))
                );
                continue;
            }
            Err(_) => {
                eprintln!(
                    "TRUST-WALLA-PROBE A def={def_path} impl={} resolve=error",
                    rustc_middle::ty::print::with_no_trimmed_paths!(tcx.def_path_str(imp))
                );
                continue;
            }
        };
        if inst.def_id() != def.to_def_id() {
            eprintln!(
                "TRUST-WALLA-PROBE A def={def_path} impl={} resolve=overridden-by-impl \
                 (resolves to {})",
                rustc_middle::ty::print::with_no_trimmed_paths!(tcx.def_path_str(imp)),
                rustc_middle::ty::print::with_no_trimmed_paths!(tcx.def_path_str(inst.def_id()))
            );
            continue;
        }
        // catch_unwind: one unexpected panic must not kill the whole harvest —
        // a probe line saying PANIC is a measurement; a dead compile is not
        // (same defense-in-depth stance as `trust_ir_flip::try_flip`).
        let caught = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            probe_instance_at_hook(tcx, def, &def_path, lowered, built, inst);
        }));
        if caught.is_err() {
            eprintln!(
                "TRUST-WALLA-PROBE A def={def_path} inst_args={:?} PANIC-in-probe",
                inst.args
            );
        }
    }
}

/// One channel-A measurement: incumbent = rustc's own instantiation of its own
/// freshly built body; verdict = the frozen comparator on the instantiated pair.
fn probe_instance_at_hook<'tcx>(
    tcx: TyCtxt<'tcx>,
    def: LocalDefId,
    def_path: &str,
    lowered: &Lowered,
    built: &Body<'tcx>,
    inst: ty::Instance<'tcx>,
) {
    let typing_env = ty::TypingEnv::fully_monomorphized();
    let inst_built = match inst.try_instantiate_mir_and_normalize_erasing_regions(
        tcx,
        typing_env,
        ty::EarlyBinder::bind(tcx, built.clone()),
    ) {
        Ok(b) => b,
        Err(e) => {
            eprintln!(
                "TRUST-WALLA-PROBE A def={def_path} inst_args={:?} incumbent=NORMALIZATION-ERROR {e:?}",
                inst.args
            );
            return;
        }
    };
    let residual_generic = inst_built.has_non_region_param();
    let abi_indep = match rederive_abi_sig_at_instance(tcx, def, inst.args) {
        Ok((inputs, output)) => match abi_exact(&inputs, output, &inst_built) {
            Ok(()) => "exact".to_string(),
            Err(e) => format!("MISMATCH({e})"),
        },
        Err(e) => format!("REDERIVE-ERR({e})"),
    };
    // The FROZEN comparator, untouched: it re-lowers the recorded Module with
    // `SigSource::Provided` anchors read from THIS instantiated body, and
    // canonically compares the two — exactly the object a per-instance flip
    // would consume, against exactly the incumbent it would replace. The
    // comparator fails closed without a built-side extraction snapshot, so the
    // probe extracts the INSTANTIATED built body through the same faithful lane
    // the comparator uses for the derived side.
    let vf_inst_built = trust_mir_extract::extract_function_faithful(tcx, &inst_built);
    let report =
        mir_differential::compare_derived(tcx, def, lowered, &inst_built, Some(&vf_inst_built));
    eprintln!(
        "TRUST-WALLA-PROBE A def={def_path} inst_args={:?} residual_generic={residual_generic} \
         abi_rederive_at_instance={abi_indep} verdict={:?} markers_exact={} detail={}",
        inst.args, report.verdict, report.markers_exact, report.detail
    );
}

/// Channel B. Called from `start_codegen` AFTER `codegen_crate`: the mono
/// partition is computed and cached, every flip decision has fired.
pub fn finalize_probe(tcx: TyCtxt<'_>) {
    let Some(filter) = probe_filter(tcx) else {
        return;
    };
    if !tcx.sess.opts.output_types.should_codegen() {
        eprintln!("TRUST-WALLA-PROBE B skipped=no-codegen-in-this-session");
        return;
    }
    // Channel C runs first and independently of B's stash: it measures every collected
    // instance, not only the stashed generic bodies.
    channel_c(tcx, &filter);
    let entries: HashMap<u32, StashEntry> =
        tcx.sess.with_trust_compiler_state::<ProbeStash, _>(|s| s.entries.clone());
    if entries.is_empty() {
        eprintln!("TRUST-WALLA-PROBE B stash-empty (no generic agreed body matched the filter)");
        return;
    }
    let partitions = tcx.collect_and_partition_mono_items(());
    let mut seen: HashSet<(u32, String)> = HashSet::new();
    let mut counts: HashMap<u32, usize> = HashMap::new();
    for cgu in partitions.codegen_units {
        for item in cgu.items().keys() {
            let MonoItem::Fn(inst) = item else { continue };
            let did = inst.def_id();
            let Some(def) = did.as_local() else { continue };
            let idx = did.index.as_u32();
            let Some(entry) = entries.get(&idx) else { continue };
            if !seen.insert((idx, format!("{:?}", inst.args))) {
                continue;
            }
            *counts.entry(idx).or_insert(0) += 1;
            let caught = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                probe_mono_instance(tcx, def, *inst, entry);
            }));
            if caught.is_err() {
                eprintln!(
                    "TRUST-WALLA-PROBE B def={} inst_args={:?} PANIC-in-probe",
                    entry.def_path, inst.args
                );
            }
        }
    }
    let mut missing: Vec<_> = entries.iter().filter(|(idx, _)| !counts.contains_key(idx)).collect();
    missing.sort_by_key(|(idx, _)| **idx);
    for (idx, e) in missing {
        eprintln!(
            "TRUST-WALLA-PROBE B def_index={idx} def={} no-mono-instance-in-this-crate",
            e.def_path
        );
    }
    let total: usize = counts.values().sum();
    eprintln!(
        "TRUST-WALLA-PROBE B summary stashed_bodies={} bodies_with_instances={} distinct_instances={total}",
        entries.len(),
        counts.len()
    );
}

/// The instance-kind label, a local copy of `rustc_monomorphize::trust_instance_census`'s
/// (private there; copied rather than adding a crate edge) so rows read the same in both.
fn instance_kind_label(kind: ty::InstanceKind<'_>) -> &'static str {
    use ty::{InstanceKind, ShimKind};
    match kind {
        InstanceKind::Item(_) => "item",
        InstanceKind::LlvmIntrinsic(_) => "llvm-intrinsic",
        InstanceKind::Intrinsic(_) => "intrinsic",
        InstanceKind::Virtual(..) => "virtual",
        InstanceKind::Shim(shim) => match shim {
            ShimKind::VTable(_) => "shim-vtable",
            ShimKind::Reify(..) => "shim-reify",
            ShimKind::FnPtr(..) => "shim-fn-ptr",
            ShimKind::ClosureOnce { .. } => "shim-closure-once",
            ShimKind::ConstructCoroutineInClosure { .. } => "shim-construct-coroutine",
            ShimKind::ThreadLocal(_) => "shim-thread-local",
            ShimKind::FutureDropPoll(..) => "shim-future-drop-poll",
            ShimKind::DropGlue(..) => "shim-drop-glue",
            ShimKind::Clone(..) => "shim-clone",
            ShimKind::FnPtrAsPtr(..) => "shim-fn-ptr-addr",
            ShimKind::FnPtrFromPtr(..) => "shim-fn-ptr-from",
            ShimKind::AsyncDropGlueCtor(..) => "shim-async-drop-ctor",
            ShimKind::AsyncDropGlue(..) => "shim-async-drop",
        },
    }
}

/// A refusal's class, with the unbounded payload of `OracleRefused` dropped so the class
/// table stays a closed set (`LaneRefused` carries a `&'static str`, which is bounded).
/// Step 2 increment 3's payload-carrying variants (`UnsignableCallee` names a declaration,
/// `NotSelfContained` a finding, `CalleeMisresolved` an edge) are mapped the same way.
fn refusal_class(refusal: &crate::InstanceRefusal) -> String {
    match refusal {
        crate::InstanceRefusal::OracleRefused(_) => "OracleRefused".to_string(),
        crate::InstanceRefusal::UnsignableCallee(_) => "UnsignableCallee".to_string(),
        crate::InstanceRefusal::NotSelfContained(_) => "NotSelfContained".to_string(),
        crate::InstanceRefusal::CalleeMisresolved(_) => "CalleeMisresolved".to_string(),
        other => format!("{other:?}"),
    }
}

/// Channel C (`TRUST-WALLA-PROBE C`, after `codegen_crate`): the step-2 scoreboard.
///
/// Every `MonoItem::Fn` the collector handed codegen, deduplicated across codegen units, is run
/// through the instance-keyed producer's ROUTING RULE and, when the route is the source-first
/// one, through the producer itself (`trust_ir_of_instance_with_facts`). Only `route=thir
/// result=ok(..)` rows are coverage of "trust-ir is the only codegen input"
/// (docs/plans/2026-09-29-trust-ir-sole-compile-path.md, step 2), and a producer admission is
/// `ok` only if crate assembly also took the body and the probe sees no erasure or abstraction
/// in it — otherwise the row says `assembly-refused(<why>)`, `erased(<what>)` or
/// `abstracted(<what>)` (see [`assembly_state`]). `route=mir` rows
/// are upstream items and rustc-synthesized shims, which today have no source-first producer;
/// the probe does NOT run the MIR-derived producer for them (R-2 of that plan: MIR is not a
/// production input), and reports them as `result=residue` — the population step 2's
/// increments 4 and 6 must retire.
///
/// WHAT `ok` MEANS since step 2 increment 3: the producer returned a SELF-CONTAINED instance
/// module (`trust_ir_of_instance_body`: the body plus one signed declaration per callee edge,
/// validated standalone), so `functions=` is `1 + n` for a body with `n` callees. It does NOT
/// mean the codegen-time assembler will splice it: table-freedom, fn-pointer-freedom and the
/// per-edge checks are decided there (`rustc_codegen_trust_cg`'s `instance_assembly`), so a
/// table-bearing instance still prints `ok` here.
///
/// WHAT `refused(..)` covers since 2026-10-01: the instance lane's own gate (the frozen
/// `instance_admission`) refuses, before assembly is asked, the abstractions it can name in the
/// lowering — an elided drop (`LaneRefused("drop-bearing")`), a tag-free opaque collapse
/// (`LaneRefused("opaque collapse")`) and any `undef` (`LaneRefused("undef placeholder")`) —
/// because no seam differential judges an instance body yet (D17; a defect, docs/STATUS.md). So a
/// monomorphic body that the handoff splices with one of those abstractions reads `refused(..)`
/// here, not `abstracted(..)`; `abstracted(..)` is left to what the published body shows that
/// the instance lowering did not report.
///
/// Like channels A and B it installs nothing and changes no emitted code.
fn channel_c(tcx: TyCtxt<'_>, filter: &str) {
    let partitions = tcx.collect_and_partition_mono_items(());
    let mut seen: HashSet<MonoItem<'_>> = HashSet::new();
    let mut rows: Vec<(String, String)> = Vec::new(); // (symbol, rendered row)
    let mut non_fn = 0usize;
    let (mut thir_ok, mut refused, mut residue, mut panics) = (0usize, 0usize, 0usize, 0usize);
    let (mut assembly_refused, mut erased, mut abstracted) = (0usize, 0usize, 0usize);
    let mut not_conserved = 0usize;
    let mut classes: HashMap<String, usize> = HashMap::new();
    let mut drop_counts: HashMap<&'static str, usize> = HashMap::new();
    // Trust (step 2 increment 4c): the drop-glue oracle's tallies (`glue=` column).
    let mut glue_counts: HashMap<&'static str, usize> = HashMap::new();
    let (mut glue_misses, mut glue_extras) = (0usize, 0usize);
    let mut glue_details: Vec<(String, String)> = Vec::new();
    // Trust (step 2 increment 6, step 6.2): the rmeta column's tallies.
    let mut rmeta_counts: HashMap<&'static str, usize> = HashMap::new();
    for cgu in partitions.codegen_units {
        for item in cgu.items().keys() {
            if !seen.insert(*item) {
                continue;
            }
            let MonoItem::Fn(inst) = item else {
                non_fn += 1;
                continue;
            };
            let def_path =
                rustc_middle::ty::print::with_no_trimmed_paths!(tcx.def_path_str(inst.def_id()));
            if filter != "*" && !def_path.contains(filter) {
                continue;
            }
            let symbol = tcx.symbol_name(*inst).name.to_string();
            let kind = instance_kind_label(inst.def);
            let local = inst.def_id().is_local();
            // Trust (S3): the producer's OWN shape facts, not a copy of them that a new field can
            // miss. Before S3 neither knew a constructor, so a local ctor instance (aterm-uds:
            // `ChildStdio::Fd`, `BootClock`) routed to THIR and `thir_body` ICEd on it; it now
            // reads `route=pre-route result=refused(NoSourceBody("ctor"))`.
            let facts = crate::instance_shape_facts(tcx, *inst);
            let (route, result) = match crate::instance_route(facts) {
                Err(refusal) => {
                    let class = refusal_class(&refusal);
                    refused += 1;
                    *classes.entry(class.clone()).or_insert(0) += 1;
                    ("pre-route", format!("refused({class})"))
                }
                Ok(crate::InstanceRoute::Mir) => {
                    residue += 1;
                    *classes.entry("residue-mir-route".to_string()).or_insert(0) += 1;
                    ("mir", "residue".to_string())
                }
                Ok(crate::InstanceRoute::Thir) => {
                    let produced = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                        crate::trust_ir_of_instance_with_facts(tcx, *inst).map(
                            |(module, input, facts)| {
                                let state = assembly_state(tcx, *inst, facts);
                                (module, input, state)
                            },
                        )
                    }));
                    let result = match produced {
                        Ok(Ok((module, input, AssemblyState::Spliced))) => {
                            thir_ok += 1;
                            format!("ok(input={input:?},functions={})", module.functions.len())
                        }
                        Ok(Ok((_, _, AssemblyState::Erased(what)))) => {
                            erased += 1;
                            *classes.entry(format!("erased({what})")).or_insert(0) += 1;
                            format!("erased({what})")
                        }
                        Ok(Ok((_, _, AssemblyState::NotConserved(what)))) => {
                            not_conserved += 1;
                            *classes.entry(format!("not-conserved({what})")).or_insert(0) += 1;
                            format!("not-conserved({what})")
                        }
                        Ok(Ok((_, _, AssemblyState::Abstracted(what)))) => {
                            abstracted += 1;
                            *classes.entry(format!("abstracted({what})")).or_insert(0) += 1;
                            format!("abstracted({what})")
                        }
                        Ok(Ok((_, _, AssemblyState::Refused(why)))) => {
                            assembly_refused += 1;
                            *classes.entry(format!("assembly-refused({why})")).or_insert(0) += 1;
                            format!("assembly-refused({why})")
                        }
                        Ok(Err(refusal)) => {
                            let class = refusal_class(&refusal);
                            refused += 1;
                            *classes.entry(class.clone()).or_insert(0) += 1;
                            format!("refused({class})")
                        }
                        Err(_) => {
                            panics += 1;
                            "PANIC-in-probe".to_string()
                        }
                    };
                    ("thir", result)
                }
            };
            // Trust (step 2 increment 4b): the drop column — what the producer did with the
            // definition's drops, as the effect-conservation gate judged them against rustc's
            // drop elaboration (`drop_oracle.rs`), whatever the row's result.
            let drops = if local && matches!(inst.def, ty::InstanceKind::Item(_)) {
                let d = drop_column(tcx, inst.def_id().index.as_u32());
                *drop_counts.entry(d).or_insert(0) += 1;
                format!(" drops={d}")
            } else {
                String::new()
            };
            // Trust (step 2 increment 4c): the glue column — the synthesized glue of a drop-glue
            // item against rustc's own drop shim (`drop_glue_oracle`: the events compared, the
            // body executed per variant). A test oracle; nothing here is installed.
            let glue = if crate::drop_glue::glue_instance_ty(*inst).is_some() {
                let verdict = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                    crate::drop_glue_oracle::check_glue(tcx, *inst)
                }));
                let (label, detail): (&'static str, Option<String>) = match verdict {
                    Ok(crate::drop_glue_oracle::GlueOracleVerdict::Refused { class, detail }) => (
                        if class == "upstream-body" {
                            "refused-upstream-body"
                        } else {
                            "refused-shape"
                        },
                        Some(detail),
                    ),
                    Ok(crate::drop_glue_oracle::GlueOracleVerdict::Checked {
                        comparison,
                        executed,
                    }) => {
                        glue_misses += comparison.misses.len();
                        glue_extras += comparison.extras.len();
                        match (comparison.agrees(), &executed) {
                            (true, Ok(_)) => ("match", None),
                            _ => (
                                "differs",
                                Some(format!(
                                    "misses={:?} extras={:?} order_agrees={} executed={:?}",
                                    comparison.misses,
                                    comparison.extras,
                                    comparison.order_agrees,
                                    executed
                                )),
                            ),
                        }
                    }
                    Ok(crate::drop_glue_oracle::GlueOracleVerdict::OracleFailed(why)) => {
                        ("oracle-failed", Some(why))
                    }
                    Err(_) => {
                        panics += 1;
                        ("panic", None)
                    }
                };
                *glue_counts.entry(label).or_insert(0) += 1;
                if let Some(detail) = detail {
                    glue_details.push((symbol.clone(), format!("{label}: {detail}")));
                }
                format!(" glue={label}")
            } else {
                String::new()
            };
            // Trust (step 2 increment 6, step 6.2): the rmeta column — what this compilation
            // finds in a dependency's rmeta for an UPSTREAM plain item: a trust-ir entry that
            // decodes and checks (`entry(..)`), one that does not (`entry-refused(<check>)`), the
            // producing crate's recorded reason it has none (`absent(<class>)`), or no header at
            // all (`no-header`: compiled without the producer). Read-only; nothing is admitted.
            let rmeta = if !local && matches!(inst.def, ty::InstanceKind::Item(_)) {
                let (class, column) = crate::rmeta_entry::upstream_entry_column(tcx, inst.def_id());
                *rmeta_counts.entry(class).or_insert(0) += 1;
                format!(" rmeta={column}")
            } else {
                String::new()
            };
            rows.push((
                symbol.clone(),
                format!(
                    "TRUST-WALLA-PROBE C sym={symbol} kind={kind} local={local} route={route} \
                     result={result}{drops}{glue}{rmeta} def={def_path} args={:?}",
                    inst.args
                ),
            ));
        }
    }
    rows.sort();
    for (_, row) in &rows {
        eprintln!("{row}");
    }
    glue_details.sort();
    for (symbol, detail) in &glue_details {
        eprintln!("TRUST-WALLA-PROBE C glue-detail sym={symbol} {detail}");
    }
    eprintln!(
        "TRUST-WALLA-PROBE C summary fn_items={} thir_ok={thir_ok} \
         assembly_refused={assembly_refused} erased={erased} not_conserved={not_conserved} \
         abstracted={abstracted} \
         refused={refused} \
         residue={residue} panics={panics} non_fn={non_fn} \
         drops_placed={} drops_elided={} drops_mismatch={} drops_unchecked={} \
         glue_match={} glue_differs={} glue_refused={} glue_oracle_failed={} glue_misses={} \
         glue_extras={} rmeta_entry={} rmeta_entry_refused={} rmeta_absent={} rmeta_no_header={}",
        rows.len(),
        drop_counts.get("placed").copied().unwrap_or(0),
        drop_counts.get("elided").copied().unwrap_or(0),
        drop_counts.get("mismatch").copied().unwrap_or(0),
        drop_counts.get("unchecked").copied().unwrap_or(0),
        glue_counts.get("match").copied().unwrap_or(0),
        glue_counts.get("differs").copied().unwrap_or(0),
        glue_counts.get("refused-upstream-body").copied().unwrap_or(0)
            + glue_counts.get("refused-shape").copied().unwrap_or(0),
        glue_counts.get("oracle-failed").copied().unwrap_or(0),
        glue_misses,
        glue_extras,
        rmeta_counts.get("entry").copied().unwrap_or(0),
        rmeta_counts.get("entry-refused").copied().unwrap_or(0),
        rmeta_counts.get("absent").copied().unwrap_or(0),
        rmeta_counts.get("no-header").copied().unwrap_or(0),
    );
    let mut classes: Vec<_> = classes.into_iter().collect();
    classes.sort();
    for (class, count) in classes {
        eprintln!("TRUST-WALLA-PROBE C class {class}={count}");
    }
}

/// Channel C: what crate assembly did with the definition behind a `route=thir` instance the
/// instance-keyed producer ADMITTED.
///
/// `route=thir result=ok` used to mean only "the instance lane produced a Module". That is not
/// what F1 compiles: F1 selects a body from the ASSEMBLED crate module, so a producer `ok`
/// whose body crate assembly refused (an unsignable callee declaration, a ZST callable
/// stand-in, a pending const) or whose definition is generic (the analysis-time crate module
/// holds identity bodies only; since plan step 2 increment 3 the codegen-time assembler appends
/// a generic instance's body to a private copy of it, which this probe cannot see, so the row
/// stays `assembly-refused(generic-instance)`) was counted as coverage F1 does not have. Measured 2026-10-01 on aterm-uds (aterm 4ba80b2b6, stage1 main
/// f5dd1d805a): of 127 `route=thir result=ok` rows, 102 were spliced, 24 were never
/// spliced (12 ZST callable stand-ins, 4 unspliceable global shapes, 7 unsignable callee
/// declarations, 1 pending const) and 1 (`InheritStrip::apply`) was spliced with its `fcntl`
/// loop erased. `ok` now requires all of:
///
///   * the definition is not generic (the published crate module holds identity bodies only);
///   * the published crate module carries a BODY for it, produced by this producer;
///   * that body keeps every loop NEST rustc's own MIR has: fewer cyclic strongly connected
///     components in the spliced function than in the instance's MIR means a loop was lowered
///     by erasure — the wave-ER `for` summary's failure mode (`ret` for `for fd in lo..hi {
///     close(fd) }`), and a SECOND loop erased beside a faithful one (a field-store RHS lane,
///     `reset_and_close_counted` in the 2026-10-01 review) — reported as `erased(loop)`;
///   * and the body is not one of the abstractions this probe can see, reported as
///     `abstracted(<what>)` (`+`-joined when several apply):
///       - `drop`: the instance's MIR drops a value that needs dropping and the body has no
///         `Inst::Drop` — the producer models no drop yet (step 2 increment 4), so the
///         destructor never runs (docs/KNOWN_HAZARDS.md, OPEN 2026-10-01, drop elision);
///       - `undef`: the body computes with an `Inst::Undef` (a havoc lane: a whole-value
///         field store of a non-plain value, an Option-discriminant copy, a nondeterministic
///         loop exit) — a model, not the program;
///       - `opaque-lane`: the body loads, stores or rebuilds a struct the producer registered
///         WITHOUT a layout (the `struct_ty_rmw_opaque` build, whose `Vec`/`String`/data-enum
///         fields are `()` placeholders), or the lowering reported `opaque_collapse` (a live
///         value took a placeholder — that build's `()` lanes, an `Option` field modelled as
///         its discriminant `bool` inside a struct that does carry a layout, a wave-EL data-enum
///         lane) — a field store to such a lane stores nothing, or only a discriminant.
///
///   * and (since the effect-conservation gate, 2026-10-01) the gate's verdict for the
///     definition is CONSERVED: a call, a store through an escaping pointer, a panic check, asm
///     or a yield of the MIR census that the spliced body does not carry reads
///     `not-conserved(<what>)`, and the gate's abstraction lanes join the probe's own under
///     `abstracted(..)` ([`with_conservation_verdict`]). So `ok` here implies the gate's
///     CONSERVED, and the probe's own readings (an erased loop, `opaque_collapse`, a layout-less
///     struct lane) can make it stricter than the trust-cg frontend's admission, never looser.
///
///     On the THIR route the instance lane refuses a body that sets `opaque_collapse` or holds
///     an `undef`, and every drop-bearing one, before this is asked (see [`channel_c`]), so
///     `facts.opaque_collapse` is `false` for every row that reaches here; it is still read, from
///     the frozen route's own report, rather than assumed.
///
///     What it CANNOT see, so `ok` is still not a faithfulness certificate: a WRONG value stored
///     by a faithful store, a panic check's condition, and effect ORDER (the `DerefMut` chain
///     hazard). Under `-O`,
///     `instance_mir` has inlined
///     callees, so their loops and drops can read as `erased(loop)`/`abstracted(drop)` here —
///     conservative, never `ok`.
///
/// Identification is by the assembler's own naming: since WS5.2 a spliced body is NAMED by its
/// link-time symbol, `tcx.symbol_name` of its identity instance (`crate::link_symbol`), which a
/// non-generic local instance is, so the probe resolves exactly that one injective name. A
/// display path is not identity and is never consulted (it was, with an exact collision name,
/// while the assembler named bodies by display path). Measurement only: nothing here installs
/// or changes code.
enum AssemblyState {
    Spliced,
    Erased(&'static str),
    /// Trust (effect conservation, 2026-10-01): the gate (`effect_conservation`) found an effect
    /// of the instance's MIR missing from the spliced body: `call`, `store`, `asm`, … joined by
    /// `+`, or `unchecked` when the gate never ran. Reported before any abstraction.
    NotConserved(String),
    Abstracted(String),
    Refused(String),
}

/// What channel C reads off a spliced function (see [`assembly_state`]).
struct SplicedShape {
    loop_nests: usize,
    drops: usize,
    has_undef: bool,
    touches_layoutless_struct: bool,
}

fn spliced_shape(module: &trust_ir::Module, f: &trust_ir::Function) -> SplicedShape {
    use trust_ir::{Inst, Ty};
    let layoutless = |ty: &Ty| {
        matches!(ty, Ty::Struct(sid)
            if module.struct_def(*sid).is_some_and(|d| d.size.is_none()))
    };
    let (mut drops, mut has_undef, mut touches_layoutless_struct) = (0usize, false, false);
    for node in f.blocks.iter().flat_map(|b| b.body.iter()) {
        match &node.inst {
            Inst::Drop { .. } => drops += 1,
            Inst::Undef { ty } => {
                has_undef = true;
                touches_layoutless_struct |= layoutless(ty);
            }
            Inst::Load { ty, .. }
            | Inst::Store { ty, .. }
            | Inst::InsertField { ty, .. }
            | Inst::ExtractField { ty, .. }
            | Inst::Const { ty, .. } => touches_layoutless_struct |= layoutless(ty),
            _ => {}
        }
    }
    SplicedShape {
        loop_nests: cyclic_scc_count(&ir_successors(f)),
        drops,
        has_undef,
        touches_layoutless_struct,
    }
}

/// The verdict, from the spliced function's shape and the instance MIR's loop nests and
/// needs-drop `Drop` terminators. Pure, so the unit tests pin it without a `TyCtxt`.
fn classify_spliced(
    shape: &SplicedShape,
    mir_loop_nests: usize,
    mir_drops: usize,
) -> AssemblyState {
    if shape.loop_nests < mir_loop_nests {
        return AssemblyState::Erased("loop");
    }
    let mut what: Vec<&str> = Vec::new();
    if mir_drops > shape.drops {
        what.push("drop");
    }
    if shape.has_undef {
        what.push("undef");
    }
    if shape.touches_layoutless_struct {
        what.push("opaque-lane");
    }
    if what.is_empty() { AssemblyState::Spliced } else { AssemblyState::Abstracted(what.join("+")) }
}

fn assembly_state<'tcx>(
    tcx: TyCtxt<'tcx>,
    inst: ty::Instance<'tcx>,
    facts: crate::InstanceLoweringFacts,
) -> AssemblyState {
    let def_id = inst.def_id();
    if !def_id.is_local() {
        return AssemblyState::Refused("not-local".to_string());
    }
    // Genericity of the TYPECK ROOT, not of the def: a closure's own generics carry the
    // synthetic kind/signature/upvar parameters, so every closure "requires monomorphization"
    // by that test, while the crate module splices a closure of a non-generic fn as an identity
    // body like any other.
    if tcx.generics_of(tcx.typeck_root_def_id(def_id)).requires_monomorphization(tcx) {
        return AssemblyState::Refused("generic-instance".to_string());
    }
    // Trust (WS5.2): the body's link-time symbol, the name the assembler gave it.
    let symbol = tcx.symbol_name(inst).name.to_string();
    let spliced = crate::crate_module::with_published_crate_module(tcx.sess, |published| {
        let published = match published {
            Ok(p) => p,
            Err(_) => return Err("unpublished".to_string()),
        };
        let Some(id) = published.resolve_symbol(&symbol) else {
            return Err("not-spliced".to_string());
        };
        match published.module().function_by_id(id) {
            Some(f) if !f.is_declaration() && f.producer == Some(trust_ir::Producer::TRust) => {
                let mut shape = spliced_shape(published.module(), f);
                shape.touches_layoutless_struct |= facts.opaque_collapse;
                Ok(shape)
            }
            _ => Err("not-spliced".to_string()),
        }
    });
    match spliced {
        Err(why) => AssemblyState::Refused(why),
        Ok(shape) => {
            let body = tcx.instance_mir(inst.def);
            let mir_succs: Vec<Vec<usize>> = body
                .basic_blocks
                .iter()
                .map(|bb| bb.terminator().successors().map(|s| s.as_usize()).collect())
                .collect();
            // The definition is not generic (checked above), so its MIR types are concrete.
            let typing_env = ty::TypingEnv::fully_monomorphized();
            let mir_drops = body
                .basic_blocks
                .iter()
                .filter(|bb| match &bb.terminator().kind {
                    rustc_middle::mir::TerminatorKind::Drop { place, .. } => {
                        place.ty(&body.local_decls, tcx).ty.needs_drop(tcx, typing_env)
                    }
                    _ => false,
                })
                .count();
            let state = classify_spliced(&shape, cyclic_scc_count(&mir_succs), mir_drops);
            with_conservation_verdict(tcx, def_id.index.as_u32(), state)
        }
    }
}

/// Trust (step 2 increment 4b): channel C's drop column for a local definition, read from the
/// effect-conservation verdict (measurement only):
///
/// * `placed` — the producer planned the body's drops and the gate found them equal to rustc's
///   drop elaboration (no drop tag);
/// * `elided` — a drop the program performs is missing (`abstracted(drop)`);
/// * `mismatch` — the body carries a drop the program does not perform, or a drop not where the
///   producer recorded it (`not-conserved(drop)`);
/// * `none` — no drop either way;
/// * `unchecked` — the gate did not run or has no verdict for the definition.
fn drop_column(tcx: TyCtxt<'_>, def_index: u32) -> &'static str {
    tcx.sess.with_trust_compiler_state::<crate::effect_conservation::ConservationVerdicts, _>(|v| {
        if !v.ran() {
            return "unchecked";
        }
        let Some(b) = v.verdict(def_index) else { return "unchecked" };
        let has = |k: crate::effect_conservation::TagKind| b.tags.iter().any(|t| t.kind == k);
        if has(crate::effect_conservation::TagKind::NotConserved(
            crate::effect_conservation::Effect::Drop,
        )) {
            "mismatch"
        } else if has(crate::effect_conservation::TagKind::Abstracted(
            crate::effect_conservation::Lane::Drop,
        )) {
            "elided"
        } else if b.drop_claim_live.is_some_and(|n| n > 0) {
            "placed"
        } else {
            "none"
        }
    })
}

/// Trust (effect conservation, 2026-10-01): combine the probe's own reading with the
/// conservation gate's verdict for the same definition. An erased loop stays first; a gate
/// `not-conserved(..)` finding comes next; the gate's abstraction lanes join the probe's (the
/// two readings overlap by design, and a lane either one sees is reported). A body the gate
/// never judged is `not-conserved(unchecked)`: F1 refuses it, so channel C must not call it `ok`.
fn with_conservation_verdict(
    tcx: TyCtxt<'_>,
    def_index: u32,
    state: AssemblyState,
) -> AssemblyState {
    if matches!(state, AssemblyState::Erased(_) | AssemblyState::Refused(_)) {
        return state;
    }
    let classes: Option<Vec<String>> = tcx
        .sess
        .with_trust_compiler_state::<crate::effect_conservation::ConservationVerdicts, _>(|v| {
            if !v.ran() {
                return None;
            }
            Some(v.verdict(def_index).map(|b| b.classes()).unwrap_or_else(|| {
                vec![
                    crate::effect_conservation::TagKind::NotConserved(
                        crate::effect_conservation::Effect::Census,
                    )
                    .label(),
                ]
            }))
        });
    let Some(classes) = classes else {
        return AssemblyState::NotConserved("unchecked".to_string());
    };
    let inner = |label: &str, prefix: &str| -> Option<String> {
        label.strip_prefix(prefix).and_then(|r| r.strip_suffix(')')).map(str::to_string)
    };
    let not_conserved: Vec<String> =
        classes.iter().filter_map(|c| inner(c, "not-conserved(")).collect();
    if !not_conserved.is_empty() {
        return AssemblyState::NotConserved(not_conserved.join("+"));
    }
    let mut lanes: Vec<String> = match &state {
        AssemblyState::Abstracted(what) => what.split('+').map(str::to_string).collect(),
        _ => Vec::new(),
    };
    for lane in classes.iter().filter_map(|c| inner(c, "abstracted(")) {
        if !lanes.contains(&lane) {
            lanes.push(lane);
        }
    }
    // The probe's fixed order: drop, destructor, undef, opaque-lane, union-lane,
    // enum-param-lane.
    let order = |l: &String| match l.as_str() {
        "drop" => 0,
        "destructor" => 1,
        "undef" => 2,
        "opaque-lane" => 3,
        "union-lane" => 4,
        "enum-param-lane" => 5,
        _ => 6,
    };
    lanes.sort_by_key(order);
    if lanes.is_empty() {
        AssemblyState::Spliced
    } else {
        AssemblyState::Abstracted(lanes.join("+"))
    }
}

/// `f`'s CFG as successor lists over block POSITIONS: the terminators' targets. An edge to a
/// block the function does not define is ignored (validation refuses such a module before
/// publication); a terminator this walk does not enumerate contributes no edge, so the loop
/// count can only err LOW — which reads as `erased`, never as `ok`.
fn ir_successors(f: &trust_ir::Function) -> Vec<Vec<usize>> {
    use trust_ir::Inst;
    let index: HashMap<trust_ir::BlockId, usize> =
        f.blocks.iter().enumerate().map(|(i, b)| (b.id, i)).collect();
    f.blocks
        .iter()
        .map(|b| {
            let mut out = Vec::new();
            for node in &b.body {
                match &node.inst {
                    Inst::Br { target, .. } => out.push(*target),
                    Inst::CondBr { then_target, else_target, .. } => {
                        out.push(*then_target);
                        out.push(*else_target);
                    }
                    Inst::Switch { default, cases, .. } => {
                        out.push(*default);
                        out.extend(cases.iter().map(|c| c.target));
                    }
                    Inst::Invoke { normal_dest, unwind_dest, .. } => {
                        out.push(*normal_dest);
                        out.push(*unwind_dest);
                    }
                    _ => {}
                }
            }
            out.into_iter().filter_map(|t| index.get(&t).copied()).collect()
        })
        .collect()
}

/// Does `f`'s CFG contain a cycle?
#[cfg(test)]
fn ir_function_is_cyclic(f: &trust_ir::Function) -> bool {
    cyclic_scc_count(&ir_successors(f)) > 0
}

/// How many LOOP NESTS a CFG has: strongly connected components that contain a cycle (more
/// than one node, or a self-edge). A nest of loops is one component and sequential loops are
/// separate ones, in rustc's MIR and in trust-ir alike, so the two counts are comparable where
/// a block-level "is there any cycle" is not: it called a body with one faithful loop and one
/// erased loop `ok`. Iterative Tarjan; out-of-range successors are ignored.
fn cyclic_scc_count(succs: &[Vec<usize>]) -> usize {
    let n = succs.len();
    const UNSEEN: usize = usize::MAX;
    let mut index = vec![UNSEEN; n];
    let mut low = vec![0usize; n];
    let mut on_stack = vec![false; n];
    let mut stack: Vec<usize> = Vec::new();
    let mut next_index = 0usize;
    let mut count = 0usize;
    for root in 0..n {
        if index[root] != UNSEEN {
            continue;
        }
        // (node, next successor position)
        let mut work: Vec<(usize, usize)> = vec![(root, 0)];
        index[root] = next_index;
        low[root] = next_index;
        next_index += 1;
        stack.push(root);
        on_stack[root] = true;
        while let Some(&(v, pos)) = work.last() {
            let edges = &succs[v];
            if pos < edges.len() {
                if let Some(top) = work.last_mut() {
                    top.1 += 1;
                }
                let w = edges[pos];
                if w >= n {
                    continue;
                }
                if index[w] == UNSEEN {
                    index[w] = next_index;
                    low[w] = next_index;
                    next_index += 1;
                    stack.push(w);
                    on_stack[w] = true;
                    work.push((w, 0));
                } else if on_stack[w] {
                    low[v] = low[v].min(index[w]);
                }
                continue;
            }
            work.pop();
            if let Some(&(parent, _)) = work.last() {
                low[parent] = low[parent].min(low[v]);
            }
            if low[v] == index[v] {
                let mut members = 0usize;
                let mut self_edge = false;
                loop {
                    let w = stack.pop().expect("Tarjan stack holds the component root");
                    on_stack[w] = false;
                    members += 1;
                    self_edge |= succs[w].contains(&w);
                    if w == v {
                        break;
                    }
                }
                if members > 1 || self_edge {
                    count += 1;
                }
            }
        }
    }
    count
}

/// One channel-B measurement, per codegen-demanded mono instance.
fn probe_mono_instance<'tcx>(
    tcx: TyCtxt<'tcx>,
    def: LocalDefId,
    inst: ty::Instance<'tcx>,
    entry: &StashEntry,
) {
    let typing_env = ty::TypingEnv::fully_monomorphized();
    let kind_item = matches!(inst.def, ty::InstanceKind::Item(_));
    let rederived = rederive_abi_sig_at_instance(tcx, def, inst.args);
    let (abi_rederive, lowering, abi_vs_incumbent) = match &rederived {
        Err(e) => (format!("REDERIVE-ERR({e})"), "-".to_string(), "-".to_string()),
        Ok((inputs, output)) => {
            let lowering = match to_mir::lower_ir_to_mir(
                tcx,
                def,
                &entry.module,
                &entry.callees,
                to_mir::SigSource::Provided(inputs.clone(), *output),
                &entry.enum_fold_switch_blocks,
            ) {
                Ok(l) => {
                    let derived_ok = abi_exact(inputs, *output, &l.body).is_ok();
                    format!(
                        "ok(blocks={},derived_abi_selfcheck={derived_ok})",
                        l.body.basic_blocks.len()
                    )
                }
                Err(e) => format!("ERR({})", e.reason),
            };
            let incumbent = match inst.try_instantiate_mir_and_normalize_erasing_regions(
                tcx,
                typing_env,
                ty::EarlyBinder::bind(tcx, tcx.optimized_mir(def.to_def_id()).clone()),
            ) {
                Ok(b) => match abi_exact(inputs, *output, &b) {
                    Ok(()) => "exact".to_string(),
                    Err(e) => format!("MISMATCH({e})"),
                },
                Err(e) => format!("NORMALIZATION-ERROR({e:?})"),
            };
            (String::from("ok"), lowering, incumbent)
        }
    };
    eprintln!(
        "TRUST-WALLA-PROBE B def={} inst_args={:?} kind_item={kind_item} \
         abi_rederive_at_instance={abi_rederive} derived_lowering={lowering} \
         rederived_abi_vs_instantiated_optimized={abi_vs_incumbent}",
        entry.def_path, inst.args
    );
}

#[cfg(test)]
mod assembly_state_tests {
    use trust_ir::{Block, BlockId, FuncId, FuncTy, Function, Inst, InstrNode, Module, ValueId};

    use super::{
        AssemblyState, SplicedShape, classify_spliced, cyclic_scc_count, ir_function_is_cyclic,
        ir_successors,
    };

    /// A function whose blocks are `(id, successors)`, in the given ORDER — the order is the
    /// point: the producer creates a join or a loop exit before the arm that branches to it.
    fn function(blocks: &[(u32, &[u32])]) -> Function {
        let mut module = Module::new("cyclic_probe");
        let ty = module
            .add_func_type(FuncTy {
                params: Vec::new(),
                returns: Vec::new(),
                is_vararg: false,
                abi: None,
            })
            .expect("Module::add_func_type: test fixture");
        let mut f = Function::new(FuncId::new(0), "probe", ty, BlockId::new(blocks[0].0));
        for &(id, succs) in blocks {
            let mut block = Block::new(BlockId::new(id));
            let terminator = match succs {
                [] => Inst::Return { values: Vec::new() },
                [t] => Inst::Br { target: BlockId::new(*t), args: Vec::new() },
                [t, e] => Inst::CondBr {
                    cond: ValueId::new(0),
                    then_target: BlockId::new(*t),
                    then_args: Vec::new(),
                    else_target: BlockId::new(*e),
                    else_args: Vec::new(),
                },
                _ => panic!("at most two successors in these fixtures"),
            };
            block.body.push(InstrNode::new(terminator));
            f.blocks.push(block);
        }
        f
    }

    /// The measured erasure: `close_range` lowered to a single `ret`.
    #[test]
    fn an_erased_loop_is_acyclic() {
        assert!(!ir_function_is_cyclic(&function(&[(0, &[])])));
    }

    /// An `if`/`else` whose JOIN was created first (bb1) — both arms branch to a LOWER-numbered
    /// block, which a numeric "back-edge" shortcut would call a loop.
    #[test]
    fn a_join_numbered_before_its_arms_is_not_a_loop() {
        let f = function(&[(0, &[2, 3]), (1, &[]), (2, &[1]), (3, &[1])]);
        assert!(!ir_function_is_cyclic(&f));
    }

    /// The wave-FR range shape the fixed producer emits: header bb1, exit bb2, body bb3.
    #[test]
    fn a_range_loop_is_cyclic() {
        let f = function(&[(0, &[1]), (1, &[3, 2]), (2, &[]), (3, &[1])]);
        assert!(ir_function_is_cyclic(&f));
    }

    /// A self-loop, and a cycle only reachable through the second successor.
    #[test]
    fn every_successor_edge_is_followed() {
        assert!(ir_function_is_cyclic(&function(&[(0, &[0])])));
        let f = function(&[(0, &[1, 2]), (1, &[]), (2, &[3]), (3, &[2])]);
        assert!(ir_function_is_cyclic(&f));
    }

    /// `Switch` and `Invoke` edges count, not only `Br`/`CondBr`.
    #[test]
    fn switch_and_invoke_edges_count() {
        // bb0 --switch default--> bb1 --invoke normal--> bb0; the unwind edge leaves to bb2.
        let mut f = function(&[(0, &[]), (1, &[]), (2, &[])]);
        f.blocks[0].body[0] = InstrNode::new(Inst::Switch {
            value: ValueId::new(0),
            default: BlockId::new(1),
            default_args: Vec::new(),
            cases: Vec::new(),
            exhaustive_enum_unreachable: false,
        });
        f.blocks[1].body[0] = InstrNode::new(Inst::Invoke {
            callee: FuncId::new(0),
            args: Vec::new(),
            normal_dest: BlockId::new(0),
            normal_args: Vec::new(),
            unwind_dest: BlockId::new(2),
        });
        assert!(ir_function_is_cyclic(&f));
    }

    /// Loop NESTS, not cycles: sequential loops count separately, a nest counts once, a
    /// self-edge is a loop, and straight-line code and joins are none.
    #[test]
    fn loop_nests_are_counted_as_cyclic_components() {
        let none = function(&[(0, &[2, 3]), (1, &[]), (2, &[1]), (3, &[1])]);
        assert_eq!(cyclic_scc_count(&ir_successors(&none)), 0);
        let self_loop = function(&[(0, &[0, 1]), (1, &[])]);
        assert_eq!(cyclic_scc_count(&ir_successors(&self_loop)), 1);
        // header bb1 (body bb2), then header bb3 (body bb4), exit bb5.
        let sequential =
            function(&[(0, &[1]), (1, &[2, 3]), (2, &[1]), (3, &[4, 5]), (4, &[3]), (5, &[])]);
        assert_eq!(cyclic_scc_count(&ir_successors(&sequential)), 2);
        // outer header bb1 -> inner header bb2 <-> bb3, inner exit back to bb1, outer exit bb4.
        let nested = function(&[(0, &[1]), (1, &[2, 4]), (2, &[3, 1]), (3, &[2]), (4, &[])]);
        assert_eq!(cyclic_scc_count(&ir_successors(&nested)), 1);
        // Raw successor lists: an out-of-range target is ignored, not a panic.
        assert_eq!(cyclic_scc_count(&[vec![1, 7], vec![0]]), 1);
    }

    fn shape(loop_nests: usize) -> SplicedShape {
        SplicedShape { loop_nests, drops: 0, has_undef: false, touches_layoutless_struct: false }
    }

    /// The 2026-10-01 review's `reset_and_close_counted`: one faithful `while` beside an
    /// erased `for` in a field-store RHS. "Any cycle" said `ok`; the nest count says erased.
    #[test]
    fn a_second_loop_erased_beside_a_faithful_one_is_erased() {
        assert!(matches!(classify_spliced(&shape(1), 2, 0), AssemblyState::Erased("loop")));
        assert!(matches!(classify_spliced(&shape(2), 2, 0), AssemblyState::Spliced));
        // More IR nests than MIR (a lowering that splits a region) is not an erasure.
        assert!(matches!(classify_spliced(&shape(3), 2, 0), AssemblyState::Spliced));
    }

    /// Each visible abstraction keeps a body out of `ok`, named, and joined in a fixed order.
    #[test]
    fn visible_abstractions_are_not_ok() {
        let name = |state: AssemblyState| match state {
            AssemblyState::Abstracted(what) => what,
            _ => String::from("<not abstracted>"),
        };
        // `guard_scope`: MIR drops a `Guard` with a side-effecting `Drop`; the body has no drop.
        assert_eq!(name(classify_spliced(&shape(0), 0, 1)), "drop");
        let undef = SplicedShape { has_undef: true, ..shape(0) };
        assert_eq!(name(classify_spliced(&undef, 0, 0)), "undef");
        let lane = SplicedShape { touches_layoutless_struct: true, ..shape(0) };
        assert_eq!(name(classify_spliced(&lane, 0, 0)), "opaque-lane");
        let all = SplicedShape { has_undef: true, touches_layoutless_struct: true, ..shape(0) };
        assert_eq!(name(classify_spliced(&all, 0, 2)), "drop+undef+opaque-lane");
        // A body that carries its drops (increment 4b) is not flagged for them.
        let dropped = SplicedShape { drops: 1, ..shape(0) };
        assert!(matches!(classify_spliced(&dropped, 0, 1), AssemblyState::Spliced));
        // An erased loop outranks every abstraction.
        assert!(matches!(classify_spliced(&all, 1, 2), AssemblyState::Erased("loop")));
    }
}

/// Trust (step 2 increment 4d, sub-step 4d.0a; docs/design/2026-09-29-step2-inc4-drops.md §5 and
/// §7.4, docs/design/2026-10-08-step2-inc4d-shims-plan.md §1(b)): THE MIR-DERIVED PRODUCER IS NO
/// CODEGEN ROUTE. `instance_route` sends every shim, and every upstream item, to
/// `InstanceRoute::Mir` (`a_synthesized_shim_routes_to_mir`). The codegen entry
/// (`trust_ir_of_instance_body`, pinned whole) answers that route `ThirUnavailable`; the
/// MIR-derived producer (`trust_ir_of_instance_from_mir`) is named only in
/// `trust_ir_of_instance_with_facts`, whose one caller is channel C's `Thir` arm, which runs it
/// only after the same pure `instance_route` answered `Thir`, so the producer has no run-time
/// caller; channel C's `Mir` arm records residue and runs no producer; the two `pub` wrappers that
/// could have run it on a shim from any dependent crate (`trust_ir_of_instance`,
/// `trust_ir_of_instance_explained`) are deleted (R-2); and every read of an instance's MIR and
/// every MIR-to-trust-ir lowering in the crate is pinned to its site. Read over every source file
/// of this crate, tests included (through `source_scan::crate_sources`, the crate's one whole-crate
/// walk), with comments and string literals blanked (`code_only`), and with only this module's own
/// block removed from this file, so its needles never count and code after it is read.
#[cfg(test)]
mod shim_route_tests {
    /// Rust source with every comment and every string, byte-string, raw-string and char
    /// literal blanked: a literal keeps its delimiters and loses its contents (`"…"` and
    /// `r#"…"#` become `""`, `'x'` becomes `' '`), and a comment becomes nothing; line breaks
    /// are kept. An unterminated literal or comment panics, so a mis-lex cannot silently swallow
    /// the rest of a file.
    fn code_only(src: &str) -> String {
        fn ident(b: u8) -> bool {
            b.is_ascii_alphanumeric() || b == b'_'
        }
        fn newlines(out: &mut Vec<u8>, span: &[u8]) {
            out.extend(span.iter().filter(|&&c| c == b'\n'));
        }
        let b = src.as_bytes();
        let mut out: Vec<u8> = Vec::with_capacity(b.len());
        let mut i = 0;
        while i < b.len() {
            let c = b[i];
            let next = b.get(i + 1).copied();
            if c == b'/' && next == Some(b'/') {
                i = b[i..].iter().position(|&c| c == b'\n').map_or(b.len(), |p| i + p);
                continue;
            }
            if c == b'/' && next == Some(b'*') {
                let (mut depth, mut j) = (0usize, i);
                loop {
                    assert!(j + 1 < b.len(), "unterminated block comment at byte {i}");
                    match (b[j], b[j + 1]) {
                        (b'/', b'*') => (depth, j) = (depth + 1, j + 2),
                        (b'*', b'/') => {
                            (depth, j) = (depth - 1, j + 2);
                            if depth == 0 {
                                break;
                            }
                        }
                        _ => j += 1,
                    }
                }
                newlines(&mut out, &b[i..j]);
                i = j;
                continue;
            }
            // A raw string, `r"…"`, `r#"…"#`, `br"…"` or `cr"…"`, whose prefix does not continue
            // an identifier (`r#ident` is a raw identifier: no `"` follows its `#`s).
            let after_ident = i > 0 && ident(b[i - 1]);
            if !after_ident && (c == b'r' || ((c == b'b' || c == b'c') && next == Some(b'r'))) {
                let open = if c == b'r' { i + 1 } else { i + 2 };
                let hashes = b[open..].iter().take_while(|&&h| h == b'#').count();
                if b.get(open + hashes) == Some(&b'"') {
                    let close: Vec<u8> = std::iter::once(b'"').chain(vec![b'#'; hashes]).collect();
                    let body = open + hashes + 1;
                    let end = b[body..]
                        .windows(close.len())
                        .position(|w| w == close.as_slice())
                        .map(|p| body + p + close.len())
                        .unwrap_or_else(|| panic!("unterminated raw string at byte {i}"));
                    out.extend_from_slice(b"\"\"");
                    newlines(&mut out, &b[i..end]);
                    i = end;
                    continue;
                }
            }
            if c == b'"' {
                let mut j = i + 1;
                loop {
                    assert!(j < b.len(), "unterminated string at byte {i}");
                    match b[j] {
                        // An escape, a line continuation included, skips the byte it escapes.
                        b'\\' => j += 2,
                        b'"' => break,
                        _ => j += 1,
                    }
                }
                out.extend_from_slice(b"\"\"");
                newlines(&mut out, &b[i..j]);
                i = j + 1;
                continue;
            }
            if c == b'\'' {
                // A char literal (`'x'`, `'"'`, `'\''`, `'\u{7b}'`), not a lifetime or a label.
                let end = if next == Some(b'\\') {
                    b.get(i + 3..)
                        .and_then(|rest| rest.iter().position(|&c| c == b'\''))
                        .map(|p| i + 3 + p + 1)
                } else {
                    src[i + 1..].chars().next().and_then(|ch| {
                        let close = i + 1 + ch.len_utf8();
                        (b.get(close) == Some(&b'\'')).then_some(close + 1)
                    })
                };
                if let Some(end) = end {
                    out.extend_from_slice(b"' '");
                    i = end;
                    continue;
                }
            }
            out.push(c);
            i += 1;
        }
        String::from_utf8(out).expect("blanking cuts only at ASCII bytes")
    }

    /// The byte range, `{` to `}`, of the brace-balanced block that opens at `open`.
    fn block_at(code: &str, open: usize) -> std::ops::Range<usize> {
        let b = code.as_bytes();
        assert_eq!(b[open], b'{', "a block opens at byte {open}");
        let mut depth = 0usize;
        for (k, &c) in b.iter().enumerate().skip(open) {
            match c {
                b'{' => depth += 1,
                b'}' => {
                    depth -= 1;
                    if depth == 0 {
                        return open..k + 1;
                    }
                }
                _ => {}
            }
        }
        panic!("the block at byte {open} is unbalanced")
    }

    /// Every fn item of blanked source `code`: its name and its body's byte range. The body
    /// opens at the first `{` outside parentheses and brackets after the name; a `;` there
    /// first is a bodyless declaration (`[u8; 4]` in a signature is not).
    fn fn_bodies(code: &str) -> Vec<(String, std::ops::Range<usize>)> {
        let b = code.as_bytes();
        let mut out = Vec::new();
        let mut from = 0;
        while let Some(rel) = code[from..].find("fn ") {
            let at = from + rel;
            from = at + 3;
            if at > 0 && (b[at - 1].is_ascii_alphanumeric() || b[at - 1] == b'_') {
                continue;
            }
            let name: String = code[at + 3..]
                .chars()
                .take_while(|c| c.is_ascii_alphanumeric() || *c == '_')
                .collect();
            if name.is_empty() {
                continue;
            }
            let mut depth = 0i32;
            let mut open = None;
            for (k, &c) in b.iter().enumerate().skip(at) {
                match c {
                    b'(' | b'[' => depth += 1,
                    b')' | b']' => depth -= 1,
                    b';' if depth == 0 => break,
                    b'{' if depth == 0 => {
                        open = Some(k);
                        break;
                    }
                    _ => {}
                }
            }
            if let Some(open) = open {
                out.push((name, block_at(code, open)));
            }
        }
        out
    }

    /// The body of the one fn named `name` in blanked source `code`.
    fn fn_text<'a>(code: &'a str, name: &str) -> &'a str {
        let found: Vec<_> = fn_bodies(code).into_iter().filter(|(n, _)| n == name).collect();
        assert_eq!(found.len(), 1, "exactly one fn `{name}`");
        &code[found[0].1.clone()]
    }

    /// Byte offsets of `ident` as a whole identifier in `code`, its definitions (`fn ident`)
    /// excluded.
    fn uses_of(code: &str, ident: &str) -> Vec<usize> {
        let b = code.as_bytes();
        let is_ident = |c: Option<u8>| c.is_some_and(|c| c.is_ascii_alphanumeric() || c == b'_');
        code.match_indices(ident)
            .map(|(at, _)| at)
            .filter(|&at| {
                let before = at.checked_sub(1).map(|k| b[k]);
                !is_ident(before)
                    && !is_ident(b.get(at + ident.len()).copied())
                    && !code[..at].ends_with("fn ")
            })
            .collect()
    }

    /// Every `.rs` file of this crate, as (path relative to `src/`, blanked code), read through
    /// the crate's one whole-crate walk (`source_scan::crate_sources`: a test here reads no source
    /// file by path). Only this module's own block is removed from this file (its line breaks
    /// kept): whatever follows the module is read like the rest of the crate.
    fn crate_sources() -> Vec<(String, String)> {
        let out: Vec<(String, String)> = crate::source_scan::crate_sources()
            .into_iter()
            .map(|(name, text)| {
                let mut code = code_only(&text);
                if name == "instance_probe.rs" {
                    code = without_this_module(&code);
                }
                (name, code)
            })
            .collect();
        assert!(out.len() > 50, "the walk read the crate: {} files", out.len());
        out
    }

    /// Blanked `code` with this module's block, `mod shim_route_tests { … }`, removed and its
    /// line breaks kept; everything before and after it stays.
    fn without_this_module(code: &str) -> String {
        let header = code.find("mod shim_route_tests").expect("this module");
        let open = code[header..].find('{').expect("the module's block") + header;
        let block = block_at(code, open);
        let removed: String = code[header..block.end].chars().filter(|&c| c == '\n').collect();
        format!("{}{removed}{}", &code[..header], &code[block.end..])
    }

    /// Where `ident` is used in `sources`, as sorted (file, innermost enclosing fn).
    fn sites(sources: &[(String, String)], ident: &str) -> Vec<(String, String)> {
        let mut found = Vec::new();
        for (name, code) in sources {
            let bodies = fn_bodies(code);
            for at in uses_of(code, ident) {
                let enclosing = bodies
                    .iter()
                    .filter(|(_, range)| range.contains(&at))
                    .min_by_key(|(_, range)| range.len())
                    .map_or("<item level>", |(fn_name, _)| fn_name.as_str());
                found.push((name.clone(), enclosing.to_string()));
            }
        }
        found.sort();
        found
    }

    fn file<'a>(sources: &'a [(String, String)], name: &str) -> &'a str {
        &sources.iter().find(|(n, _)| n == name).unwrap_or_else(|| panic!("no `{name}`")).1
    }

    fn flat(text: &str) -> String {
        text.split_whitespace().collect::<Vec<_>>().join(" ")
    }

    /// The codegen-time entry answers the MIR route with a refusal and never runs the
    /// MIR-derived producer. Its body is pinned WHOLE (2026-10-13 review): a guard arm ahead of
    /// the refusal, or an early return before the `match`, that routes a shim anywhere else
    /// fails here.
    #[test]
    fn the_codegen_entry_never_takes_the_mir_route() {
        let sources = crate_sources();
        let entry = fn_text(file(&sources, "lib.rs"), "trust_ir_of_instance_body");
        assert_eq!(
            flat(entry),
            "{ instance_admission::refuse_inside_producer_lowering()?; \
             if !tcx.sess.trust_ir_lower_enabled() && !tcx.sess.trust_cg_frontend_is_trust_ir() { \
             return Err(InstanceRefusal::LoweringDisabled); } \
             match instance_route(instance_shape_facts(tcx, instance))? { \
             InstanceRoute::Thir => instance_admission::admit_instance_body(tcx, instance), \
             InstanceRoute::Mir => Err(InstanceRefusal::ThirUnavailable), } }",
            "the codegen entry changed: its MIR route is a refusal and its THIR route the frozen \
             admission, and nothing else"
        );
    }

    /// Every read of an instance's MIR in this crate, and every lowering of a MIR body to
    /// trust-ir, is where it is today (2026-10-13 review): a new MIR route for a shim, under any
    /// name, private or `pub`, fails here. A shim's MIR is `mir_shims`, read through
    /// `instance_mir` or through trust-mir-extract's instance readers (`instance_body`,
    /// `atomic_callsite`); a MIR body becomes trust-ir only through trust-ir-bridge. The three
    /// MIR reads: the MIR-derived producer (no run-time caller: channel C reaches its entry only
    /// on the `Thir` route), the probe's assembly-state read of an admitted local item, and the
    /// drop-glue oracle's read of rustc's drop shim (an oracle, compared, never lowered). The
    /// lowerings: that producer, and the frozen differentials' MIR side (`differential.rs`,
    /// `crate_module.rs`). trust-mir-extract's `concurrency_effects` reads shim MIR for effect
    /// facts, never a body to lower, and is not a needle.
    #[test]
    fn every_mir_read_and_mir_lowering_of_this_crate_is_pinned() {
        let sources = crate_sources();
        let pairs = |list: &[(&str, &str)]| -> Vec<(String, String)> {
            list.iter().map(|(file, func)| (file.to_string(), func.to_string())).collect()
        };
        let pinned: &[(&str, &[(&str, &str)])] = &[
            (
                "instance_mir",
                &[
                    ("drop_glue_oracle.rs", "shim_events"),
                    ("instance_probe.rs", "assembly_state"),
                    ("lib.rs", "trust_ir_of_instance_from_mir"),
                ],
            ),
            ("mir_shims", &[]),
            ("extract_instance_faithful", &[]),
            ("instance_body", &[]),
            ("atomic_callsite", &[]),
            ("lower_to_trust_ir", &[("lib.rs", "trust_ir_of_instance_from_mir")]),
            ("lower_mir_compat_to_trust_ir", &[("differential.rs", "compare")]),
            (
                "lower_mir_compat_functions_to_trust_ir",
                &[
                    ("crate_module.rs", "run_seam_differentials"),
                    ("crate_module/seam_reference.rs", "run_seam_differentials"),
                ],
            ),
        ];
        for (ident, expected) in pinned {
            assert_eq!(
                sites(&sources, ident),
                pairs(*expected),
                "`{ident}` is used outside its pinned sites: a new read of an instance's MIR (a \
                 shim's is `mir_shims`), or a new lowering of a MIR body to trust-ir"
            );
        }
    }

    /// The MIR-derived producer has exactly one caller, the measurement entry; that entry has
    /// exactly one caller, channel C's `Thir` arm; the `Mir` arm runs no producer; and no `pub`
    /// wrapper of either remains.
    #[test]
    fn the_mir_producer_is_reached_only_from_the_probe_thir_arm() {
        let sources = crate_sources();
        // Where an identifier is used, as (file, innermost enclosing fn, byte offset).
        let uses = |ident: &str| -> Vec<(String, String, usize)> {
            let mut found = Vec::new();
            for (name, code) in &sources {
                let bodies = fn_bodies(code);
                for at in uses_of(code, ident) {
                    let enclosing = bodies
                        .iter()
                        .filter(|(_, range)| range.contains(&at))
                        .min_by_key(|(_, range)| range.len())
                        .map_or("<item level>", |(fn_name, _)| fn_name.as_str());
                    found.push((name.clone(), enclosing.to_string(), at));
                }
            }
            found
        };
        let from_mir = uses("trust_ir_of_instance_from_mir");
        assert_eq!(from_mir.len(), 1, "one caller of the MIR-derived producer: {from_mir:?}");
        assert_eq!(
            (from_mir[0].0.as_str(), from_mir[0].1.as_str()),
            ("lib.rs", "trust_ir_of_instance_with_facts")
        );
        let with_facts = uses("trust_ir_of_instance_with_facts");
        assert_eq!(with_facts.len(), 1, "one caller of the measurement entry: {with_facts:?}");
        let (name, enclosing, at) = &with_facts[0];
        assert_eq!((name.as_str(), enclosing.as_str()), ("instance_probe.rs", "channel_c"));

        // ... inside channel C's `Thir` arm, and the `Mir` arm names no producer.
        let probe = file(&sources, "instance_probe.rs");
        let channel_c = fn_bodies(probe)
            .into_iter()
            .find(|(n, _)| n == "channel_c")
            .map(|(_, range)| range)
            .expect("channel C");
        let arm = |pattern: &str| -> std::ops::Range<usize> {
            let at = probe[channel_c.clone()].find(pattern).expect(pattern) + channel_c.start;
            let open = probe[at..].find('{').expect("the arm's block") + at;
            block_at(probe, open)
        };
        let thir = arm("Ok(crate::InstanceRoute::Thir) =>");
        assert!(thir.contains(at), "the measurement entry runs in the `Thir` arm only");
        let mir = &probe[arm("Ok(crate::InstanceRoute::Mir) =>")];
        for forbidden in ["trust_ir_of", "instance_mir"] {
            assert!(!mir.contains(forbidden), "channel C's `Mir` arm names `{forbidden}`: {mir}");
        }
        assert!(flat(mir).contains("(\"\", \"\".to_string())"), "it records residue: {mir}");

        // No `pub` wrapper remains to run the producer on a shim from a dependent crate.
        for wrapper in ["trust_ir_of_instance", "trust_ir_of_instance_explained"] {
            assert!(uses(wrapper).is_empty(), "`{wrapper}` is used: {:?}", uses(wrapper));
            for (name, code) in &sources {
                let defined = fn_bodies(code).into_iter().any(|(n, _)| n == wrapper);
                assert!(!defined, "`fn {wrapper}` is defined again in {name}");
            }
        }
    }

    #[test]
    fn the_lexer_blanks_literals_and_comments() {
        let src = concat!(
            "fn a() { let s = \"x\\\"instance_mir(\\\\\"; }\n",
            "fn b() { let t = \"line \\\n  instance_mir( continued\"; }\n",
            "fn c() { let r = r#\"raw \"instance_mir(\" }\"#; let q = br\"{\"; }\n",
            "fn d<'a>(x: &'a u8) -> char { let _ = b'{'; let _ = '\\''; '\"' }\n",
            "fn e() { /* outer /* instance_mir( */ { */ g(); } // instance_mir(\n",
            "fn f(x: [u8; 4]) -> u8 { let r#type = 1; instance_mir(x) }\n",
        );
        let code = code_only(src);
        assert_eq!(code.lines().count(), src.lines().count(), "line breaks are kept: {code}");
        assert_eq!(uses_of(&code, "instance_mir").len(), 1, "only `f` calls it: {code}");
        let bodies = fn_bodies(&code);
        let names: Vec<&str> = bodies.iter().map(|(n, _)| n.as_str()).collect();
        assert_eq!(names, ["a", "b", "c", "d", "e", "f"], "{code}");
        let at = uses_of(&code, "instance_mir")[0];
        let owner = bodies.iter().find(|(_, r)| r.contains(&at)).map(|(n, _)| n.as_str());
        assert_eq!(owner, Some("f"));
        assert!(fn_text(&code, "e").contains("g();"), "a block comment's braces are not code");
        assert!(fn_text(&code, "d").ends_with("' ' }"), "a char literal `'\"'` opens no string");
        assert!(uses_of("fn a() {} a();", "a") == [10], "a definition is not a use");
    }
}
