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
    args: ty::GenericArgsRef<'tcx>,
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
    let def_path = tcx.def_path_str(def.to_def_id());
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
                tcx.def_path_str(imp)
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
                    tcx.def_path_str(imp)
                );
                continue;
            }
            Err(_) => {
                eprintln!(
                    "TRUST-WALLA-PROBE A def={def_path} impl={} resolve=error",
                    tcx.def_path_str(imp)
                );
                continue;
            }
        };
        if inst.def_id() != def.to_def_id() {
            eprintln!(
                "TRUST-WALLA-PROBE A def={def_path} impl={} resolve=overridden-by-impl \
                 (resolves to {})",
                tcx.def_path_str(imp),
                tcx.def_path_str(inst.def_id())
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
    if probe_filter(tcx).is_none() {
        return;
    }
    if !tcx.sess.opts.output_types.should_codegen() {
        eprintln!("TRUST-WALLA-PROBE B skipped=no-codegen-in-this-session");
        return;
    }
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
