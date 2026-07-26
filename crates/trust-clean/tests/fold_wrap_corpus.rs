// fold_wrap_corpus — RUNG E of the structural-fold lane
// (docs/design/2026-07-10-structural-fold-lane.md §3.4 + §5 Rung E): the
// G-FAMILY WRAPPERS over the rung-C/D-certified memoized Expr folds. REAL
// trustc MIR dumps (never hand-transcribed — see
// fixtures/expr-fold-corpus/PROVENANCE.md) of clean-kernel `expr/subst.rs`'s
// launch/delegate wrappers, through the production pipeline.
//
// What this pins:
//   * FOLDER-LAUNCH wrappers (design §3.4 option (b), per-wrapper inlining —
//     structurally forced; see `trustir_fold_wrap`'s module doc):
//     `subst_fvar` (depthless FVarSubst), `lift_at` (depth Lifter + the
//     `amount == 0` early-clone guard), `abstract_fvar_at` (depth Abstractor
//     via the fingerprinted `Abstractor::new` ctor + inline-HashMap memo) —
//     each recognizes with the exact folder/field/d0 map and flips
//     FULLY_FAITHFUL on the production gate (empty registry — inlining needs
//     no callee ordering).
//   * PURE DELEGATES (design §3.4 option (a), the TExpr-valued
//     `CallE`/`callResultE` transport twin): `lift`/`lift_from` →
//     `lift_at`, `abstract_fvar` → `abstract_fvar_at` — each flips
//     FULLY_FAITHFUL ONLY with its callee in the callees-first certified
//     registry (registry dependence pinned both ways).
//   * THE KERNEL PIECES: `wrapAdequate`/`wrapAdequateD` mint modulo 3 on the
//     real 33-ctor table; the identity-claim and swapped-eliminator
//     forgeries are KernelRejected; `callReturnInstanceE` mints modulo 3 and
//     a WRONG conclusion predicate is KernelRejected.
//   * TRANSPORT FORGERY PROBES: wrong-denotation (doctored wrapper building
//     a different folder than its fold row), callee-caller mismatch
//     (delegate whose registry entry names a non-launch callee), stale
//     registry (callee body doctored after registration) — each a NAMED
//     decline / non-FF verdict.
//   * `instantiate_at` (launch, Instantiator) and `instantiate` (delegate →
//     `instantiate_at`) flip TOO: the Instantiator SCC certified on main via
//     the P-ORD-CMP leaf-assert landing (its `fold_bvar_opt` hostage
//     retired), so the rung-E arms compose with it — 8 wrapper flips total.
//   * THE HOSTAGE ROWS, BY NAME: `instantiate_rev` (MultiInstantiator's
//     genuinely-satisfiable `self.depth + n` overflow asserts + slice
//     guards), `lower_loose_bvars` (Lowerer's reachable debug-assert +
//     Option return), `instantiate_level_params{,_map,_direct}`
//     (fold_sort/const leaves + Iterator::collect),
//     `has_loose_bvar`/`collect_constants` (Expr-scale bool/accumulator
//     folds not yet certified; has_loose_bvar additionally carries a
//     genuinely-satisfiable `idx + 1` overflow VC).
//
// Run with:
//   RUSTC_BOOTSTRAP=1 cargo test -p trust-clean --manifest-path crates/Cargo.toml \
//       --test fold_wrap_corpus -- --nocapture
//
// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use clean_kernel::{BinderData, BinderInfo, Expr, Name};
use trust_clean::mirsem::CalleeFact;
use trust_clean::trustir_anchor::{IrOperand, RefinementVerdict};
use trust_clean::trustir_fold::DumpBodies;
use trust_clean::trustir_fold_expr::{
    check_call_return_instance_texpr, check_expr_fold_wrap_refinement_cached,
    check_expr_fold_wrap_refinement_cached_d, check_expr_fold_wrap_refinement_claimed,
    check_expr_fold_wrap_refinement_claimed_d, probe_wrap_rhs_swapped,
};
use trust_clean::trustir_fold_wrap::{
    FoldWrapDecline, LaunchFieldSrc, SemFoldLaunch, sem_adt_delegate_of, sem_fold_launch_wrapper_of,
};
use trust_types::VerifiableFunction;

fn corpus_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("fixtures/expr-fold-corpus")
}

fn load(name: &str) -> VerifiableFunction {
    let path = corpus_dir().join(format!("{name}.json"));
    let bytes = std::fs::read(&path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
    trust_clean::prove::decode_verifiable_function_with_authenticated_legacy_metadata(&bytes)
        .unwrap_or_else(|e| panic!("parse {}: {e}", path.display()))
}

fn all_bodies() -> DumpBodies {
    let mut m = DumpBodies::new();
    for entry in std::fs::read_dir(corpus_dir()).expect("corpus dir") {
        let path = entry.expect("entry").path();
        if path.extension().and_then(|e| e.to_str()) != Some("json") {
            continue;
        }
        let bytes = std::fs::read(&path).expect("read");
        let f = trust_clean::prove::decode_verifiable_function_with_authenticated_legacy_metadata(
            &bytes,
        )
        .expect("parse");
        m.entry(f.def_path.clone()).or_insert(f);
    }
    m
}

const SUBST_FVAR: &str = "expr__subst__<impl expr__Expr>__subst_fvar";
const LIFT: &str = "expr__subst__<impl expr__Expr>__lift";
const LIFT_AT: &str = "expr__subst__<impl expr__Expr>__lift_at";
const LIFT_FROM: &str = "expr__subst__<impl expr__Expr>__lift_from";
const ABSTRACT_FVAR: &str = "expr__subst__<impl expr__Expr>__abstract_fvar";
const ABSTRACT_FVAR_AT: &str = "expr__subst__<impl expr__Expr>__abstract_fvar_at";
const INSTANTIATE: &str = "expr__subst__<impl expr__Expr>__instantiate";
const INSTANTIATE_AT: &str = "expr__subst__<impl expr__Expr>__instantiate_at";

fn launch(name: &str) -> Result<SemFoldLaunch, FoldWrapDecline> {
    let func = load(name);
    let bodies = all_bodies();
    sem_fold_launch_wrapper_of(&func, &bodies)
}

fn bd() -> BinderData {
    BinderData::from(BinderInfo::Default)
}

fn cst(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), clean_kernel::LevelVec::new())
}

// ===========================================================================
// Launch recognition — the three certifiable wrappers
// ===========================================================================

/// `subst_fvar` launches the depthless FVarSubst: fields (id ← _2,
/// replacement ← _3, memo fresh), no guard, no ctor.
#[test]
fn subst_fvar_launch_recognizes() {
    let l = launch(SUBST_FVAR)
        .unwrap_or_else(|d| panic!("subst_fvar must recognize, got {} ({d:?})", d.name()));
    assert_eq!(l.folder, "expr::subst::FVarSubst");
    assert!(l.fold.depth.is_none(), "FVarSubst is the depthless family");
    assert_eq!(l.zero_guard, None);
    assert_eq!(l.ctor, None);
    assert_eq!(
        l.field_srcs,
        vec![LaunchFieldSrc::Param(2), LaunchFieldSrc::Param(3), LaunchFieldSrc::Memo],
        "field map: id ← _2, replacement ← _3, memo fresh"
    );
    assert_eq!(l.d0, None);
}

/// `lift_at` launches the depth Lifter behind the `amount == 0` early-clone
/// guard; d0 = the `start` parameter (_2).
#[test]
fn lift_at_launch_recognizes() {
    let l = launch(LIFT_AT)
        .unwrap_or_else(|d| panic!("lift_at must recognize, got {} ({d:?})", d.name()));
    assert_eq!(l.folder, "expr::subst::Lifter");
    assert!(l.fold.depth.is_some(), "Lifter is the depth family");
    assert_eq!(l.zero_guard, Some(3), "the amount == 0 guard reads _3");
    assert_eq!(
        l.field_srcs,
        vec![LaunchFieldSrc::Param(2), LaunchFieldSrc::Param(3), LaunchFieldSrc::Memo],
        "field map: start ← _2, amount ← _3, memo fresh"
    );
    assert_eq!(l.d0, Some(LaunchFieldSrc::Param(2)), "d0 = the start parameter");
}

/// `abstract_fvar_at` launches the depth Abstractor through the fingerprinted
/// `Abstractor::new` ctor (inline-HashMap memo); d0 = the depth parameter (_3).
#[test]
fn abstract_fvar_at_launch_recognizes() {
    let l = launch(ABSTRACT_FVAR_AT)
        .unwrap_or_else(|d| panic!("abstract_fvar_at must recognize, got {} ({d:?})", d.name()));
    assert_eq!(l.folder, "expr::subst::Abstractor");
    assert_eq!(l.ctor.as_deref(), Some("expr::subst::Abstractor::new"));
    let depth = l.fold.depth.as_ref().expect("Abstractor is the depth family");
    assert!(depth.inline_memo, "Abstractor uses the inline-HashMap memo");
    assert_eq!(
        l.field_srcs,
        vec![LaunchFieldSrc::Param(2), LaunchFieldSrc::Param(3), LaunchFieldSrc::Memo],
        "field map (through the ctor): id ← _2, depth ← _3, map fresh"
    );
    assert_eq!(l.d0, Some(LaunchFieldSrc::Param(3)), "d0 = the depth parameter");
}

/// `instantiate_at` launches the depth Instantiator (rung-E takeover: the
/// banked wip recognized it but held it hostage on the then-uncertified
/// `fold_bvar_opt` leaf; main's P-ORD-CMP leaf-assert landing retired that).
#[test]
fn instantiate_at_launch_recognizes() {
    let l = launch(INSTANTIATE_AT)
        .unwrap_or_else(|d| panic!("instantiate_at must recognize, got {} ({d:?})", d.name()));
    assert_eq!(l.folder, "expr::subst::Instantiator");
    assert!(l.fold.depth.is_some(), "Instantiator is the depth family");
}

// ===========================================================================
// Production-gate flips — launch wrappers (registry-free, option (b))
// ===========================================================================

/// The four launch wrappers flip FULLY_FAITHFUL with an EMPTY registry —
/// per-wrapper inlining needs no callee ordering. `instantiate_at` is the
/// rung-E-takeover addition: the banked wip pinned it hostage on the
/// Instantiator SCC's `fold_bvar_opt` leaf, which main's leaf-assert landing
/// (P-ORD-CMP ordering-dispatch lane) has since certified — the launch arm
/// now composes with that certificate, no rung-E code change needed.
#[test]
fn launch_wrappers_fully_faithful_on_production_gate() {
    let bodies = all_bodies();
    let empty: BTreeMap<String, CalleeFact> = BTreeMap::new();
    for row in [SUBST_FVAR, LIFT_AT, ABSTRACT_FVAR_AT, INSTANTIATE_AT] {
        let func = load(row);
        let diag = trust_clean::diagnose_fully_faithful_gate_with_bodies(&func, &empty, &bodies);
        assert!(diag.via_ir_shape, "{row}: the rung-E launch arm must accept the shape");
        assert!(diag.fully_faithful, "{row} must be FULLY_FAITHFUL");
    }
}

// ===========================================================================
// Production-gate flips — delegates (registry-dependent, option (a))
// ===========================================================================

/// The delegates flip ONLY with their callee in the certified registry
/// (callees-first discipline), and NOT with an empty registry.
/// `instantiate` → `instantiate_at` is the rung-E-takeover addition (callee
/// unhostaged by main's Instantiator-SCC certification).
#[test]
fn delegates_fully_faithful_with_certified_callee_registry_only() {
    let bodies = all_bodies();
    let empty: BTreeMap<String, CalleeFact> = BTreeMap::new();
    for (row, callee) in [
        (LIFT, LIFT_AT),
        (LIFT_FROM, LIFT_AT),
        (ABSTRACT_FVAR, ABSTRACT_FVAR_AT),
        (INSTANTIATE, INSTANTIATE_AT),
    ] {
        let func = load(row);
        // Empty registry: the delegate arm must decline (no callee fact).
        let diag = trust_clean::diagnose_fully_faithful_gate_with_bodies(&func, &empty, &bodies);
        assert!(!diag.fully_faithful, "{row} must NOT be FF without its callee in the registry");
        // The callee itself is FF (launch arm), so the driver would have
        // registered it earlier in the callees-first order; mirror that.
        let callee_func = load(callee);
        let cdiag =
            trust_clean::diagnose_fully_faithful_gate_with_bodies(&callee_func, &empty, &bodies);
        assert!(cdiag.fully_faithful, "{callee} must be FF (launch arm) before its caller");
        let mut reg: BTreeMap<String, CalleeFact> = BTreeMap::new();
        reg.insert(callee_func.def_path.clone(), CalleeFact::of_certified(&callee_func));
        let diag = trust_clean::diagnose_fully_faithful_gate_with_bodies(&func, &reg, &bodies);
        assert!(diag.via_ir_shape, "{row}: the rung-E delegate arm must accept the shape");
        assert!(diag.fully_faithful, "{row} must be FULLY_FAITHFUL with {callee} registered");
    }
}

#[test]
fn delegate_rechecks_recognizable_callee_semantics_at_composition_point() {
    const HOSTAGE: &str = "expr__subst__<impl expr__Expr>__instantiate_level_params_map";
    let bodies = all_bodies();
    let hostage = load(HOSTAGE);
    assert!(
        sem_fold_launch_wrapper_of(&hostage, &bodies).is_ok(),
        "the adversarial callee must retain a recognizable launch shape",
    );

    let mut delegate = load(INSTANTIATE);
    for block in &mut delegate.body.blocks {
        if let trust_types::Terminator::Call { func, .. } = &mut block.terminator {
            *func = hostage.def_path.clone();
        }
    }
    let mut registry = BTreeMap::new();
    let mut surface_fact = CalleeFact::of_certified(&hostage);
    // Model an adversarial/stale registry snapshot that satisfies the delegate
    // recognizer's shallow arity pin.  The composition gate must still inspect
    // the current sibling body and re-run its semantic launch certificate.
    surface_fact.arg_count = 3;
    registry.insert(hostage.def_path.clone(), surface_fact);
    let surface = sem_adt_delegate_of(&delegate, &registry);
    assert!(
        surface.is_ok(),
        "registry + surface shape alone intentionally reach the composition gate: {surface:?}",
    );

    let diag = trust_clean::diagnose_fully_faithful_gate_with_bodies(&delegate, &registry, &bodies);
    assert!(
        !diag.fully_faithful,
        "a recognizable but semantically uncertified launch must fail the composition-point recheck",
    );
}

/// The delegate recognizer records the exact callee + arg map.
#[test]
fn lift_delegate_shape_records_callee_and_args() {
    let func = load(LIFT);
    let callee_func = load(LIFT_AT);
    let mut reg: BTreeMap<String, CalleeFact> = BTreeMap::new();
    reg.insert(callee_func.def_path.clone(), CalleeFact::of_certified(&callee_func));
    let del = sem_adt_delegate_of(&func, &reg)
        .unwrap_or_else(|d| panic!("lift must recognize as a delegate, got {d:?}"));
    assert_eq!(del.callee, "expr::subst::<impl expr::Expr>::lift_at");
    assert_eq!(
        del.args,
        vec![IrOperand::Var(0), IrOperand::Const(0), IrOperand::Var(1)],
        "lift(self, amount) = lift_at(self, 0, amount)"
    );
}

// ===========================================================================
// The hostage rows — named declines / honest non-verdicts
// ===========================================================================

/// `instantiate_level_params_map` RECOGNIZES as a launch (shape walked
/// end-to-end) but stays hostage at the gate: LevelParamSubst's SCC carries
/// uncertified leaves (`fold_sort_opt` → `Level::substitute_map`, the E-sort
/// blocker; `fold_const_opt` → the `Iterator::collect` residue).
///
/// `instantiate_at` — recognize-but-hostage at the banked rung-E wip — is NOT
/// in this list anymore: main's leaf-assert landing certified the
/// Instantiator SCC (P-ORD-CMP), so it now flips (see
/// `launch_wrappers_fully_faithful_on_production_gate`).
#[test]
fn hostage_launches_recognize_but_do_not_flip() {
    let bodies = all_bodies();
    let empty: BTreeMap<String, CalleeFact> = BTreeMap::new();
    for (row, folder) in [(
        "expr__subst__<impl expr__Expr>__instantiate_level_params_map",
        "expr::subst::LevelParamSubst",
    )] {
        let l = launch(row)
            .unwrap_or_else(|d| panic!("{row} must RECOGNIZE (hostage at the gate), got {d:?}"));
        assert_eq!(l.folder, folder);
        let func = load(row);
        let diag = trust_clean::diagnose_fully_faithful_gate_with_bodies(&func, &empty, &bodies);
        assert!(!diag.fully_faithful, "{row} must stay hostage (uncertified leaves)");
    }
}

/// The named launch declines of the remaining hostages:
/// * `instantiate_rev` — slice guards (`is_empty`, len==1 bounds-checked
///   index) before the launch: outside the pinned vocabulary;
/// * `lower_loose_bvars` — returns `Option<Expr>`, not `Expr`;
/// * `has_loose_bvar` — Bool-returning (the Expr-scale bool fold is not this
///   lane; its `idx + 1` overflow VC is additionally genuinely satisfiable);
/// * `collect_constants` — HashSet-returning (accumulator lane).
///
/// (`instantiate` left this list at the rung-E takeover: its callee
/// `instantiate_at` now certifies, so it flips — see the delegates test. Its
/// empty-registry `callee_unresolved` decline below is the registry-
/// dependence pin, not a hostage claim.)
#[test]
fn remaining_hostages_decline_by_name() {
    let bodies = all_bodies();
    let empty: BTreeMap<String, CalleeFact> = BTreeMap::new();

    let d = launch("expr__subst__<impl expr__Expr>__instantiate_rev").unwrap_err();
    assert_eq!(d.name(), "fold_wrap::launch_shape", "instantiate_rev: {d:?}");

    let d = launch("expr__subst__<impl expr__Expr>__lower_loose_bvars").unwrap_err();
    assert_eq!(d.name(), "fold_wrap::signature_unsupported", "lower_loose_bvars: {d:?}");

    let d = launch("expr__subst__<impl expr__Expr>__has_loose_bvar").unwrap_err();
    assert_eq!(d.name(), "fold_wrap::signature_unsupported", "has_loose_bvar: {d:?}");

    let d = launch("expr__subst__<impl expr__Expr>__collect_constants").unwrap_err();
    assert_eq!(d.name(), "fold_wrap::signature_unsupported", "collect_constants: {d:?}");

    // `instantiate` with an EMPTY registry declines `callee_unresolved` —
    // the delegate arm's registry dependence (the callees-first driver must
    // certify + register `instantiate_at` first; with it registered the row
    // flips, see `delegates_fully_faithful_with_certified_callee_registry_only`).
    let func = load("expr__subst__<impl expr__Expr>__instantiate");
    let d = sem_adt_delegate_of(&func, &empty).unwrap_err();
    assert_eq!(d.name(), "fold_wrap::callee_unresolved", "instantiate: {d:?}");

    // And none of the hostages is FULLY_FAITHFUL on the production gate.
    for row in [
        "expr__subst__<impl expr__Expr>__instantiate_rev",
        "expr__subst__<impl expr__Expr>__lower_loose_bvars",
        "expr__subst__<impl expr__Expr>__has_loose_bvar",
        "expr__subst__<impl expr__Expr>__collect_constants",
        "expr__subst__<impl expr__Expr>__instantiate_level_params",
        "expr__subst__<impl expr__Expr>__instantiate_level_params_direct",
    ] {
        let func = load(row);
        let diag = trust_clean::diagnose_fully_faithful_gate_with_bodies(&func, &empty, &bodies);
        assert!(!diag.fully_faithful, "{row} must stay honestly non-FF");
    }
}

// ===========================================================================
// Kernel witnesses — wrapAdequate / wrapAdequateD + forgery probes
// ===========================================================================

/// The launch-composition theorems mint modulo 3 on the REAL 33-ctor table
/// (both families), and the forgeries are KernelRejected:
/// * the IDENTITY claim (`wrapper = e` — drops the fold entirely);
/// * the SWAPPED-ELIMINATOR claim (`some ↦ e` — discards the fold result).
#[test]
fn wrap_witnesses_mint_and_forgeries_kernel_rejected() {
    let subst = launch(SUBST_FVAR).expect("subst_fvar recognizes");
    let lifter = launch(LIFT_AT).expect("lift_at recognizes");

    let (v, _) = check_expr_fold_wrap_refinement_cached(&subst.fold.ctors);
    assert!(
        matches!(v, RefinementVerdict::ProvenModulo3),
        "depthless wrapAdequate must mint: {v:?}"
    );
    let (v, _) = check_expr_fold_wrap_refinement_cached_d(&lifter.fold.ctors);
    assert!(matches!(v, RefinementVerdict::ProvenModulo3), "depth wrapAdequateD must mint: {v:?}");

    // Identity forgery (both families): claim the wrapper returns e.
    let identity = Expr::bvar(0);
    let v = check_expr_fold_wrap_refinement_claimed(&subst.fold.ctors, Some(&identity));
    assert!(
        matches!(v, RefinementVerdict::KernelRejected(_)),
        "identity claim must be KernelRejected (depthless): {v:?}"
    );
    // Depth family: under (…, e, d) the identity claim is `e` = bvar 1.
    let identity_d = Expr::bvar(1);
    let v = check_expr_fold_wrap_refinement_claimed_d(&lifter.fold.ctors, Some(&identity_d));
    assert!(
        matches!(v, RefinementVerdict::KernelRejected(_)),
        "identity claim must be KernelRejected (depth): {v:?}"
    );

    // Swapped-eliminator forgery (depthless).
    let swapped = probe_wrap_rhs_swapped(&subst.fold.ctors);
    let v = check_expr_fold_wrap_refinement_claimed(&subst.fold.ctors, Some(&swapped));
    assert!(
        matches!(v, RefinementVerdict::KernelRejected(_)),
        "swapped-eliminator claim must be KernelRejected: {v:?}"
    );
}

// ===========================================================================
// The ADT transport twin — callReturnInstanceE + wrong-postcondition probe
// ===========================================================================

/// `callReturnInstanceE` mints modulo 3 over the real fold mirror, and a
/// WRONG conclusion predicate (`λ (_ : TExpr). True` — distinct from the
/// ∀-bound transported `post`) is KernelRejected.
#[test]
fn call_transport_instance_mints_and_wrong_postcondition_fails_closed() {
    let subst = launch(SUBST_FVAR).expect("subst_fvar recognizes");
    let v = check_call_return_instance_texpr(&subst.fold.ctors, 0, &IrOperand::Var(0), None);
    assert!(
        matches!(v, RefinementVerdict::ProvenModulo3),
        "callReturnInstanceE must mint modulo 3: {v:?}"
    );
    let wrong = Expr::lam(bd(), cst("Trust.TrustIr.ExprFold.TExpr"), cst("True"));
    let v =
        check_call_return_instance_texpr(&subst.fold.ctors, 0, &IrOperand::Var(0), Some(&wrong));
    assert!(
        matches!(v, RefinementVerdict::KernelRejected(_)),
        "a WRONG conclusion predicate must be KernelRejected: {v:?}"
    );
}

// ===========================================================================
// Transport forgery probes — wrong denotation / mismatch / stale registry
// ===========================================================================

/// WRONG-DENOTATION probe: doctor `subst_fvar` to build a DIFFERENT folder
/// (Lifter) than its own — the launch recognizer must decline
/// `fold_wrap::folder_mismatch` (the folder row's shape disagrees with the
/// wrapper's aggregate field map).
#[test]
fn doctored_wrong_folder_declines_folder_mismatch() {
    let mut func = load(SUBST_FVAR);
    let bodies = all_bodies();
    // Rename the aggregate's folder type in place.
    for b in &mut func.body.blocks {
        for s in &mut b.stmts {
            if let trust_types::Statement::Assign {
                rvalue:
                    trust_types::Rvalue::Aggregate(trust_types::AggregateKind::Adt { name, .. }, _),
                ..
            } = s
            {
                if name == "expr::subst::FVarSubst" {
                    *name = "expr::subst::Lifter".to_string();
                }
            }
        }
    }
    let d = sem_fold_launch_wrapper_of(&func, &bodies).unwrap_err();
    assert_eq!(d.name(), "fold_wrap::folder_mismatch", "{d:?}");
}

/// STALE-REGISTRY probe: the delegate's registry entry exists, but the
/// callee's sibling dump body has been doctored into a non-launch shape —
/// conjunct (b) (callee-caller match) must fail, so the delegate is NOT FF
/// even though the registry still names the callee.
#[test]
fn stale_registry_entry_does_not_certify_delegate() {
    let func = load(LIFT);
    let callee_func = load(LIFT_AT);
    let mut reg: BTreeMap<String, CalleeFact> = BTreeMap::new();
    reg.insert(callee_func.def_path.clone(), CalleeFact::of_certified(&callee_func));
    // Doctor the callee body in the sibling map: swap its return type so the
    // launch recognition fails (a stale/incompatible dump).
    let mut bodies = all_bodies();
    if let Some(cb) = bodies.get_mut(&callee_func.def_path) {
        cb.body.return_ty = trust_types::Ty::Bool;
    }
    let diag = trust_clean::diagnose_fully_faithful_gate_with_bodies(&func, &reg, &bodies);
    assert!(
        !diag.fully_faithful,
        "a stale/doctored callee body must fail the callee-caller match conjunct"
    );
}

/// CALLEE-CALLER MISMATCH probe: the delegate resolves a registry entry whose
/// arity disagrees with the call site — named decline
/// `fold_wrap::callee_mismatch`.
#[test]
fn arity_mismatch_declines_callee_mismatch() {
    let func = load(LIFT);
    let callee_func = load(LIFT_AT);
    let mut fact = CalleeFact::of_certified(&callee_func);
    fact.arg_count = 2; // the real lift_at takes 3
    let mut reg: BTreeMap<String, CalleeFact> = BTreeMap::new();
    reg.insert(callee_func.def_path.clone(), fact);
    let d = sem_adt_delegate_of(&func, &reg).unwrap_err();
    assert_eq!(d.name(), "fold_wrap::callee_mismatch", "{d:?}");
}

/// MEMO-FRESHNESS probe: doctor `subst_fvar` to COPY (not MOVE) a reused memo
/// into the folder — declines `fold_wrap::folder_mismatch` (the memo field
/// must consume the fresh default by move).
#[test]
fn doctored_memo_copy_declines() {
    let mut func = load(SUBST_FVAR);
    let bodies = all_bodies();
    for b in &mut func.body.blocks {
        for s in &mut b.stmts {
            if let trust_types::Statement::Assign {
                rvalue: trust_types::Rvalue::Aggregate(_, ops),
                ..
            } = s
            {
                for op in ops.iter_mut() {
                    if let trust_types::Operand::Move(p) = op {
                        *op = trust_types::Operand::Copy(p.clone());
                    }
                }
            }
        }
    }
    let d = sem_fold_launch_wrapper_of(&func, &bodies).unwrap_err();
    assert_eq!(d.name(), "fold_wrap::folder_mismatch", "{d:?}");
}

/// GUARD-POLARITY probe: doctor `lift_at`'s guard switch to send the `== 0`
/// case into the FOLD path and the nonzero case into the clone arm (swapped
/// arms) — the clone arm lands where the build path must be, and the
/// recognizer declines by name.
#[test]
fn doctored_guard_swap_declines() {
    let mut func = load(LIFT_AT);
    let bodies = all_bodies();
    for b in &mut func.body.blocks {
        if let trust_types::Terminator::SwitchInt { targets, otherwise, .. } = &mut b.terminator {
            if let [(0, t)] = targets.as_mut_slice() {
                std::mem::swap(t, otherwise);
            }
        }
    }
    let d = sem_fold_launch_wrapper_of(&func, &bodies).unwrap_err();
    assert!(matches!(d.name(), "fold_wrap::guard_shape" | "fold_wrap::launch_shape"), "{d:?}");
}
