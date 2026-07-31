// trust-certify: the whnf REDUCER-UNIVERSAL COMPOSITION — one fail-closed
// certificate over the full L + M + F component set.
//
// The composition argument (docs/design-notes/2026-07-16-checker-core-whnf-
// closure-status.md):
//
//   (L) LITERAL control-flow witnesses — the real fork-extracted reducer MIR:
//       dispatch totality over all 25 ExprKind variants, the stack_safe payload
//       passthrough, the coherent cache wrapper, and the fixpoint-only exits;
//   (M) MODEL universals — `whnf_progress_bd` / `whnf_normalizes_bd`, re-checked
//       through clean's own kernel (the checker-core attestation lane);
//   (F) STEP FIDELITY — the executable gates: the real `TypeChecker::whnf`
//       agrees structurally with small auditable micro reducers on β+ζ (the
//       bounded fragment), δ (declaration table), ι (recursors incl. the
//       recursive-IH arm), and the nat literal accelerator — plus the
//       machine-checked SCOPING facts (the default mode has no cubical layer,
//       so the kan arms are dead; unregistered native spines are stuck)
//
//   ⟹ these components are mutually COHERENT. That is the full claim. This
//     composition does NOT establish that the literal Rust `whnf` returns
//     weak-head normal forms (the reducer universal): reachability witnesses
//     plus bounded model theorems may not mint a literal-Rust universal —
//     step semantic correspondence, cache/environment validity, and recursive
//     certificates remain open (see the 2026-07-16 checker-core closure note,
//     "Remaining literal-Rust boundaries"). NON-AUTHORITATIVE validation
//     artifact: the report minted below is a coherence report, never
//     ProofEvidence.
//
// THIS module turns that argument into ONE fail-closed artifact: a single
// certify call that RUNS every component — the four MIR witnesses on the
// committed real-MIR fixtures, the six fidelity checks, and the kernel
// re-attestation of both model universals — and mints a composition report
// (with a lineage digest binding every component) ONLY if ALL of them hold.
//
// HONEST SCOPE (updated 2026-07-17): every L-witness now ALSO has a
// KERNEL-CHECKED reflection — the payload shape predicate computed over
// kernel-encoded MIR data (registered + byte-pinned to the fixture), and the
// dispatch/cached-reducer/fixpoint-exit fact sets COMPUTED by the kernel over
// programmatically-encoded real CFGs (the LK components below, checked against
// one shared spec build). The M components are kernel attestations, including
// the composition glue theorem (fixpoint + progress => done-or-stuck). What
// remains Rust is: the F gates (executable structural agreement — their
// auditable micro reducers ARE the comparator), the fail-closed ENCODERS
// (fixture -> kernel data; the payload's is byte-pinned, the others share the
// witnesses' own primitives), and THIS CONJUNCTION. The single all-in-one
// kernel theorem (one statement conjoining every reflected component) is the
// natural final packaging; its parts are all kernel-checked here.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use sha2::{Digest, Sha256};
use trust_types::VerifiableFunction;

use crate::checker_core_is_whnf::{
    WhnfDispatchPartition, whnf_dispatch_partition, whnf_inner_is_cached_reducer,
    whnf_outer_loop_exits_only_at_fixpoint_cache_or_heartbeat,
    whnf_stack_safe_payload_is_whnf_inner,
};
use crate::checker_core_lemma::{
    certify_env_fixpoint_classifies_bd, certify_red_fixpoint_classifies_bd,
    certify_reduce_once_sound, certify_step_fixpoint_classifies_bd, certify_whnf_fuel_no_redex,
    certify_whnf_fuel_reaches_sound, certify_whnf_normalizes_bd, certify_whnf_progress_bd,
    certify_whnf_progress_env_bd, certify_whnf_progress_red_bd,
};

/// The per-component outcome of the composition run. Every field must be `true`
/// (and the M lineages present) for the composite to mint.
#[derive(Debug, Clone)]
pub struct ReducerCompositionReport {
    /// (L1) dispatch totality over all 25 ExprKind variants, expected classes.
    pub l_dispatch_totality: bool,
    /// (L2) the stack_safe payload is a pure whnf_inner passthrough.
    pub l_payload_passthrough: bool,
    /// (L3) whnf_inner is a coherent cached wrapper of whnf_outer_loop.
    pub l_cached_reducer: bool,
    /// (L4) whnf_outer_loop exits only at fixpoint / cache-hit / heartbeat.
    pub l_fixpoint_exits: bool,
    /// (L5) whnf_core_inner's EXACT per-iteration step routing: δ only from
    /// Const, β/ι (+ accelerators + Glue) only from App, ι-proj only from
    /// Proj, path-β/kan only under their cubical kinds, FVar/Let/MData step-free.
    pub l_core_step_routing: bool,
    /// (L6) beta_or_iota_step's REDEX-GATED contraction: the pre-normalized
    /// head's is_lam test exclusively partitions β (instantiate_rev) from the
    /// five ι-family reducers — the first property about what a step DOES.
    pub l_step_redex_gating: bool,
    /// (L7) whnf_recurse MODE FIDELITY: the exhaustive WhnfMode switch routes
    /// Full/NoDelta/Transparency to DISJOINT reducers — δ-discipline (NoDelta
    /// never reaches the δ-enabled whnf_impl) + cache coherence.
    pub l_recurse_mode_fidelity: bool,
    /// (L8) δ INTERIOR: inside unfold_definition_cached the env unfold fires
    /// ONLY on a cache-missing Const-kind expr; Some inserts, None/hit/non-
    /// Const never do.
    pub l_delta_interior: bool,
    /// (L9) ι-PROJ INTERIOR: field extraction fires exactly on a constructor-
    /// headed struct with the field present; complements rebuild the honest
    /// stuck proj.
    pub l_proj_interior: bool,
    /// (L10) SPINE LINK: whnf_reduce_proj is a pure delegation shim to
    /// reduce_proj_with_mode.
    pub l_proj_shim: bool,
    /// (F1..F4) the four structural step-fidelity gates (β+ζ, δ, ι, nat).
    pub f_step_gates: bool,
    /// (F5) machine-checked scope: default mode has no cubical layer AND
    /// unregistered native spines are stuck.
    pub f_scope: bool,
    /// (LK1..LK4) the four KERNEL-CHECKED L reflections: the payload's registered
    /// kernel goal pinned byte-identically to the fixture-derived encoding, and
    /// the dispatch / cached-reducer / fixpoint-exit fact sets COMPUTED by the
    /// kernel over the programmatically-encoded real MIR.
    pub l_kernel_payload_pinned: bool,
    pub l_kernel_dispatch: bool,
    pub l_kernel_cached_reducer: bool,
    pub l_kernel_fixpoint_exit: bool,
    /// (LK5) the step-routing exclusivity core kernel-computed over the
    /// encoded whnf_core_inner CFG (backedge cut kernel-side).
    pub l_kernel_core_routing: bool,
    /// (LK6) the redex-gating exclusivity core kernel-computed over the
    /// encoded beta_or_iota_step CFG (is_lam partitions β from the ι family).
    pub l_kernel_beta_iota_gating: bool,
    /// (LK7) the mode-fidelity partition kernel-computed over the encoded
    /// whnf_recurse CFG (δ-discipline + cache coherence at saturation fuel).
    pub l_kernel_recurse_mode: bool,
    /// (LK8) the δ-interior partition kernel-computed over the encoded
    /// unfold_definition_cached CFG.
    pub l_kernel_delta_interior: bool,
    /// (LK9) the ι-proj-interior partition kernel-computed over the encoded
    /// reduce_proj_with_mode CFG.
    pub l_kernel_proj_interior: bool,
    /// (LK6) THE SINGLE COMPOSITE THEOREM: one kernel statement conjoining the
    /// payload statement, the three programmatic fact sets (one Eq.refl
    /// computation), and all three model universals — accepted by the kernel in
    /// ONE `check_type` call.
    pub l_kernel_single_theorem: bool,
    /// (M1) `whnf_progress_bd` kernel re-attested (lineage digest hex).
    pub m_progress_lineage: String,
    /// (M2) `whnf_normalizes_bd` kernel re-attested (lineage digest hex).
    pub m_normalizes_lineage: String,
    /// (M3) `step_fixpoint_classifies_bd` — the COMPOSITION GLUE itself
    /// (no-step ⟹ done-or-stuck), kernel re-attested (lineage digest hex). With
    /// this, the inference tying (L)'s fixpoint exits to WHNF-ness is a
    /// kernel-checked theorem, not Rust-side reasoning.
    pub m_glue_lineage: String,
    /// (M4) `whnf_progress_env_bd` — FULL δ-PROGRESS (the DeltaProgress
    /// spec-port capstone: closed + all-consts-defined ⟹ δ-aware whnf exit),
    /// kernel re-attested (lineage digest hex).
    pub m_env_progress_lineage: String,
    /// (M5) `env_fixpoint_classifies_bd` — the δ-AWARE COMPOSITION GLUE
    /// (no β/ζ/head-δ reduct ⟹ done-or-stuck), kernel re-attested (lineage
    /// digest hex). The reducer-universal inference over the FULL default-mode
    /// step family.
    pub m_env_glue_lineage: String,
    /// (M6) `whnf_progress_red_bd` — 3-way progress over the combined RedEnv
    /// step (β/ζ + head-δ + head-ι), kernel re-attested (lineage digest hex).
    /// CAVEAT (audit M5): its consts_defined hypothesis excludes δ-opaque
    /// recursor heads, so it adds no ι-progress content beyond the δ capstone;
    /// ι-liveness is separately witnessed at natrec_fires_red_zero/succ.
    pub m_red_progress_lineage: String,
    /// (M7) `red_fixpoint_classifies_bd` — THE 3-WAY COMPOSITION GLUE (no
    /// β/ζ/head-δ/head-ι reduct ⟹ done-or-stuck), kernel re-attested
    /// (lineage digest hex). Same audit-M5 caveat as M6: the hypothesis
    /// domain excludes δ-opaque recursor heads (no ι content beyond the δ
    /// capstone).
    pub m_red_glue_lineage: String,
    /// (M8) `whnf_fuel_no_redex` — FIXPOINT-ONLY RETURNS of the in-spec
    /// executable loop, kernel re-attested (lineage digest hex).
    pub m_fuel_no_redex_lineage: String,
    /// (M9) `reduce_once_sound` — EXECUTABLE-STEP SOUNDNESS via the spine-δ
    /// correspondence, kernel re-attested (lineage digest hex).
    pub m_reduce_sound_lineage: String,
    /// (M10) `whnf_fuel_reaches_sound` — UNCONDITIONAL REACH of the
    /// executable loop, kernel re-attested (lineage digest hex).
    pub m_fuel_reaches_lineage: String,
    /// SHA-256 over every component verdict + the M lineages — the composite
    /// identity (position-tagged, so a report cannot be replayed piecemeal).
    pub composition_digest: [u8; 32],
}

/// Load one committed real-MIR fixture (same provenance-pinned set the
/// checker_core_is_whnf witnesses use).
fn load_fixture(name: &str) -> Option<VerifiableFunction> {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("fixtures/checker_core_is_whnf_mir")
        .join(name);
    let json = std::fs::read_to_string(path).ok()?;
    serde_json::from_str(&json).ok()
}

/// The (L) component: all four MIR witnesses on the committed real-MIR
/// fixtures, INCLUDING the expected-partition check (the dispatch classes must
/// be exactly the measured ones — a permuted partition fails).
#[allow(clippy::type_complexity)]
fn l_components() -> Option<(bool, bool, bool, bool, bool, bool, bool, bool, bool, bool)> {
    let whnf_impl = load_fixture("clean_kernel.tc.whnf.whnf_impl.json")?;
    let closure1 = load_fixture("clean_kernel.tc.whnf.whnf_impl.closure1.json")?;
    let whnf_inner = load_fixture("clean_kernel.tc.whnf.whnf_inner.json")?;
    let outer_loop = load_fixture("clean_kernel.tc.whnf_proj.whnf_outer_loop.json")?;
    let core_inner = load_fixture("clean_kernel.tc.whnf.whnf_core_inner.json")?;
    let beta_iota = load_fixture("clean_kernel.tc.whnf.beta_or_iota_step.json")?;
    let recurse = load_fixture("clean_kernel.tc.whnf_proj.whnf_recurse.json")?;
    let delta_step = load_fixture("clean_kernel.tc.whnf_proj.unfold_definition_cached.json")?;
    let proj_step = load_fixture("clean_kernel.tc.whnf_proj.reduce_proj_with_mode.json")?;
    let proj_shim = load_fixture("clean_kernel.tc.whnf_proj.whnf_reduce_proj.json")?;

    let expected_core: Vec<usize> = [3usize, 4, 7, 9, 10].into_iter().chain(11..25).collect();
    let dispatch = match whnf_dispatch_partition(&whnf_impl) {
        Some(WhnfDispatchPartition {
            identity_whnf,
            identity_residual,
            fvar_lookup,
            recursive_core,
        }) => {
            identity_whnf == vec![2, 5, 6]
                && identity_residual == vec![0, 8]
                && fvar_lookup == vec![1]
                && recursive_core == expected_core
        }
        None => false,
    };
    Some((
        dispatch,
        whnf_stack_safe_payload_is_whnf_inner(&closure1),
        whnf_inner_is_cached_reducer(&whnf_inner),
        whnf_outer_loop_exits_only_at_fixpoint_cache_or_heartbeat(&outer_loop),
        crate::checker_core_is_whnf::whnf_core_inner_routes_steps_by_kind(&core_inner),
        crate::checker_core_is_whnf::beta_or_iota_step_gates_contraction_by_redex(&beta_iota),
        crate::checker_core_is_whnf::whnf_recurse_routes_by_mode(&recurse),
        crate::checker_core_is_whnf::unfold_definition_cached_delta_interior(&delta_step),
        crate::checker_core_is_whnf::reduce_proj_fires_only_on_constructor(&proj_step),
        crate::checker_core_is_whnf::whnf_reduce_proj_delegates(&proj_shim),
    ))
}

/// The (F) component: the four structural step-fidelity gates plus the two
/// machine-checked scoping facts.
fn f_components() -> (bool, bool) {
    // clean unified the four per-kind whnf/delta/iota/nat step-fidelity audits
    // into one gate over the deterministic core corpus (`audit_fidelity`,
    // fidelity_gate.rs). `passed()` keeps the fail-closed conjunction: it is
    // `false` iff ANY supported term produced a new (non-allowlisted)
    // model↔kernel divergence — the same "all step kinds faithful" fact the
    // four `is_ok()` calls asserted.
    let gates = clean_verify::fidelity_gate::audit_fidelity().passed();

    let scope = {
        use clean_kernel::{Environment, Expr, LevelVec, Name, TypeChecker};
        let env = Environment::new();
        let no_cubical = !env.mode().has_cubical_layer();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let stuck = |head: &str| {
            let e = Expr::app(
                Expr::const_(Name::from_string(head), LevelVec::new()),
                Expr::const_(Name::from_string("Trust.Certify.CompositionTarget"), LevelVec::new()),
            );
            tc.whnf(&e) == e
        };
        no_cubical && stuck("Lean.reduceBool") && stuck("Lean.reduceNat")
    };
    (gates, scope)
}

/// Run the FULL composition — every L, F, and M component — and mint the
/// composite report ONLY if all of them hold. Fail-closed (`None`) on any
/// component failure, any fixture problem, or any attestation failure.
///
/// The M components each rebuild `Specification::new()` and kernel-re-check the
/// registered zero-axiom proof terms (the checker-core attestation lane), so a
/// full composition run takes tens of minutes — it is a VALIDATION artifact,
/// not a hot-path check.
#[must_use]
pub fn certify_reducer_universal_composition() -> Option<ReducerCompositionReport> {
    // (L) — seconds.
    let (l1, l2, l3, l4, l5, l6, l7, l8, l9, l10) = l_components()?;
    if !(l1 && l2 && l3 && l4 && l5 && l6 && l7 && l8 && l9 && l10) {
        return None;
    }
    // (F) — seconds.
    let (f_gates, f_scope) = f_components();
    if !(f_gates && f_scope) {
        return None;
    }
    // (L-KERNEL) — the four kernel-checked reflections against ONE shared spec
    // build: the payload's registered goal pinned byte-identically to the
    // fixture-derived encoding, and the dispatch / cached-reducer /
    // fixpoint-exit reachability goals COMPUTED by the kernel.
    let payload_expected = expected_payload_reflection_goal()?;
    let dispatch_body = dispatch_reflection_body()?;
    let cached_body = cached_reducer_reflection_body()?;
    let fixpoint_body = fixpoint_exit_reflection_body()?;
    let core_routing_body = core_inner_routing_body()?;
    let beta_iota_body = beta_iota_gating_body()?;
    let recurse_body = recurse_mode_body()?;
    let delta_body = delta_interior_body()?;
    let proj_body = proj_interior_body()?;
    let l_kernel = {
        use crate::checker_core::run_on_large_stack;
        run_on_large_stack(move || {
            let spec = clean_verify::spec::Specification::new().ok()?;
            let env: &Environment = spec.env();
            let payload_pinned = spec
                .definitions()
                .get("mir_payload_reflection_whnf_inner")
                .is_some_and(|d| d.type_src == payload_expected);
            // ONE TypeChecker for every goal: its whnf cache carries shared
            // subterm reductions across the individual checks and the single
            // theorem (the band members recur there).
            let tc = clean_kernel::TypeChecker::with_mode(env, env.mode());
            let check_pair = |goal: &Expr, proof: &Expr| tc.check_type(proof, goal).is_ok();
            let check = |body: &Expr| {
                let (goal, proof) = eq_bool_true_pair(body.clone());
                check_pair(&goal, &proof)
            };
            let dispatch_ok = check(&dispatch_body);
            let cached_ok = check(&cached_body);
            let fixpoint_ok = check(&fixpoint_body);
            let core_routing_ok = check(&core_routing_body);
            let beta_iota_ok = check(&beta_iota_body);
            let recurse_ok = check(&recurse_body);
            let delta_ok = check(&delta_body);
            let proj_ok = check(&proj_body);
            // (LK10) the SINGLE THEOREM conjoining every component, one
            // check_type call over the same shared environment.
            let single_ok = single_composite_theorem_pair(
                env,
                [
                    dispatch_body,
                    cached_body,
                    fixpoint_body,
                    core_routing_body,
                    beta_iota_body,
                    recurse_body,
                    delta_body,
                    proj_body,
                ],
            )
            .is_some_and(|(goal, proof)| check_pair(&goal, &proof));
            Some((
                payload_pinned,
                dispatch_ok,
                cached_ok,
                fixpoint_ok,
                core_routing_ok,
                beta_iota_ok,
                recurse_ok,
                delta_ok,
                proj_ok,
                single_ok,
            ))
        })
        .flatten()?
    };
    #[allow(clippy::type_complexity)]
    let (
        lk_payload,
        lk_dispatch,
        lk_cached,
        lk_fixpoint,
        lk_core,
        lk_beta,
        lk_rec,
        lk_delta,
        lk_proj,
        lk_single,
    ) = l_kernel;
    if !(lk_payload
        && lk_dispatch
        && lk_cached
        && lk_fixpoint
        && lk_core
        && lk_beta
        && lk_rec
        && lk_delta
        && lk_proj
        && lk_single)
    {
        return None;
    }
    // (M) — the three kernel re-attestations (spec builds; the expensive part):
    // both model universals AND the composition glue itself.
    let progress = certify_whnf_progress_bd()?;
    let normalizes = certify_whnf_normalizes_bd()?;
    let glue = certify_step_fixpoint_classifies_bd()?;
    let env_progress = certify_whnf_progress_env_bd()?;
    let env_glue = certify_env_fixpoint_classifies_bd()?;
    let red_progress = certify_whnf_progress_red_bd()?;
    let red_glue = certify_red_fixpoint_classifies_bd()?;
    let fuel_no_redex = certify_whnf_fuel_no_redex()?;
    let reduce_sound = certify_reduce_once_sound()?;
    let fuel_reaches = certify_whnf_fuel_reaches_sound()?;
    let (trust_ir::ProofEvidence::CleanCic { lineage: lp, .. },) = (progress,) else {
        return None;
    };
    let (trust_ir::ProofEvidence::CleanCic { lineage: ln, .. },) = (normalizes,) else {
        return None;
    };
    let (trust_ir::ProofEvidence::CleanCic { lineage: lg, .. },) = (glue,) else {
        return None;
    };
    let (trust_ir::ProofEvidence::CleanCic { lineage: lep, .. },) = (env_progress,) else {
        return None;
    };
    let (trust_ir::ProofEvidence::CleanCic { lineage: leg, .. },) = (env_glue,) else {
        return None;
    };
    let (trust_ir::ProofEvidence::CleanCic { lineage: lrp, .. },) = (red_progress,) else {
        return None;
    };
    let (trust_ir::ProofEvidence::CleanCic { lineage: lrg, .. },) = (red_glue,) else {
        return None;
    };
    let (trust_ir::ProofEvidence::CleanCic { lineage: lfn, .. },) = (fuel_no_redex,) else {
        return None;
    };
    let (trust_ir::ProofEvidence::CleanCic { lineage: lrs, .. },) = (reduce_sound,) else {
        return None;
    };
    let (trust_ir::ProofEvidence::CleanCic { lineage: lfr, .. },) = (fuel_reaches,) else {
        return None;
    };
    let m_progress_lineage = hex(&lp.bytes);
    let m_normalizes_lineage = hex(&ln.bytes);
    let m_glue_lineage = hex(&lg.bytes);
    let m_env_progress_lineage = hex(&lep.bytes);
    let m_env_glue_lineage = hex(&leg.bytes);
    let m_red_progress_lineage = hex(&lrp.bytes);
    let m_red_glue_lineage = hex(&lrg.bytes);
    let m_fuel_no_redex_lineage = hex(&lfn.bytes);
    let m_reduce_sound_lineage = hex(&lrs.bytes);
    let m_fuel_reaches_lineage = hex(&lfr.bytes);

    // The composite digest binds every verdict + both M lineages.
    let mut hasher = Sha256::new();
    hasher.update(b"trust-certify.reducer-universal-composition.v1");
    for (tag, bit) in [
        (b"l1".as_slice(), l1),
        (b"l2".as_slice(), l2),
        (b"l3".as_slice(), l3),
        (b"l4".as_slice(), l4),
        (b"l5".as_slice(), l5),
        (b"l6".as_slice(), l6),
        (b"l7".as_slice(), l7),
        (b"l8".as_slice(), l8),
        (b"l9".as_slice(), l9),
        (b"la".as_slice(), l10),
        (b"fg".as_slice(), f_gates),
        (b"fs".as_slice(), f_scope),
        (b"k1".as_slice(), lk_payload),
        (b"k2".as_slice(), lk_dispatch),
        (b"k3".as_slice(), lk_cached),
        (b"k4".as_slice(), lk_fixpoint),
        (b"k5".as_slice(), lk_core),
        (b"k6".as_slice(), lk_beta),
        (b"k7".as_slice(), lk_rec),
        (b"k8".as_slice(), lk_delta),
        (b"k9".as_slice(), lk_proj),
        (b"ka".as_slice(), lk_single),
    ] {
        hasher.update(tag);
        hasher.update([u8::from(bit)]);
    }
    hasher.update(b"mp:");
    hasher.update(m_progress_lineage.as_bytes());
    hasher.update(b"mn:");
    hasher.update(m_normalizes_lineage.as_bytes());
    hasher.update(b"mg:");
    hasher.update(m_glue_lineage.as_bytes());
    hasher.update(b"m4:");
    hasher.update(m_env_progress_lineage.as_bytes());
    hasher.update(b"m5:");
    hasher.update(m_env_glue_lineage.as_bytes());
    hasher.update(b"m6:");
    hasher.update(m_red_progress_lineage.as_bytes());
    hasher.update(b"m7:");
    hasher.update(m_red_glue_lineage.as_bytes());
    hasher.update(b"m8:");
    hasher.update(m_fuel_no_redex_lineage.as_bytes());
    hasher.update(b"m9:");
    hasher.update(m_reduce_sound_lineage.as_bytes());
    hasher.update(b"ma:");
    hasher.update(m_fuel_reaches_lineage.as_bytes());
    let digest = hasher.finalize();
    let mut composition_digest = [0u8; 32];
    composition_digest.copy_from_slice(&digest);

    Some(ReducerCompositionReport {
        l_dispatch_totality: l1,
        l_payload_passthrough: l2,
        l_cached_reducer: l3,
        l_fixpoint_exits: l4,
        l_core_step_routing: l5,
        l_step_redex_gating: l6,
        l_recurse_mode_fidelity: l7,
        l_delta_interior: l8,
        l_proj_interior: l9,
        l_proj_shim: l10,
        f_step_gates: f_gates,
        f_scope,
        l_kernel_payload_pinned: lk_payload,
        l_kernel_dispatch: lk_dispatch,
        l_kernel_cached_reducer: lk_cached,
        l_kernel_fixpoint_exit: lk_fixpoint,
        l_kernel_core_routing: lk_core,
        l_kernel_beta_iota_gating: lk_beta,
        l_kernel_recurse_mode: lk_rec,
        l_kernel_delta_interior: lk_delta,
        l_kernel_proj_interior: lk_proj,
        l_kernel_single_theorem: lk_single,
        m_progress_lineage,
        m_normalizes_lineage,
        m_glue_lineage,
        m_env_progress_lineage,
        m_env_glue_lineage,
        m_red_progress_lineage,
        m_red_glue_lineage,
        m_fuel_no_redex_lineage,
        m_reduce_sound_lineage,
        m_fuel_reaches_lineage,
        composition_digest,
    })
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

// ────────────────────────────────────────────────────────────────────────────
// MIR payload ENCODER — the fidelity pin for the kernel-checked L-witness.
//
// clean-verify registers `mir_payload_reflection_whnf_inner`: the kernel
// COMPUTES `mir_payload_check <encoding> <whnf_inner> = true` (Eq.refl) over a
// kernel-side encoding of the stack_safe payload closure. The RESIDUAL trust of
// that reflection is the encoding's fidelity to the real MIR — closed HERE: the
// encoder below re-derives the canonical encoding from the COMMITTED real-MIR
// fixture, and the pinning test asserts it reproduces the registered kernel
// goal BYTE-IDENTICALLY. Fixture -> encoder -> exact registered goal: any drift
// in the fixture, the encoding scheme, or the registration fails the pin.
// ────────────────────────────────────────────────────────────────────────────

/// `Nat.succ^n Nat.zero` — must match clean-verify's `nat_src` exactly.
fn spec_nat_src(n: usize) -> String {
    let mut s = "Nat.zero".to_string();
    for _ in 0..n {
        s = format!("(Nat.succ {s})");
    }
    s
}

/// The compact injective name code (`c - 94` over `[_a-z]`) — must match
/// clean-verify's `name_src` exactly. Fail-closed (`None`) outside the domain.
fn spec_name_src(text: &str) -> Option<String> {
    let mut s = "Name.anonymous".to_string();
    for c in text.chars() {
        if !(c == '_' || c.is_ascii_lowercase()) {
            return None;
        }
        s = format!("(Name.str {s} {})", spec_nat_src((c as usize) - 94));
    }
    Some(s)
}

/// Encode the REAL stack_safe payload closure MIR as the canonical kernel-side
/// `PayloadBody` source. Fail-closed (`None`) unless the body has EXACTLY the
/// payload shape (two blocks; block 0 = capture unpacks + one Opaque call whose
/// callee's final segment is in the name-code domain; block 1 = bare return; no
/// statement writes `_0`) — the SAME checks as
/// [`crate::checker_core_is_whnf::whnf_stack_safe_payload_is_whnf_inner`], here
/// producing the encoding the kernel-checked theorem consumes.
fn encode_payload_body(func: &VerifiableFunction) -> Option<String> {
    use trust_types::{Operand, Projection, Rvalue, Statement, Terminator};
    if func.body.blocks.len() != 2 {
        return None;
    }
    let b0 = &func.body.blocks[0];
    let b1 = &func.body.blocks[1];
    if !b1.stmts.is_empty() || !matches!(b1.terminator, Terminator::Return) {
        return None;
    }
    // Statements: classify exactly as the spec model does.
    let mut stmts_src = "(ListType.nil MirStmt)".to_string();
    for s in b0.stmts.iter().rev() {
        let Statement::Assign { place, rvalue, .. } = s else {
            return None; // non-assign in the payload block: not the shape
        };
        if place.local == 0 {
            return None; // a _0 writer: not the pure-passthrough shape
        }
        let (Rvalue::Use(Operand::Copy(src)) | Rvalue::Use(Operand::Move(src))) = rvalue else {
            return None;
        };
        if src.local != 1 || !matches!(src.projections.first(), Some(Projection::Field(_))) {
            return None;
        }
        stmts_src = format!(
            "(ListType.cons MirStmt (MirStmt.unpack {}) {stmts_src})",
            spec_nat_src(place.local)
        );
    }
    // Terminator: the Opaque-encoded call; extract the callee's FINAL segment.
    let Terminator::Opaque { kind, targets, .. } = &b0.terminator else {
        return None;
    };
    if !kind.starts_with("Call::") || targets.as_slice() != [trust_types::BlockId(1)] {
        return None;
    }
    let path = kind.trim_start_matches("Call::");
    let path = path.split("::Unsupported").next()?;
    let final_segment = path.rsplit("::").next()?;
    let callee = spec_name_src(final_segment)?;
    Some(format!(
        "(PayloadBody.mk2 (MirBlock.mk {stmts_src} (MirTerm.opaque_call {callee})) \
         (MirBlock.mk (ListType.nil MirStmt) MirTerm.ret))"
    ))
}

/// The full registered kernel goal reproduced from the REAL fixture: the pin
/// target for `mir_payload_reflection_whnf_inner`'s `type_src`.
#[must_use]
pub fn expected_payload_reflection_goal() -> Option<String> {
    let closure = load_fixture("clean_kernel.tc.whnf.whnf_impl.closure1.json")?;
    let encoded = encode_payload_body(&closure)?;
    let callee = spec_name_src("whnf_inner")?;
    Some(format!("Eq Bool (mir_payload_check {encoded} {callee}) Bool.true"))
}

// ────────────────────────────────────────────────────────────────────────────
// FIXPOINT-EXIT reflection — the kernel re-checks the loop's reachability facts.
//
// The whnf_outer_loop graph (87 blocks) exceeds the term parser's 128-deep
// nesting limit, so the encoding is built PROGRAMMATICALLY as `Expr`s (no
// parser) against the kernel-registered CFG substrate (`MirNode`, `mir_reaches`
// with the kernel-side cut edge). The kernel then COMPUTES the same five
// reachability facts the Rust witness checks — including the LOAD-BEARING
// NEGATIVE (changed+miss cannot exit) — and the goal closes by `Eq.refl`.
// ────────────────────────────────────────────────────────────────────────────

use clean_kernel::{Environment, Expr, LevelVec, Name};

fn kc(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), LevelVec::new())
}

/// `Nat.succ^n Nat.zero` as an `Expr` (no parser — no depth limit).
fn nat_expr(n: usize) -> Expr {
    let mut e = kc("Nat.zero");
    for _ in 0..n {
        e = Expr::app(kc("Nat.succ"), e);
    }
    e
}

/// `ListType Nat` literal from ids.
fn nat_list_expr(xs: &[usize]) -> Expr {
    let mut e = Expr::app(kc("ListType.nil"), kc("Nat"));
    for x in xs.iter().rev() {
        e = Expr::apps(kc("ListType.cons"), [kc("Nat"), nat_expr(*x), e]);
    }
    e
}

/// The encoded CFG of `func` as a `ListType MirNode` — id + successors per
/// block, the SAME edge relation the Rust witnesses walk (`block_successors`).
fn graph_expr(func: &VerifiableFunction) -> Option<Expr> {
    let mut e = Expr::app(kc("ListType.nil"), kc("MirNode"));
    for bb in func.body.blocks.iter().rev() {
        let succs: Vec<usize> = crate::checker_core_is_whnf::block_successors(func, bb.id)?
            .into_iter()
            .map(|b| b.0)
            .collect();
        let node = Expr::apps(kc("MirNode.mk"), [nat_expr(bb.id.0), nat_list_expr(&succs)]);
        e = Expr::apps(kc("ListType.cons"), [kc("MirNode"), node, e]);
    }
    Some(e)
}

/// `mir_reaches g cf ct fuel start target` as an `Expr`.
fn reaches_expr(g: &Expr, cf: usize, ct: usize, fuel: usize, start: usize, target: usize) -> Expr {
    Expr::apps(
        kc("mir_reaches"),
        [g.clone(), nat_expr(cf), nat_expr(ct), nat_expr(fuel), nat_expr(start), nat_expr(target)],
    )
}

/// KERNEL-CHECKED FIXPOINT-EXIT REFLECTION: encode the real `whnf_outer_loop`
/// CFG, derive the semantic landmarks (the SAME fail-closed derivation the Rust
/// witness uses), and have the KERNEL compute the five reachability facts —
/// with the backedge cut applied KERNEL-SIDE — closing the conjunction by
/// `Eq.refl`:
///
///   reaches(hb_bail -> ret) ∧ reaches(fixpoint -> ret) ∧ reaches(hit -> ret)
///   ∧ ¬reaches(miss -> ret) ∧ reaches(miss -> backedge)      [all under the cut]
///
/// Fail-closed (`None`) on any fixture/landmark/spec failure; `Some(true)` only
/// if the kernel ACCEPTS the computed goal. The residual is the graph encoder
/// (`block_successors` — the same relation the Rust witnesses walk).
/// KERNEL-CHECKED DISPATCH REFLECTION: encode the outer `whnf_impl` kind-switch
/// arms as `(variant, is_identity)` pairs — the identity classification derived
/// by the SAME copy-trace read the Rust witness uses (the encoder residual) —
/// and have the KERNEL check the partition facts (`mir_arms_ok_from`: every
/// variant < 25, strictly increasing, identity flags exactly on {0,2,5,6,8},
/// the single non-identity arm = FVar 1) PLUS the routing fact as kernel-computed
/// reachability: the `otherwise` complement reaches the `stack_safe` call block
/// over the encoded whnf_impl CFG. Closes by `Eq.refl`. The fourth L-witness's
/// kernel half.
fn dispatch_reflection_goal() -> Option<(Expr, Expr)> {
    Some(eq_bool_true_pair(dispatch_reflection_body()?))
}

fn dispatch_reflection_body() -> Option<Expr> {
    use trust_types::Terminator;

    let whnf_impl = load_fixture("clean_kernel.tc.whnf.whnf_impl.json")?;
    // The switch arms with the SAME identity classification the witness uses.
    let (arg_local, targets, otherwise) =
        crate::checker_core_is_whnf::whnf_kind_switch_public(&whnf_impl)?;
    let mut arms: Vec<(usize, bool)> = Vec::new();
    for (value, target) in &targets {
        let v = usize::try_from(*value).ok()?;
        let ident = crate::checker_core_is_whnf::block_returns_clone_of_arg_public(
            &whnf_impl, *target, arg_local,
        );
        arms.push((v, ident));
    }
    arms.sort_unstable();

    // The stack_safe call block (writes _0) — the routing target.
    let mut stack_safe = None;
    for bb in &whnf_impl.body.blocks {
        if let Terminator::Call { func: callee, dest, .. } = &bb.terminator
            && callee.rsplit("::").next() == Some("stack_safe")
            && dest.local == 0
        {
            if stack_safe.is_some() {
                return None;
            }
            stack_safe = Some(bb.id);
        }
    }
    let stack_safe = stack_safe?;

    // Kernel goal: arms_ok(25, 0, <encoded arms>) ∧ reaches(otherwise -> stack_safe).
    let mut arms_expr = Expr::app(kc("ListType.nil"), kc("MirArm"));
    for (v, ident) in arms.iter().rev() {
        let flag = if *ident { kc("Bool.true") } else { kc("Bool.false") };
        let arm = Expr::apps(kc("MirArm.mk"), [nat_expr(*v), flag]);
        arms_expr = Expr::apps(kc("ListType.cons"), [kc("MirArm"), arm, arms_expr]);
    }
    let arms_ok = Expr::apps(
        kc("mir_arms_ok_from"),
        [nat_expr(25), nat_expr(0), arms_expr],
    );
    let g = graph_expr(&whnf_impl)?;
    let n = whnf_impl.body.blocks.len();
    let routing = reaches_expr(&g, n, n, n, otherwise.0, stack_safe.0);
    Some(Expr::apps(kc("mir_band"), [arms_ok, routing]))
}

/// KERNEL-CHECKED REDEX-GATING REFLECTION body: encode the real
/// `beta_or_iota_step` CFG (101 blocks) and have the KERNEL compute the
/// exclusivity core of the redex-gated contraction — the is_lam test partitions
/// β (`instantiate_rev`) from the ι-family reducers:
///
///   POS (fuel 32 — actual distances ≤ 18):
///     β-arm → instantiate_rev, ι-arm → try_iota, ι-arm → reduce_native
///   NEG (fuel = node count — the graph is cyclic, four internal loops):
///     β-arm ¬→ try_iota, ι-arm ¬→ instantiate_rev
///
/// The load-bearing exclusion: β fires ONLY on a lambda head, the ι family ONLY
/// on a non-lambda. No dispatch backedge (a single step), so the cut is a
/// sentinel no-op. Fail-closed.
fn beta_iota_gating_body() -> Option<Expr> {
    let step = load_fixture("clean_kernel.tc.whnf.beta_or_iota_step.json")?;
    let lm = crate::checker_core_is_whnf::beta_iota_landmarks(&step)?;
    if !crate::checker_core_is_whnf::beta_or_iota_step_gates_contraction_by_redex(&step) {
        return None;
    }
    let g = graph_expr(&step)?;
    let n = step.body.blocks.len();
    let (cf, ct) = (n, n); // sentinel: no edge (n, n) — a no-op cut (no backedge)
    let subst = lm.instantiate_rev.0;
    let try_iota = lm.iota_reducers[0].0;
    let reduce_native = lm.iota_reducers[4].0;
    let (beta, iota) = (lm.beta_arm.0, lm.iota_arm.0);

    let conj = |a: Expr, b: Expr| Expr::apps(kc("mir_band"), [a, b]);
    let neg = |a: Expr| Expr::app(kc("mir_bnot"), a);
    let pos = |start: usize, target: usize| reaches_expr(&g, cf, ct, 32, start, target);
    let sat = |start: usize, target: usize| reaches_expr(&g, cf, ct, n, start, target);
    let body = conj(
        pos(beta, subst),
        conj(
            pos(iota, try_iota),
            conj(
                pos(iota, reduce_native),
                conj(neg(sat(beta, try_iota)), neg(sat(iota, subst))),
            ),
        ),
    );
    Some(body)
}

fn beta_iota_gating_goal() -> Option<(Expr, Expr)> {
    Some(eq_bool_true_pair(beta_iota_gating_body()?))
}

#[must_use]
pub fn certify_beta_iota_gating_reflection() -> Option<bool> {
    run_reflection(beta_iota_gating_goal()?)
}

/// KERNEL-CHECKED STEP-ROUTING REFLECTION body: encode the real
/// `whnf_core_inner` CFG and have the KERNEL compute the load-bearing skeleton
/// of the per-iteration step-routing partition — with the single loop backedge
/// cut KERNEL-SIDE:
///
///   POS (fuel 32 — sound-if-true, the kernel validates the bound suffices):
///     Const→δ, App→β/ι, Proj→ι-proj, PathApp→path-β, HComp→kan-hcomp
///   NEG (fuel = node count — the universal saturation bound, sound):
///     App¬→δ, Const¬→β/ι, App¬→kan-hcomp — the EXCLUSIVITY TRIANGLE
///
/// (the FULL 10-arm × 12-callee exactness lives in the Rust witness
/// `whnf_core_inner_routes_steps_by_kind`; the kernel re-derives the
/// exclusivity core: δ only from Const, β/ι only from App, kan only under its
/// cubical kind. `mir_reaches` iterates FULL frontier rounds, so n rounds
/// always saturate; the negatives carry that fuel, the positives don't need it.)
fn core_inner_routing_body() -> Option<Expr> {
    let core = load_fixture("clean_kernel.tc.whnf.whnf_core_inner.json")?;
    let lm = crate::checker_core_is_whnf::core_routing_landmarks(&core)?;
    if !crate::checker_core_is_whnf::whnf_core_inner_routes_steps_by_kind(&core) {
        return None;
    }
    let g = graph_expr(&core)?;
    let fuel = core.body.blocks.len();
    let (cf, ct) = (lm.backedge_from.0, lm.head.0);
    let arm = |v: usize| -> Option<usize> {
        lm.arms.iter().find(|(av, _)| *av == v).map(|(_, t)| t.0)
    };
    let (konst, app, proj, path_app, hcomp) = (arm(3)?, arm(4)?, arm(9)?, arm(18)?, arm(19)?);

    let conj = |a: Expr, b: Expr| Expr::apps(kc("mir_band"), [a, b]);
    let neg = |a: Expr| Expr::app(kc("mir_bnot"), a);
    let pos = |start: usize, target: usize| reaches_expr(&g, cf, ct, 32, start, target);
    let sat = |start: usize, target: usize| reaches_expr(&g, cf, ct, fuel, start, target);
    let body = conj(
        pos(konst, lm.delta_unfold.0),
        conj(
            pos(app, lm.beta_iota[0].0),
            conj(
                pos(proj, lm.iota_proj.0),
                conj(
                    pos(path_app, lm.path_beta.0),
                    conj(
                        pos(hcomp, lm.kan_hcomp.0),
                        conj(
                            neg(sat(app, lm.delta_unfold.0)),
                            conj(
                                neg(sat(konst, lm.beta_iota[0].0)),
                                neg(sat(app, lm.kan_hcomp.0)),
                            ),
                        ),
                    ),
                ),
            ),
        ),
    );
    Some(body)
}

fn core_inner_routing_goal() -> Option<(Expr, Expr)> {
    Some(eq_bool_true_pair(core_inner_routing_body()?))
}

#[must_use]
pub fn certify_core_inner_routing_reflection() -> Option<bool> {
    run_reflection(core_inner_routing_goal()?)
}

/// KERNEL-CHECKED MODE-FIDELITY REFLECTION body: encode the real
/// `whnf_recurse` CFG (31 blocks, acyclic live region) and have the KERNEL
/// compute the mode-routing partition — Full/NoDelta/Transparency reach
/// DISJOINT reducers, with the δ-DISCIPLINE negative (NoDelta ¬→ whnf_impl)
/// and cache coherence (hit ¬→ reducer/insert, miss → reducer). The graph is
/// tiny, so EVERY fact runs at saturation fuel = node count. Fail-closed.
fn recurse_mode_body() -> Option<Expr> {
    let rec = load_fixture("clean_kernel.tc.whnf_proj.whnf_recurse.json")?;
    let lm = crate::checker_core_is_whnf::recurse_mode_landmarks(&rec)?;
    if !crate::checker_core_is_whnf::whnf_recurse_routes_by_mode(&rec) {
        return None;
    }
    let g = graph_expr(&rec)?;
    let n = rec.body.blocks.len();
    let (cf, ct) = (n, n); // sentinel no-op cut (acyclic live region)

    let conj = |a: Expr, b: Expr| Expr::apps(kc("mir_band"), [a, b]);
    let neg = |a: Expr| Expr::app(kc("mir_bnot"), a);
    let r = |start: usize, target: usize| reaches_expr(&g, cf, ct, n, start, target);
    let body = conj(
        r(lm.full_arm.0, lm.whnf_impl.0),
        conj(
            neg(r(lm.full_arm.0, lm.cache_get.0)),
            conj(
                r(lm.nodelta_arm.0, lm.cache_get.0),
                conj(
                    r(lm.nodelta_arm.0, lm.nodelta_stack_safe.0),
                    conj(
                        // δ-DISCIPLINE: NoDelta cannot reach the δ-enabled impl.
                        neg(r(lm.nodelta_arm.0, lm.whnf_impl.0)),
                        conj(
                            r(lm.transp_arm.0, lm.transp_arm.0),
                            conj(
                                neg(r(lm.transp_arm.0, lm.whnf_impl.0)),
                                conj(
                                    r(lm.hit_arm.0, lm.ret.0),
                                    conj(
                                        neg(r(lm.hit_arm.0, lm.nodelta_stack_safe.0)),
                                        r(lm.miss_arm.0, lm.nodelta_stack_safe.0),
                                    ),
                                ),
                            ),
                        ),
                    ),
                ),
            ),
        ),
    );
    Some(body)
}

fn recurse_mode_goal() -> Option<(Expr, Expr)> {
    Some(eq_bool_true_pair(recurse_mode_body()?))
}

#[must_use]
pub fn certify_recurse_mode_reflection() -> Option<bool> {
    run_reflection(recurse_mode_goal()?)
}

/// KERNEL-CHECKED δ-INTERIOR REFLECTION body: encode the real
/// `unfold_definition_cached` CFG (30 blocks, acyclic live region) and have
/// the KERNEL compute the interior partition — the env unfold fires ONLY on a
/// cache-missing Const-kind expr; hit/non-Const/None never unfold or insert;
/// Some inserts. All facts at saturation fuel (tiny graph). Fail-closed.
fn delta_interior_body() -> Option<Expr> {
    let step = load_fixture("clean_kernel.tc.whnf_proj.unfold_definition_cached.json")?;
    let lm = crate::checker_core_is_whnf::delta_step_landmarks(&step)?;
    if !crate::checker_core_is_whnf::unfold_definition_cached_delta_interior(&step) {
        return None;
    }
    let g = graph_expr(&step)?;
    let n = step.body.blocks.len();
    let (cf, ct) = (n, n);

    let conj = |a: Expr, b: Expr| Expr::apps(kc("mir_band"), [a, b]);
    let neg = |a: Expr| Expr::app(kc("mir_bnot"), a);
    let r = |start: usize, target: usize| reaches_expr(&g, cf, ct, n, start, target);
    let body = conj(
        r(lm.hit_arm.0, lm.ret.0),
        conj(
            neg(r(lm.hit_arm.0, lm.env_unfold.0)),
            conj(
                neg(r(lm.hit_arm.0, lm.insert.0)),
                conj(
                    neg(r(lm.nonconst_arm.0, lm.env_unfold.0)),
                    conj(
                        neg(r(lm.nonconst_arm.0, lm.insert.0)),
                        conj(
                            r(lm.const_arm.0, lm.env_unfold.0),
                            conj(
                                r(lm.some_arm.0, lm.insert.0),
                                neg(r(lm.none_arm.0, lm.insert.0)),
                            ),
                        ),
                    ),
                ),
            ),
        ),
    );
    Some(body)
}

fn delta_interior_goal() -> Option<(Expr, Expr)> {
    Some(eq_bool_true_pair(delta_interior_body()?))
}

#[must_use]
pub fn certify_delta_interior_reflection() -> Option<bool> {
    run_reflection(delta_interior_goal()?)
}

/// KERNEL-CHECKED ι-PROJ-INTERIOR REFLECTION body: encode the real
/// `reduce_proj_with_mode` CFG (45 blocks, acyclic live region) and have the
/// KERNEL compute the interior partition — field extraction fires exactly on a
/// constructor-headed struct with the field present; every complement rebuilds
/// the honest stuck proj. All facts at saturation fuel. Fail-closed.
fn proj_interior_body() -> Option<Expr> {
    let step = load_fixture("clean_kernel.tc.whnf_proj.reduce_proj_with_mode.json")?;
    let lm = crate::checker_core_is_whnf::proj_step_landmarks(&step)?;
    if !crate::checker_core_is_whnf::reduce_proj_fires_only_on_constructor(&step) {
        return None;
    }
    let g = graph_expr(&step)?;
    let n = step.body.blocks.len();
    let (cf, ct) = (n, n);

    let conj = |a: Expr, b: Expr| Expr::apps(kc("mir_band"), [a, b]);
    let neg = |a: Expr| Expr::app(kc("mir_bnot"), a);
    let r = |start: usize, target: usize| reaches_expr(&g, cf, ct, n, start, target);
    let body = conj(
        r(lm.stuck_arm.0, lm.proj_rebuild.0),
        conj(
            neg(r(lm.stuck_arm.0, lm.get_constructor.0)),
            conj(
                neg(r(lm.stuck_arm.0, lm.slice_get.0)),
                conj(
                    neg(r(lm.stuck_arm.0, lm.field_recurse.0)),
                    conj(
                        r(lm.const_head_arm.0, lm.get_constructor.0),
                        conj(
                            r(lm.found_arm.0, lm.slice_get.0),
                            conj(
                                r(lm.field_arm.0, lm.ret.0),
                                conj(
                                    neg(r(lm.field_arm.0, lm.proj_rebuild.0)),
                                    conj(
                                        r(lm.nofield_arm.0, lm.proj_rebuild.0),
                                        neg(r(lm.nofield_arm.0, lm.field_recurse.0)),
                                    ),
                                ),
                            ),
                        ),
                    ),
                ),
            ),
        ),
    );
    Some(body)
}

fn proj_interior_goal() -> Option<(Expr, Expr)> {
    Some(eq_bool_true_pair(proj_interior_body()?))
}

#[must_use]
pub fn certify_proj_interior_reflection() -> Option<bool> {
    run_reflection(proj_interior_goal()?)
}

/// `(goal, proof)` for `Eq Bool <body> Bool.true` via `Eq.refl`. The kernel's
/// Eq/Eq.refl are universe-polymorphic: Bool : Sort 1 => level [1] (measured:
/// a level-less Const is rejected).
fn eq_bool_true_pair(body: Expr) -> (Expr, Expr) {
    let lv = vec![clean_kernel::Level::succ(clean_kernel::Level::zero())];
    let goal = Expr::apps(
        Expr::const_(Name::from_string("Eq"), lv.clone()),
        [kc("Bool"), body, kc("Bool.true")],
    );
    let proof =
        Expr::apps(Expr::const_(Name::from_string("Eq.refl"), lv), [kc("Bool"), kc("Bool.true")]);
    (goal, proof)
}

/// Run one `(goal, proof)` pair against a FRESH spec build (standalone entry).
fn run_reflection(pair: (Expr, Expr)) -> Option<bool> {
    use crate::checker_core::{kernel_checks_goal, run_on_large_stack};
    let (goal, proof) = pair;
    run_on_large_stack(move || {
        let spec = clean_verify::spec::Specification::new().ok()?;
        let env: &Environment = spec.env();
        Some(kernel_checks_goal(env, &proof, &goal))
    })
    .flatten()
}

#[must_use]
pub fn certify_dispatch_reflection() -> Option<bool> {
    run_reflection(dispatch_reflection_goal()?)
}

/// KERNEL-CHECKED CACHED-REDUCER REFLECTION: encode the real `whnf_inner`
/// CFG and have the KERNEL compute the cache-wrapper facts — plain
/// reachability (a sentinel no-op cut), same substrate:
///
///   reaches(miss -> reducer) ∧ ¬reaches(hit -> reducer)
///   ∧ ¬reaches(hit -> insert) ∧ reaches(after_reducer -> insert)
///
/// closing by `Eq.refl`. The third L-witness fact set computed in the kernel.
#[must_use]
pub fn certify_cached_reducer_reflection() -> Option<bool> {
    run_reflection(cached_reducer_reflection_goal()?)
}

fn cached_reducer_reflection_goal() -> Option<(Expr, Expr)> {
    Some(eq_bool_true_pair(cached_reducer_reflection_body()?))
}

fn cached_reducer_reflection_body() -> Option<Expr> {
    let inner = load_fixture("clean_kernel.tc.whnf.whnf_inner.json")?;
    let lm = crate::checker_core_is_whnf::cached_reducer_landmarks(&inner)?;
    let g = graph_expr(&inner)?;
    let n = inner.body.blocks.len();
    let (cf, ct) = (n, n); // sentinel: no edge (n, n) exists — a no-op cut
    let fuel = n;

    let conj = |a: Expr, b: Expr| Expr::apps(kc("mir_band"), [a, b]);
    let neg = |a: Expr| Expr::app(kc("mir_bnot"), a);
    let body = conj(
        reaches_expr(&g, cf, ct, fuel, lm.miss_arm.0, lm.reducer.0),
        conj(
            neg(reaches_expr(&g, cf, ct, fuel, lm.hit_arm.0, lm.reducer.0)),
            conj(
                neg(reaches_expr(&g, cf, ct, fuel, lm.hit_arm.0, lm.insert.0)),
                reaches_expr(&g, cf, ct, fuel, lm.after_reducer.0, lm.insert.0),
            ),
        ),
    );
    Some(body)
}

#[must_use]
pub fn certify_fixpoint_exit_reflection() -> Option<bool> {
    run_reflection(fixpoint_exit_reflection_goal()?)
}

fn fixpoint_exit_reflection_goal() -> Option<(Expr, Expr)> {
    Some(eq_bool_true_pair(fixpoint_exit_reflection_body()?))
}

fn fixpoint_exit_reflection_body() -> Option<Expr> {
    let outer = load_fixture("clean_kernel.tc.whnf_proj.whnf_outer_loop.json")?;
    let lm = crate::checker_core_is_whnf::fixpoint_exit_landmarks(&outer)?;
    let g = graph_expr(&outer)?;
    let fuel = outer.body.blocks.len(); // sound: ≥ any reachability saturation
    let (cf, ct) = (lm.backedge_from.0, lm.heartbeat.0);

    let conj = |a: Expr, b: Expr| Expr::apps(kc("mir_band"), [a, b]);
    let neg = |a: Expr| Expr::app(kc("mir_bnot"), a);
    let body = conj(
        reaches_expr(&g, cf, ct, fuel, lm.hb_bail.0, lm.ret.0),
        conj(
            reaches_expr(&g, cf, ct, fuel, lm.fixpoint_arm.0, lm.ret.0),
            conj(
                reaches_expr(&g, cf, ct, fuel, lm.hit_arm.0, lm.ret.0),
                conj(
                    neg(reaches_expr(&g, cf, ct, fuel, lm.miss_arm.0, lm.ret.0)),
                    reaches_expr(&g, cf, ct, fuel, lm.miss_arm.0, lm.backedge_from.0),
                ),
            ),
        ),
    );
    Some(body)
}

// ────────────────────────────────────────────────────────────────────────────
// THE SINGLE COMPOSITE THEOREM — one kernel statement conjoining EVERY
// reflected component, checked in ONE `check_type` call:
//
//   AndType (LiftP <payload statement — the registered, byte-pinned Eq goal>)
//     (AndType (LiftP (Eq Bool (dispatch ∧b cached ∧b fixpoint) Bool.true))
//       (AndType <whnf_progress_bd statement>
//         (AndType <whnf_normalizes_bd statement>
//           <step_fixpoint_classifies_bd statement>)))
//
// proved by `AndType.intro` over the registered proof CONSTANTS (each
// kernel-checked at registration, zero axiom deps) + ONE `Eq.refl` that makes
// the kernel COMPUTE all three programmatic CFG fact sets at once. `LiftP`
// (spec-registered Prop→Type lift) bridges the Prop-sorted Eq facts into the
// Type-sorted AndType chain; each conjunct is lifted exactly when its
// kernel-inferred sort is Prop (fail-closed — a wrong sort is a kernel
// rejection, never a silent skip). The statements are fetched from the LIVE
// environment (never re-typed by hand), so the theorem asserts precisely what
// the spec registered.
// ────────────────────────────────────────────────────────────────────────────

/// Build the single composite `(goal, proof)` against the live environment.
/// `bodies` are the eight programmatic Bool fact-set bodies (dispatch,
/// cached-reducer, fixpoint-exit, core step routing, β/ι redex gating,
/// whnf_recurse mode fidelity, δ interior, ι-proj interior).
fn single_composite_theorem_pair(env: &Environment, bodies: [Expr; 8]) -> Option<(Expr, Expr)> {
    use clean_kernel::{Level, TypeChecker};

    let tc = TypeChecker::with_mode(env, env.mode());
    // A registered statement + its proof constant (monomorphic reference only).
    let registered = |name: &str| -> Option<(Expr, Expr)> {
        let n = Name::from_string(name);
        let ci = env.get_const(&n)?;
        if !ci.level_params.is_empty() {
            return None;
        }
        Some((ci.type_.clone(), Expr::const_(n, LevelVec::new())))
    };
    // Lift a Prop-sorted conjunct into Type via the spec-registered LiftP.
    let lifted = |(stmt, proof): (Expr, Expr)| -> Option<(Expr, Expr)> {
        match tc.infer_sort(&stmt) {
            Ok(level) if level == Level::zero() => Some((
                Expr::app(kc("LiftP"), stmt.clone()),
                Expr::apps(kc("LiftP.up"), [stmt, proof]),
            )),
            Ok(_) => Some((stmt, proof)),
            Err(_) => None,
        }
    };

    let [dispatch_body, cached_body, fixpoint_body, core_routing_body, beta_iota_body, recurse_body, delta_body, proj_body] =
        bodies;
    let band = |a: Expr, b: Expr| Expr::apps(kc("mir_band"), [a, b]);
    let programmatic = eq_bool_true_pair(band(
        band(band(dispatch_body, cached_body), band(fixpoint_body, core_routing_body)),
        band(band(beta_iota_body, recurse_body), band(delta_body, proj_body)),
    ));

    let parts = [
        lifted(registered("mir_payload_reflection_whnf_inner")?)?,
        lifted(programmatic)?,
        lifted(registered("whnf_progress_bd")?)?,
        lifted(registered("whnf_normalizes_bd")?)?,
        lifted(registered("step_fixpoint_classifies_bd")?)?,
    ];

    // Right-associated AndType chain with explicit constructor type args.
    let mut it = parts.into_iter().rev();
    let (mut goal, mut proof) = it.next()?;
    for (t, p) in it {
        let next_goal = Expr::apps(kc("AndType"), [t.clone(), goal.clone()]);
        proof = Expr::apps(kc("AndType.intro"), [t, goal, p, proof]);
        goal = next_goal;
    }
    Some((goal, proof))
}

/// STANDALONE entry: build a fresh spec and kernel-check the single composite
/// theorem (byte-pinning the payload conjunct first). `Some(true)` only if the
/// kernel ACCEPTS the whole conjunction in one `check_type` call.
#[must_use]
pub fn certify_single_composite_theorem() -> Option<bool> {
    use crate::checker_core::{kernel_checks_goal, run_on_large_stack};
    let payload_expected = expected_payload_reflection_goal()?;
    let dispatch_body = dispatch_reflection_body()?;
    let cached_body = cached_reducer_reflection_body()?;
    let fixpoint_body = fixpoint_exit_reflection_body()?;
    let core_routing_body = core_inner_routing_body()?;
    let beta_iota_body = beta_iota_gating_body()?;
    let recurse_body = recurse_mode_body()?;
    let delta_body = delta_interior_body()?;
    let proj_body = proj_interior_body()?;
    run_on_large_stack(move || {
        let spec = clean_verify::spec::Specification::new().ok()?;
        let env: &Environment = spec.env();
        let pinned = spec
            .definitions()
            .get("mir_payload_reflection_whnf_inner")
            .is_some_and(|d| d.type_src == payload_expected);
        if !pinned {
            return Some(false);
        }
        let pair = single_composite_theorem_pair(
            env,
            [
                dispatch_body,
                cached_body,
                fixpoint_body,
                core_routing_body,
                beta_iota_body,
                recurse_body,
                delta_body,
                proj_body,
            ],
        )?;
        Some(kernel_checks_goal(env, &pair.1, &pair.0))
    })
    .flatten()
}

// SLOW-LANE SPLIT (2026-07-20, owner-approved). The kernel-derivation tests in
// this module (*_kernel_checks, *_reflection_pins_to_real_fixture,
// reducer_universal_composition_closes) re-derive the full N-brick kernel
// composite (~3.5h, and it grows with every brick added). That exceeds the
// `quick` domination gate's 2h step budget (GATE_STEP_TIMEOUT), so those tests
// carry #[ignore] and are excluded from `targo test --workspace --lib`. They
// still run — and MUST stay green — in the opt-in composite lane:
//     scripts/trust_kernel_derivation_lane.sh reducer_universal_composition
// The CHEAP component/digest/encoder tests below stay inline and DO run in
// `quick`, so the fast lane still catches drift in the composite's inputs.
#[cfg(test)]
mod tests {
    use super::*;
    use crate::checker_core::run_on_large_stack;

    /// The CHEAP components close and fail closed: (L) + (F) hold on the real
    /// fixtures/gates, and a tampered L input fails the composite's L check.
    #[test]
    fn composition_l_and_f_components_hold_and_fail_closed() {
        let (l1, l2, l3, l4, l5, l6, l7, l8, l9, l10) =
            l_components().expect("fixtures must load");
        assert!(l1, "dispatch totality must hold with the expected classes");
        assert!(l2, "payload passthrough must hold");
        assert!(l3, "cached reducer must hold");
        assert!(l4, "fixpoint exits must hold");
        assert!(l5, "core step routing must hold");
        assert!(l6, "beta/iota redex gating must hold");
        assert!(l7, "whnf_recurse mode fidelity must hold");
        assert!(l8, "delta interior must hold");
        assert!(l9, "proj interior must hold");
        assert!(l10, "proj shim must delegate");
        let (fg, fs) = f_components();
        assert!(fg, "all four step-fidelity gates must pass");
        assert!(fs, "the machine-checked scope facts must hold");
    }

    /// SHA-256 over the structural (Debug) form of a `(goal, proof)` pair.
    fn goal_digest(pair: &(Expr, Expr)) -> String {
        let mut h = Sha256::new();
        h.update(format!("{:?}", pair.0).as_bytes());
        h.update(b"|");
        h.update(format!("{:?}", pair.1).as_bytes());
        h.finalize().iter().map(|b| format!("{b:02x}")).collect()
    }

    /// ENCODER DRIFT PINS: the three PROGRAMMATIC goal encoders (dispatch /
    /// cached-reducer / fixpoint-exit) are digest-pinned, the same role the
    /// byte-pin plays for the payload's source-text goal. The kernel checks
    /// each goal's TRUTH at certify time; these pins close the residual
    /// "encoder silently weakened into a different-but-still-true goal" gap.
    /// (Digests are over the kernel `Expr` Debug form — stable while the
    /// clean pin is stable; a pin bump that changes it fails LOUDLY here.)
    /// THE SINGLE COMPOSITE THEOREM kernel-checks: one statement conjoining
    /// the payload theorem, all three programmatic CFG fact sets, and the
    /// three model universals — accepted by the kernel in one check_type
    /// call. SLOW (one full spec build).
    /// Both step-INTERIOR partitions kernel-check over the encoded
    /// unfold_definition_cached + reduce_proj_with_mode CFGs. SLOW (spec
    /// builds; the facts are cheap — 30/45-node graphs).
    #[test]
    #[ignore = "multi-hour kernel-composite derivation (~3.5h, grows per brick): moved to the opt-in SLOW LANE so `targo test --workspace --lib` (the `quick` domination gate) stays under its 2h step budget. Run this composite via `scripts/trust_kernel_derivation_lane.sh reducer_universal_composition` (the release-built kernel-composite slow lane). The cheap component/digest tests in this module stay inline and DO run in quick."]
    fn delta_interior_reflection_kernel_checks() {
        assert_eq!(
            certify_delta_interior_reflection(),
            Some(true),
            "the kernel must accept the delta-interior reflection goal"
        );
    }

    #[test]
    #[ignore = "multi-hour kernel-composite derivation (~3.5h, grows per brick): moved to the opt-in SLOW LANE so `targo test --workspace --lib` (the `quick` domination gate) stays under its 2h step budget. Run this composite via `scripts/trust_kernel_derivation_lane.sh reducer_universal_composition` (the release-built kernel-composite slow lane). The cheap component/digest tests in this module stay inline and DO run in quick."]
    fn proj_interior_reflection_kernel_checks() {
        assert_eq!(
            certify_proj_interior_reflection(),
            Some(true),
            "the kernel must accept the proj-interior reflection goal"
        );
    }

    /// The mode-fidelity partition kernel-checks over the encoded
    /// whnf_recurse CFG. SLOW (one spec build; the facts themselves are cheap
    /// — a 31-node graph).
    #[test]
    #[ignore = "multi-hour kernel-composite derivation (~3.5h, grows per brick): moved to the opt-in SLOW LANE so `targo test --workspace --lib` (the `quick` domination gate) stays under its 2h step budget. Run this composite via `scripts/trust_kernel_derivation_lane.sh reducer_universal_composition` (the release-built kernel-composite slow lane). The cheap component/digest tests in this module stay inline and DO run in quick."]
    fn recurse_mode_reflection_kernel_checks() {
        assert_eq!(
            certify_recurse_mode_reflection(),
            Some(true),
            "the kernel must accept the mode-fidelity reflection goal"
        );
    }

    /// The redex-gating exclusivity core kernel-checks over the encoded
    /// beta_or_iota_step CFG. SLOW (one spec build).
    #[test]
    #[ignore = "multi-hour kernel-composite derivation (~3.5h, grows per brick): moved to the opt-in SLOW LANE so `targo test --workspace --lib` (the `quick` domination gate) stays under its 2h step budget. Run this composite via `scripts/trust_kernel_derivation_lane.sh reducer_universal_composition` (the release-built kernel-composite slow lane). The cheap component/digest tests in this module stay inline and DO run in quick."]
    fn beta_iota_gating_reflection_kernel_checks() {
        assert_eq!(
            certify_beta_iota_gating_reflection(),
            Some(true),
            "the kernel must accept the redex-gating reflection goal"
        );
    }

    /// The step-routing exclusivity core kernel-checks over the encoded
    /// whnf_core_inner CFG (backedge cut kernel-side). SLOW (one spec build).
    #[test]
    #[ignore = "multi-hour kernel-composite derivation (~3.5h, grows per brick): moved to the opt-in SLOW LANE so `targo test --workspace --lib` (the `quick` domination gate) stays under its 2h step budget. Run this composite via `scripts/trust_kernel_derivation_lane.sh reducer_universal_composition` (the release-built kernel-composite slow lane). The cheap component/digest tests in this module stay inline and DO run in quick."]
    fn core_inner_routing_reflection_kernel_checks() {
        assert_eq!(
            certify_core_inner_routing_reflection(),
            Some(true),
            "the kernel must accept the step-routing reflection goal"
        );
    }

    #[test]
    #[ignore = "multi-hour kernel-composite derivation (~3.5h, grows per brick): moved to the opt-in SLOW LANE so `targo test --workspace --lib` (the `quick` domination gate) stays under its 2h step budget. Run this composite via `scripts/trust_kernel_derivation_lane.sh reducer_universal_composition` (the release-built kernel-composite slow lane). The cheap component/digest tests in this module stay inline and DO run in quick."]
    fn single_composite_theorem_kernel_checks() {
        assert_eq!(
            certify_single_composite_theorem(),
            Some(true),
            "the single composite theorem must be kernel-accepted"
        );
    }

    // Re-pinned 2026-07-28: the clean kernel pin advance (db9fd6fa2) changed the
    // `Name` representation (`inner`/`cached_hash` -> `depth`/`suffix`/`lean4_hash`),
    // which is encoding-visible, so every programmatic goal digest moved. The goals'
    // SEMANTICS are unchanged: they are built by the same constructors, and the
    // sibling kernel-check tests in this module accepted them at the new pin in the
    // same run these digests were harvested from.
    #[test]
    fn programmatic_reflection_goals_are_digest_pinned() {
        let dispatch = dispatch_reflection_goal().expect("dispatch goal encodes");
        let cached = cached_reducer_reflection_goal().expect("cached-reducer goal encodes");
        let fixpoint = fixpoint_exit_reflection_goal().expect("fixpoint-exit goal encodes");
        let core_routing = core_inner_routing_goal().expect("core-routing goal encodes");
        let beta_iota = beta_iota_gating_goal().expect("beta-iota goal encodes");
        let recurse = recurse_mode_goal().expect("recurse-mode goal encodes");
        let delta = delta_interior_goal().expect("delta-interior goal encodes");
        let proj = proj_interior_goal().expect("proj-interior goal encodes");
        assert_eq!(
            goal_digest(&dispatch),
            "2749161d0c8a9a93f4039de96d02ad0587e8e613c64b82a632ae37f643db6aad",
            "dispatch goal drifted"
        );
        assert_eq!(
            goal_digest(&cached),
            "9539ea58027738a7d4b4db8965099bba308d5667e74a0c912d0061b427a300ec",
            "cached-reducer goal drifted"
        );
        assert_eq!(
            goal_digest(&fixpoint),
            "dafe40e38577ae429f7894f267452ded35aad473ed36eb03688e83f246a0507e",
            "fixpoint-exit goal drifted"
        );
        assert_eq!(
            goal_digest(&core_routing),
            "f32d17fcb9ed296202d4844389c0eecb136c15e6c919ef98b44fe1fea5c6dc6e",
            "core-routing goal drifted"
        );
        assert_eq!(
            goal_digest(&beta_iota),
            "223c1e8541dec5c0047c1eedbbf8890fabd5725e9ffae1450109a72ea6d331c1",
            "beta-iota goal drifted"
        );
        assert_eq!(
            goal_digest(&recurse),
            "16049cfecc28df7efd0cc7cb3d1ac158c64f2c32e80a92c63b2c4965a6035e20",
            "recurse-mode goal drifted"
        );
        assert_eq!(
            goal_digest(&delta),
            "848a3b030419ee0cf59c1bc1edaf1b09d3cc50ccc9cdc8aba266e3120add65c4",
            "delta-interior goal drifted"
        );
        assert_eq!(
            goal_digest(&proj),
            "cc7f85b4418bffab5933e0b8d5ca32e14cc3fbe9486a9cbcda917ee36c79c78d",
            "proj-interior goal drifted"
        );
    }

    /// ENCODER FIDELITY (cheap side): the real fixture encodes; a tampered
    /// fixture (callee renamed outside the shape, or a `_0`-writing statement)
    /// fails closed or produces a DIFFERENT encoding.
    #[test]
    fn payload_encoder_grounds_and_fails_closed() {
        let goal = expected_payload_reflection_goal()
            .expect("the real fixture must encode to the reflection goal");
        assert!(goal.starts_with("Eq Bool (mir_payload_check (PayloadBody.mk2"));
        assert!(goal.ends_with("Bool.true"));

        // Tamper: rename the callee -> different encoding (still in-domain).
        let mut renamed =
            load_fixture("clean_kernel.tc.whnf.whnf_impl.closure1.json").expect("fixture loads");
        for bb in &mut renamed.body.blocks {
            if let trust_types::Terminator::Opaque { kind, .. } = &mut bb.terminator {
                *kind = kind.replace("whnf_inner", "not_whnf_inner");
            }
        }
        let tampered = encode_payload_body(&renamed).expect("still shape-valid");
        assert!(
            !goal.contains(&tampered),
            "a renamed callee must produce a DIFFERENT encoding (injective name code)"
        );

        // Tamper: inject a `_0`-writing statement -> encoder fails closed.
        let mut writes_ret =
            load_fixture("clean_kernel.tc.whnf.whnf_impl.closure1.json").expect("fixture loads");
        let steal = writes_ret.body.blocks[0].stmts[0].clone();
        if let trust_types::Statement::Assign { mut place, rvalue, span } = steal {
            place.local = 0;
            place.projections.clear();
            writes_ret.body.blocks[0].stmts.push(trust_types::Statement::Assign {
                place,
                rvalue,
                span,
            });
        }
        assert!(
            encode_payload_body(&writes_ret).is_none(),
            "a payload with a _0 writer must fail the encoder closed"
        );
    }

    /// THE FIDELITY PIN (heavy): the kernel-checked reflection goal registered in
    /// clean-verify (`mir_payload_reflection_whnf_inner`) is BYTE-IDENTICAL to the
    /// encoding of the REAL committed fixture. Fixture -> encoder -> registered
    /// goal: with this, the kernel-checked L-witness is pinned to the literal MIR,
    /// and the reflection's only residual is this (auditable, fail-closed) encoder.
    #[test]
    #[ignore = "multi-hour kernel-composite derivation (~3.5h, grows per brick): moved to the opt-in SLOW LANE so `targo test --workspace --lib` (the `quick` domination gate) stays under its 2h step budget. Run this composite via `scripts/trust_kernel_derivation_lane.sh reducer_universal_composition` (the release-built kernel-composite slow lane). The cheap component/digest tests in this module stay inline and DO run in quick."]
    fn mir_payload_reflection_pins_to_real_fixture() {
        let expected = expected_payload_reflection_goal().expect("fixture must encode");
        let registered = run_on_large_stack(|| {
            let spec = clean_verify::spec::Specification::new().expect("spec builds");
            spec.definitions().get("mir_payload_reflection_whnf_inner").map(|d| d.type_src.clone())
        })
        .flatten()
        .expect("the reflection must be registered in the spec");
        assert_eq!(
            registered, expected,
            "the kernel-checked goal must be EXACTLY the encoding of the real fixture"
        );
    }

    /// KERNEL-CHECKED DISPATCH (heavy): the kernel checks the arm-partition facts
    /// + the otherwise->stack_safe routing reachability over the encoded whnf_impl
    /// CFG — the fourth L-witness's kernel half.
    #[test]
    #[ignore = "multi-hour kernel-composite derivation (~3.5h, grows per brick): moved to the opt-in SLOW LANE so `targo test --workspace --lib` (the `quick` domination gate) stays under its 2h step budget. Run this composite via `scripts/trust_kernel_derivation_lane.sh reducer_universal_composition` (the release-built kernel-composite slow lane). The cheap component/digest tests in this module stay inline and DO run in quick."]
    fn dispatch_reflection_kernel_checks() {
        assert_eq!(
            certify_dispatch_reflection(),
            Some(true),
            "the kernel must check the dispatch arm partition + routing"
        );
    }

    /// KERNEL-CHECKED CACHED-REDUCER (heavy): the kernel computes the cache-wrapper
    /// reachability facts over the encoded real whnf_inner CFG and accepts Eq.refl —
    /// the third L-witness fact set in the kernel.
    #[test]
    #[ignore = "multi-hour kernel-composite derivation (~3.5h, grows per brick): moved to the opt-in SLOW LANE so `targo test --workspace --lib` (the `quick` domination gate) stays under its 2h step budget. Run this composite via `scripts/trust_kernel_derivation_lane.sh reducer_universal_composition` (the release-built kernel-composite slow lane). The cheap component/digest tests in this module stay inline and DO run in quick."]
    fn cached_reducer_reflection_kernel_checks() {
        assert_eq!(
            certify_cached_reducer_reflection(),
            Some(true),
            "the kernel must compute + accept the cached-reducer reachability conjunction"
        );
    }

    /// KERNEL-CHECKED FIXPOINT-EXIT (heavy): the kernel COMPUTES the loop's five
    /// reachability facts — incl. the load-bearing negative — over the encoded
    /// real 87-block CFG with the backedge cut applied kernel-side, and accepts
    /// the Eq.refl. The second L-witness reflected into the kernel's logic.
    #[test]
    #[ignore = "multi-hour kernel-composite derivation (~3.5h, grows per brick): moved to the opt-in SLOW LANE so `targo test --workspace --lib` (the `quick` domination gate) stays under its 2h step budget. Run this composite via `scripts/trust_kernel_derivation_lane.sh reducer_universal_composition` (the release-built kernel-composite slow lane). The cheap component/digest tests in this module stay inline and DO run in quick."]
    fn fixpoint_exit_reflection_kernel_checks() {
        assert_eq!(
            certify_fixpoint_exit_reflection(),
            Some(true),
            "the kernel must compute + accept the fixpoint-exit reachability conjunction"
        );
    }

    /// FULL COMPOSITION closes: every L, F, and M component holds and the
    /// composite report mints with both kernel-attested M lineages bound into
    /// the digest. (Heavy: two Specification::new() spec builds.)
    #[test]
    #[ignore = "multi-hour kernel-composite derivation (~3.5h, grows per brick): moved to the opt-in SLOW LANE so `targo test --workspace --lib` (the `quick` domination gate) stays under its 2h step budget. Run this composite via `scripts/trust_kernel_derivation_lane.sh reducer_universal_composition` (the release-built kernel-composite slow lane). The cheap component/digest tests in this module stay inline and DO run in quick."]
    fn reducer_universal_composition_closes() {
        let report = run_on_large_stack(certify_reducer_universal_composition)
            .flatten()
            .expect("the full L+M+F composition must close");
        assert!(report.l_dispatch_totality);
        assert!(report.l_payload_passthrough);
        assert!(report.l_cached_reducer);
        assert!(report.l_fixpoint_exits);
        assert!(report.f_step_gates);
        assert!(report.f_scope);
        assert!(report.l_kernel_payload_pinned, "payload reflection pinned");
        assert!(report.l_kernel_dispatch, "dispatch reflection kernel-checked");
        assert!(report.l_kernel_cached_reducer, "cached-reducer reflection kernel-checked");
        assert!(report.l_kernel_fixpoint_exit, "fixpoint-exit reflection kernel-checked");
        assert!(report.l_core_step_routing, "core step routing witness holds");
        assert!(report.l_kernel_core_routing, "core-routing reflection kernel-checked");
        assert!(report.l_step_redex_gating, "beta/iota redex gating witness holds");
        assert!(report.l_kernel_beta_iota_gating, "beta-iota reflection kernel-checked");
        assert!(report.l_recurse_mode_fidelity, "whnf_recurse mode fidelity witness holds");
        assert!(report.l_kernel_recurse_mode, "recurse-mode reflection kernel-checked");
        assert!(report.l_delta_interior, "delta interior witness holds");
        assert!(report.l_kernel_delta_interior, "delta-interior reflection kernel-checked");
        assert!(report.l_proj_interior, "proj interior witness holds");
        assert!(report.l_kernel_proj_interior, "proj-interior reflection kernel-checked");
        assert!(report.l_proj_shim, "proj shim delegates");
        assert!(!report.m_env_progress_lineage.is_empty(), "M4 δ-progress attested");
        assert!(!report.m_env_glue_lineage.is_empty(), "M5 δ-glue attested");
        assert!(!report.m_red_progress_lineage.is_empty(), "M6 3-way progress attested");
        assert!(!report.m_red_glue_lineage.is_empty(), "M7 3-way glue attested");
        assert!(!report.m_fuel_no_redex_lineage.is_empty(), "M8 fixpoint-only returns attested");
        assert!(!report.m_reduce_sound_lineage.is_empty(), "M9 executable soundness attested");
        assert!(!report.m_fuel_reaches_lineage.is_empty(), "M10 unconditional reach attested");
        assert!(
            report.l_kernel_single_theorem,
            "THE SINGLE COMPOSITE THEOREM must be kernel-accepted in one check"
        );
        assert_eq!(report.m_progress_lineage.len(), 64, "sha256 hex lineage");
        assert_eq!(report.m_normalizes_lineage.len(), 64, "sha256 hex lineage");
        assert_eq!(report.m_glue_lineage.len(), 64, "sha256 hex glue lineage");
        assert_ne!(report.composition_digest, [0u8; 32]);
    }
}
