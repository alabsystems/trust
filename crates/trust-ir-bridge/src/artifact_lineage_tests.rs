//! Tests for artifact-lineage attestation (job L1 / A-LIN).
//!
//! These are the acceptance gates the execution plan states for machine 3,
//! turned into assertions:
//!
//! | gate | test |
//! |---|---|
//! | two clean builds reproduce the digest | `*_is_deterministic*`, `canonical_json_is_byte_stable` |
//! | the flip verifies the digest | `verify_flip_accepts_the_recorded_body` |
//! | a perturbed artifact fails CLOSED | `verify_flip_rejects_*` (one per component) |
//! | A1's hash and A6's flip are the same object | `coverage_*` |
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com> | Copyright 2026 | License: MIT OR Apache-2.0

use std::collections::BTreeMap;

use trust_ir::Module;

use super::{
    BodyLineage, BuildIdentity, CalleeIdentity, CalleeRemap, CrateLineage, LineageError,
    RemapCertificate, callee_ledger_digest, verify_covered_by_artifact, verify_flip_lineage,
};

/// A representative build identity. `debuginfo: "None"` because that is the
/// ONLY level at which the flip fires.
fn identity() -> BuildIdentity {
    BuildIdentity {
        compiler: "trustc 1.99.0-dev (629729f69 2026-07-13)".to_string(),
        crate_name: "clean_kernel".to_string(),
        target: "aarch64-apple-darwin".to_string(),
        opt_level: "Aggressive".to_string(),
        debuginfo: "None".to_string(),
        panic_strategy: "unwind".to_string(),
        instrument_coverage: false,
        // Deliberately UNSORTED, to prove `canonicalized` normalizes them.
        cfgs: vec!["target_arch=\"aarch64\"".to_string(), "not_kani".to_string()],
        features: vec!["std".to_string(), "binary".to_string()],
        ..BuildIdentity::default()
    }
    .canonicalized()
}

fn callees() -> Vec<CalleeIdentity> {
    vec![
        CalleeIdentity {
            func_id: 0,
            is_local: true,
            def_index: 41,
            def_krate: 0,
            def_path: "level::Level::is_zero".to_string(),
            force_havoc: false,
            ..CalleeIdentity::default()
        },
        CalleeIdentity {
            func_id: 1,
            is_local: false,
            def_index: 7,
            def_krate: 2,
            def_path: "core::option::Option::<T>::as_deref".to_string(),
            force_havoc: true,
            ..CalleeIdentity::default()
        },
    ]
}

fn body() -> BodyLineage {
    BodyLineage::compute(
        41,
        "level::Level::is_zero",
        &Module::new("level::Level::is_zero"),
        &callees(),
        &identity(),
    )
}

// ── determinism: two clean builds must reproduce every digest ───────────────

#[test]
fn body_lineage_is_deterministic_for_equal_inputs() {
    assert_eq!(
        body(),
        body(),
        "two independent computations over identical inputs must produce an identical \
         attestation — this is the `two clean builds reproduce the digest` gate"
    );
}

#[test]
fn identity_digest_is_deterministic_and_order_insensitive() {
    let mut shuffled = identity();
    shuffled.cfgs.reverse();
    shuffled.features.reverse();
    assert_eq!(
        identity().digest(),
        shuffled.canonicalized().digest(),
        "cfgs/features are SETS: a session that collected them in a different order must \
         still produce the same identity digest, or the same build would fail to reproduce"
    );
}

#[test]
fn identity_digest_discriminates_on_debuginfo() {
    // Load-bearing: the flip fires ONLY at debuginfo=None, so a lineage record
    // from a debuginfo build must never be able to match a flip event.
    let mut other = identity();
    other.debuginfo = "Full".to_string();
    assert_ne!(
        identity().digest(),
        other.digest(),
        "debuginfo MUST be part of the identity: the flip only fires at None, so a record \
         from another level must not be able to alias one that can flip"
    );
}

#[test]
fn identity_digest_discriminates_on_every_scalar_field() {
    let base = identity();
    let mutations: Vec<BuildIdentity> = vec![
        BuildIdentity {
            compiler: "trustc 1.99.0-dev (deadbeef 2026-07-14)".to_string(),
            ..base.clone()
        },
        BuildIdentity { crate_name: "clean_elab".to_string(), ..base.clone() },
        BuildIdentity { target: "x86_64-unknown-linux-gnu".to_string(), ..base.clone() },
        BuildIdentity { opt_level: "No".to_string(), ..base.clone() },
        BuildIdentity { panic_strategy: "abort".to_string(), ..base.clone() },
        BuildIdentity { instrument_coverage: true, ..base.clone() },
        BuildIdentity { cfgs: vec!["extra".to_string()], ..base.clone() },
        BuildIdentity { features: vec!["extra".to_string()], ..base.clone() },
    ];
    for mutated in mutations {
        let label = format!("{mutated:?}");
        assert_ne!(
            base.digest(),
            mutated.canonicalized().digest(),
            "every configuration field must be covered by the identity digest; \
             {label} aliased the base"
        );
    }
}

#[test]
fn callee_ledger_digest_is_order_sensitive() {
    // Emission order is digested as given. NOT because it is semantic — `func_id`
    // is DefIndex-derived and to_mir resolves it position-independently — but
    // because digesting the sequence makes a reorder OVER-key into a fail-closed
    // miss. Sorting first would make the digest blind to a reordering that did
    // matter. Contrast the remap SET below, which must be order-insensitive.
    let forward = callees();
    let mut reversed = forward.clone();
    reversed.reverse();
    assert_ne!(
        callee_ledger_digest(&forward),
        callee_ledger_digest(&reversed),
        "callee ledger order is load-bearing and must be digested"
    );
}

#[test]
fn callee_ledger_digest_is_framed_against_concatenation_aliasing() {
    // Without length framing, ("ab", "c") and ("a", "bc") produce the same
    // material. For a digest whose entire purpose is artifact identity that
    // would be a silent aliasing hole, so it is tested directly.
    let split = vec![
        CalleeIdentity { def_path: "ab".to_string(), ..CalleeIdentity::default() },
        CalleeIdentity { def_path: "c".to_string(), ..CalleeIdentity::default() },
    ];
    let other = vec![
        CalleeIdentity { def_path: "a".to_string(), ..CalleeIdentity::default() },
        CalleeIdentity { def_path: "bc".to_string(), ..CalleeIdentity::default() },
    ];
    assert_ne!(
        callee_ledger_digest(&split),
        callee_ledger_digest(&other),
        "length-prefix framing must prevent field-boundary aliasing"
    );
}

#[test]
fn callee_ledger_digest_covers_force_havoc() {
    // force_havoc CHANGES what assembly links: a forced edge becomes a bodyless
    // havoc declaration even when a clean local body exists. Two assemblies that
    // differ in it are materially different and must not share a digest.
    let mut flipped = callees();
    flipped[0].force_havoc = true;
    assert_ne!(
        callee_ledger_digest(&callees()),
        callee_ledger_digest(&flipped),
        "force_havoc must be digested — it decides body-vs-havoc linkage"
    );
}

// ── the flip-time verification ─────────────────────────────────────────────

#[test]
fn verify_flip_accepts_the_recorded_body() {
    let recorded = body();
    let verified = verify_flip_lineage(
        &recorded,
        41,
        &Module::new("level::Level::is_zero"),
        &callees(),
        &identity(),
    )
    .expect("an unperturbed body must verify");
    assert_eq!(
        verified, recorded.body_digest,
        "verification must return the SAME digest the flip event will carry"
    );
}

#[test]
fn verify_flip_rejects_a_perturbed_module() {
    let recorded = body();
    let err = verify_flip_lineage(
        &recorded,
        41,
        // A deliberately perturbed artifact: a different module presented at the
        // flip for the same def index.
        &Module::new("level::Level::is_nonzero"),
        &callees(),
        &identity(),
    )
    .expect_err("a perturbed module must FAIL CLOSED");
    assert!(
        matches!(err, LineageError::ModuleDigestMismatch { def_index: 41, .. }),
        "the error must name the module as the diverging object, got {err:?}"
    );
}

#[test]
fn verify_flip_rejects_a_perturbed_callee_ledger() {
    let recorded = body();
    let mut perturbed = callees();
    perturbed.pop();
    let err = verify_flip_lineage(
        &recorded,
        41,
        &Module::new("level::Level::is_zero"),
        &perturbed,
        &identity(),
    )
    .expect_err("a perturbed callee ledger must FAIL CLOSED");
    assert!(
        matches!(err, LineageError::CalleeDigestMismatch { def_index: 41, .. }),
        "the error must name the callee ledger, got {err:?}"
    );
}

#[test]
fn verify_flip_rejects_a_different_configuration() {
    let recorded = body();
    let mut other = identity();
    other.debuginfo = "Full".to_string();
    let err = verify_flip_lineage(
        &recorded,
        41,
        &Module::new("level::Level::is_zero"),
        &callees(),
        &other,
    )
    .expect_err("a different build configuration must FAIL CLOSED");
    assert!(
        matches!(err, LineageError::IdentityMismatch { def_index: 41, .. }),
        "the error must name the build identity, got {err:?}"
    );
}

#[test]
fn verify_flip_rejects_a_mismatched_def_index() {
    let recorded = body();
    let err = verify_flip_lineage(
        &recorded,
        99,
        &Module::new("level::Level::is_zero"),
        &callees(),
        &identity(),
    )
    .expect_err("verifying one body's record against another def index must FAIL CLOSED");
    assert_eq!(
        err,
        LineageError::DefIndexMismatch { recorded: 41, actual: 99 },
        "a def-index mismatch must be reported as itself, not as a content change"
    );
}

// ── the remapping certificate: the (1) -> (2) link ─────────────────────────

fn remap_rows() -> Vec<CalleeRemap> {
    vec![
        CalleeRemap {
            body_func_id: 1,
            assembled_func_id: 12,
            def_path: "core::option::Option::<T>::as_deref".to_string(),
            resolved_to_body: false,
        },
        CalleeRemap {
            body_func_id: 0,
            assembled_func_id: 3,
            def_path: "level::Level::is_zero".to_string(),
            resolved_to_body: true,
        },
    ]
}

#[test]
fn remap_certificate_is_insensitive_to_row_discovery_order() {
    // The remap is a SET of edges: assembly may discover them in any order, and
    // two builds that discovered the same edges must agree. `new` sorts.
    let mut reversed = remap_rows();
    reversed.reverse();
    let a = RemapCertificate::new(body(), 3, "level::Level::is_zero", remap_rows());
    let b = RemapCertificate::new(body(), 3, "level::Level::is_zero", reversed);
    assert_eq!(
        a.remap_digest, b.remap_digest,
        "the certificate must be a function of the edge SET, not of discovery order"
    );
    assert_eq!(a.callee_remap, b.callee_remap, "rows must be canonically sorted");
}

#[test]
fn remap_certificate_discriminates_on_the_assembled_mapping() {
    let base = RemapCertificate::new(body(), 3, "level::Level::is_zero", remap_rows());

    let renumbered = RemapCertificate::new(body(), 4, "level::Level::is_zero", remap_rows());
    assert_ne!(
        base.remap_digest, renumbered.remap_digest,
        "a different assembled FuncId is a different remapping"
    );

    let renamed = RemapCertificate::new(body(), 3, "level::Level::is_nonzero", remap_rows());
    assert_ne!(
        base.remap_digest, renamed.remap_digest,
        "a different assembled name is a different remapping"
    );

    let mut relinked = remap_rows();
    relinked[0].assembled_func_id = 99;
    let relinked = RemapCertificate::new(body(), 3, "level::Level::is_zero", relinked);
    assert_ne!(
        base.remap_digest, relinked.remap_digest,
        "re-pointing a callee edge is a different remapping — this is the case that made \
         A1 and A6 concern different objects"
    );

    let mut havoced = remap_rows();
    havoced[1].resolved_to_body = false;
    let havoced = RemapCertificate::new(body(), 3, "level::Level::is_zero", havoced);
    assert_ne!(
        base.remap_digest, havoced.remap_digest,
        "body-vs-havoc resolution must be part of the certificate"
    );
}

// ── the crate root: object (2), and what A1 pins ───────────────────────────

fn lineage() -> CrateLineage {
    let cert = RemapCertificate::new(body(), 3, "level::Level::is_zero", remap_rows());
    let mut certs = BTreeMap::new();
    certs.insert(41, cert);
    CrateLineage::new(identity(), certs, &Module::new("clean_kernel"))
}

#[test]
fn crate_root_digest_is_deterministic() {
    assert_eq!(
        lineage().root_digest,
        lineage().root_digest,
        "the root digest is what A1 pins — it must reproduce across builds"
    );
}

#[test]
fn crate_root_digest_covers_the_assembled_module() {
    let cert = RemapCertificate::new(body(), 3, "level::Level::is_zero", remap_rows());
    let mut certs = BTreeMap::new();
    certs.insert(41, cert);
    let other = CrateLineage::new(identity(), certs, &Module::new("clean_elab"));
    assert_ne!(
        lineage().root_digest,
        other.root_digest,
        "the root must bind the ASSEMBLED module's own digest, not only the per-body ones"
    );
}

#[test]
fn crate_root_digest_covers_body_membership() {
    let mut certs = lineage().certificates;
    certs.insert(
        7,
        RemapCertificate::new(
            BodyLineage::compute(
                7,
                "level::Level::is_nonzero",
                &Module::new("level::Level::is_nonzero"),
                &[],
                &identity(),
            ),
            4,
            "level::Level::is_nonzero",
            vec![],
        ),
    );
    let wider = CrateLineage::new(identity(), certs, &Module::new("clean_kernel"));
    assert_ne!(
        lineage().root_digest,
        wider.root_digest,
        "adding a body to the artifact must change the root digest"
    );
}

#[test]
fn canonical_json_is_byte_stable() {
    assert_eq!(
        lineage().to_canonical_json(),
        lineage().to_canonical_json(),
        "the sidecar must be byte-identical across builds: fixed key order, sorted rows, \
         no timestamps"
    );
    let rendered = lineage().to_canonical_json();
    assert!(
        rendered.contains("\"schema\": \"trust.artifact-lineage.v1\""),
        "the sidecar must be schema-tagged so a consumer cannot misread a future version"
    );
    assert!(
        rendered.contains(&lineage().root_digest.to_string()),
        "the sidecar must carry the root digest a proof cites"
    );
    assert!(
        rendered.contains(&body().body_digest.to_string()),
        "the sidecar must carry each body digest a flip event will report"
    );
}

// ── coverage: A1's hash and A6's flip are the SAME object ──────────────────

#[test]
fn coverage_accepts_a_body_in_the_pinned_artifact() {
    let verified = verify_flip_lineage(
        &body(),
        41,
        &Module::new("level::Level::is_zero"),
        &callees(),
        &identity(),
    )
    .expect("the body verifies");
    verify_covered_by_artifact(&lineage(), 41, &verified)
        .expect("a verified body present in the pinned artifact must be accepted");
}

#[test]
fn coverage_rejects_a_body_absent_from_the_pinned_artifact() {
    let verified = verify_flip_lineage(
        &body(),
        41,
        &Module::new("level::Level::is_zero"),
        &callees(),
        &identity(),
    )
    .expect("the body verifies");
    let err = verify_covered_by_artifact(&lineage(), 99, &verified)
        .expect_err("a body absent from the artifact must FAIL CLOSED");
    assert_eq!(
        err,
        LineageError::MissingCertificate { def_index: 99 },
        "an uncovered flip must be reported as a missing certificate"
    );
}

#[test]
fn coverage_rejects_a_body_whose_artifact_entry_disagrees() {
    // The precise defect A-LIN closes: the body verifies against its own
    // recording, but the artifact a proof pinned holds a DIFFERENT body at that
    // index. Before this check, that flip would have been reported as a success.
    let stale = BodyLineage::compute(
        41,
        "level::Level::is_zero",
        &Module::new("level::Level::is_zero"),
        // A different ledger => a different body digest for the same def index.
        &[],
        &identity(),
    );
    let mut certs = BTreeMap::new();
    certs.insert(41, RemapCertificate::new(stale, 3, "level::Level::is_zero", remap_rows()));
    let pinned = CrateLineage::new(identity(), certs, &Module::new("clean_kernel"));

    let verified = verify_flip_lineage(
        &body(),
        41,
        &Module::new("level::Level::is_zero"),
        &callees(),
        &identity(),
    )
    .expect("the body verifies against its own recording");
    let err = verify_covered_by_artifact(&pinned, 41, &verified)
        .expect_err("a verified body that does not match the PINNED artifact must FAIL CLOSED");
    assert!(
        matches!(err, LineageError::BodyDigestMismatch { def_index: 41, .. }),
        "the mismatch must be reported against the pinned artifact, got {err:?}"
    );
}

#[test]
fn wave489_identity_digest_thread_local_memo_and_presized_framed_match_uncached_oracle() {
    let base = identity();
    let uncached_base = base.compute_digest();
    assert_eq!(base.digest(), uncached_base);
    // Repeated hits on the same thread must match `compute_digest` bit-for-bit.
    for _ in 0..4 {
        assert_eq!(base.digest(), uncached_base);
    }

    // Mutating any field must invalidate the thread-local 1-entry cache and agree with uncached.
    let mut alt = base.clone();
    alt.features.push("extra_feature".to_string());
    alt = alt.canonicalized();
    let uncached_alt = alt.compute_digest();
    assert_ne!(uncached_alt, uncached_base);
    assert_eq!(alt.digest(), uncached_alt);
    // Switching back to `base` must also re-compute and re-cache `uncached_base`.
    assert_eq!(base.digest(), uncached_base);
}
