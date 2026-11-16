//! Andrew Yates — REAL-MIR pins for per-row grading of the argument premises
//! (gate RCA "premise", 2026-10-17).
//!
//! The compiler grades an installed argument premise (D96 `NOALIAS_MUT_ARGS`,
//! D95/D100 `REFERENCE_ARG_BOX_VALID`) per ROW: it generates the body a second time
//! with the premise parameter lists EMPTIED and keeps a row's kernel certificate only
//! when that premise-free generation produces the row's VC byte-identically
//! (`rustc_mir_transform::trust_verify::premise_free_generation`,
//! `argument_premise::PremiseFreeRows`). These tests pin, on the compiler's own
//! extraction and through the entry it calls, the two facts that grading rests on:
//!
//! * a row the premise SHAPED differs between the two generations (the negative
//!   control: its certificate is demoted), and
//! * a row the premise did not touch is byte-identical in both (its certificate is
//!   kept);
//!
//! and the two the twin adoption rests on (`argument_premise::adopt_premise_free_twins`:
//! a row the premise changed dispatches its premise-free twin when the interval lane
//! proves the twin):
//!
//! * every row the premise changed in `clip_textured_quad_x` has exactly one twin,
//!   and the interval lane proves it and the Clean kernel certifies it, and
//! * the twin of the row that NEEDS the premise (`guarded_index`'s `*n += 1`) is not
//!   proved by the interval lane (the negative control: it stays premised).
//!
//! Fixtures: `tests/fixtures/argument_premise_{mixed,clip,guarded_index}_mir.json` are
//! the compiler's own extraction of `tests/data/argument_premise_mixed.rs` (one per
//! function), captured from the repository
//! root (so every `span.file` is already repo-relative) with
//!
//! ```text
//! trustc --edition 2021 --crate-type lib -Ztrust-verify=on -Ztrust-policy=advisory \
//!        -Ztrust-dump=mir-only:<dir> crates/trust-vcgen/tests/data/argument_premise_mixed.rs
//! ```
//!
//! on the stage 1 of this change (2026-10-17, source identity 576650a63d);
//! `false_refutation_rhs_const_mir.json` is the D100 fixture
//! `false_refutation_shapes_realmir.rs` already uses.
use std::collections::HashSet;

use trust_types::{BlockId, VcKind, VerifiableFunction, VerificationCondition};

/// Real extracted MIR carries deep recursive `Formula` walks.
const STACK_BYTES: usize = 256 * 1024 * 1024;

fn load(file: &str) -> VerifiableFunction {
    let path = format!("{}/tests/fixtures/{file}", env!("CARGO_MANIFEST_DIR"));
    let text = std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("fixture `{file}` must be readable: {e}"));
    serde_json::from_str(&text).unwrap_or_else(|e| panic!("fixture `{file}` must deserialize: {e}"))
}

/// Every VC (dispatched and preclassified) of one generation of `func`, through
/// the entry the compiler calls, with the given premise parameter lists installed.
fn generate(
    func: &VerifiableFunction,
    box_deref_ops: &[(usize, usize)],
    noalias_params: &[usize],
    reference_box_params: &[usize],
) -> Vec<VerificationCondition> {
    let func = func.clone();
    let ops: HashSet<(BlockId, usize)> =
        box_deref_ops.iter().map(|&(b, s)| (BlockId(b), s)).collect();
    let noalias_params = noalias_params.to_vec();
    let reference_box_params = reference_box_params.to_vec();
    std::thread::Builder::new()
        .stack_size(STACK_BYTES)
        .spawn(move || {
            let context = trust_vcgen::VcgenContext::for_function(func.def_path.clone())
                .with_noalias_mut_params(noalias_params)
                .with_reference_box_root_params(reference_box_params);
            let db = trust_vcgen::SummaryDatabase::new();
            let (solver_vcs, preclassified) =
                trust_vcgen::generate_vcs_with_discharge_and_summaries_configured_with_context_and_box_deref_ops(
                    &func, &db, true, &context, &ops,
                );
            solver_vcs.into_iter().chain(preclassified.into_iter().map(|(vc, _)| vc)).collect()
        })
        .expect("spawn")
        .join()
        .expect("generation thread")
}

/// The exact serialization of a VC — the same complete payload the compiler's
/// row identity compares (never a digest).
fn payload(vc: &VerificationCondition) -> String {
    serde_json::to_string(vc).expect("a VC serializes")
}

fn payloads(vcs: &[VerificationCondition]) -> HashSet<String> {
    vcs.iter().map(payload).collect()
}

fn is_add_overflow_at(vc: &VerificationCondition, line: u32) -> bool {
    matches!(vc.kind, VcKind::ArithmeticOverflow { op: trust_types::BinOp::Add, .. })
        && vc.location.line_start == line
}

/// D96 `NOALIAS_MUT_ARGS` on `tests/data/argument_premise_mixed.rs::mixed`:
/// `let y = (x & 0x7f) + 1;` (line 9) reads no argument pointee, and `*n += 1`
/// (line 12) stands on the guard `*n < 8` that only the premise keeps across the
/// store `*a = 1`. The install gate fires for the two `&mut` arguments.
#[test]
fn noalias_premise_shapes_only_the_row_that_reads_the_spared_name() {
    let func = load("argument_premise_mixed_mir.json");
    assert!(
        trust_vcgen::noalias_premise_would_fire(&func, &[1, 2]),
        "the compiler installs the premise for `a` (`_1`) and `n` (`_2`)"
    );
    let premised = generate(&func, &[], &[1, 2], &[]);
    let premise_free = generate(&func, &[], &[], &[]);
    let free = payloads(&premise_free);

    let independent: Vec<_> = premised.iter().filter(|vc| is_add_overflow_at(vc, 9)).collect();
    assert!(!independent.is_empty(), "the `(x & 0x7f) + 1` row exists: {premised:#?}");
    for vc in &independent {
        assert!(
            free.contains(&payload(vc)),
            "a row the premise did not touch is byte-identical without it: {vc:#?}"
        );
    }

    let shaped: Vec<_> = premised.iter().filter(|vc| is_add_overflow_at(vc, 12)).collect();
    assert!(!shaped.is_empty(), "the `*n += 1` row exists: {premised:#?}");
    for vc in &shaped {
        assert!(
            !free.contains(&payload(vc)),
            "negative control: the row whose guard only the premise keeps differs without \
             it, so its certificate must not be kept: {vc:#?}"
        );
    }
}

/// D100 `REFERENCE_ARG_BOX_VALID` on the real `rhs_const` body (`eval(e: &Expr)`
/// reading `**rhs` of a recursive enum): the premise REMOVES the `[unsafe:sep:*]`
/// deref rows and leaves every other row byte-identical, so every kernel
/// certificate of the premised generation certifies a premise-free VC. The rows it
/// removed exist only in the premise-free generation, and the compiler discloses
/// them as the unproved `argument-premise` row.
#[test]
fn reference_box_premise_only_removes_rows() {
    const NOMINATED: [(usize, usize); 2] = [(1, 3), (6, 0)];
    let func = load("false_refutation_rhs_const_mir.json");
    let premised = generate(&func, &NOMINATED, &[], &[1]);
    let premise_free = generate(&func, &NOMINATED, &[], &[]);
    let free = payloads(&premise_free);
    for vc in &premised {
        assert!(
            free.contains(&payload(vc)),
            "the box premise changed a row it did not remove: {vc:#?}"
        );
    }
    let removed: Vec<_> =
        premise_free.iter().filter(|vc| !payloads(&premised).contains(&payload(vc))).collect();
    assert!(
        removed.iter().any(|vc| format!("{:?}", vc.kind).contains("[unsafe:sep:deref]")),
        "control: without the premise the deref rows are minted: {removed:#?}"
    );
}

/// The identity of a row apart from the facts its generation conjoined (the
/// compiler's `twin_key`): the formula blanked and the obligation record's wrappers
/// cleared, which is where those facts are recorded too. Keyed with the wrappers,
/// no row of `clip_textured_quad_x` or `guarded_index` has a twin.
fn twin_key(vc: &VerificationCondition) -> String {
    let mut key = vc.clone();
    key.formula = trust_types::Formula::Bool(true);
    if let Some(record) = key.obligation.as_mut() {
        record.wrappers.clear();
    }
    payload(&key)
}

/// Does the interval lane (the compiler's twin-adoption decision procedure) prove `vc`?
fn interval_proves(vc: &VerificationCondition) -> bool {
    let vc = vc.clone();
    std::thread::Builder::new()
        .stack_size(STACK_BYTES)
        .spawn(move || {
            let interval = trust_router::Router::with_backends(vec![Box::new(
                trust_router::interval_backend::IntervalBackend,
            )]);
            interval.verify_all(std::slice::from_ref(&vc)).first().is_some_and(|(_, result)| {
                matches!(result, trust_types::VerificationResult::Proved { .. })
            })
        })
        .expect("spawn")
        .join()
        .expect("interval thread")
}

/// For every row of `premised` that `free` does not produce byte-identically: its
/// unique twin in `free` (equal `twin_key`, itself not produced by `premised`).
fn shaped_with_twins<'a>(
    premised: &'a [VerificationCondition],
    free: &'a [VerificationCondition],
) -> Vec<(&'a VerificationCondition, &'a VerificationCondition)> {
    let free_payloads = payloads(free);
    let premised_payloads = payloads(premised);
    premised
        .iter()
        .filter(|vc| !free_payloads.contains(&payload(vc)))
        .map(|vc| {
            let twins: Vec<_> = free
                .iter()
                .filter(|f| !premised_payloads.contains(&payload(f)) && twin_key(f) == twin_key(vc))
                .collect();
            assert_eq!(twins.len(), 1, "exactly one premise-free twin for {vc:#?}: {twins:#?}");
            (vc, twins[0])
        })
        .collect()
}

/// `aterm_gpu::renderer::clip_textured_quad_x` (the 2026-10-16 gate: base 17 proved,
/// candidate 0): the premise changes exactly the six rows of `uv[2] *= kept`,
/// `rect[0] = x0` and `rect[2] = x1 - x0` (bounds and hardened twin each), whose VCs
/// keep `old_x = rect[0]`, `old_w = rect[2]` across the stores through `uv`. Each
/// has one twin, which the interval lane proves and the kernel certifies: the
/// compiler dispatches the twin and the row is certified like a premise-free row.
#[test]
fn noalias_premise_touched_rows_dispatch_interval_proved_twins() {
    let func = load("argument_premise_clip_mir.json");
    assert!(trust_vcgen::noalias_premise_would_fire(&func, &[1, 2]));
    let premised = generate(&func, &[], &[1, 2], &[]);
    let free = generate(&func, &[], &[], &[]);
    let pairs = shaped_with_twins(&premised, &free);
    let mut lines: Vec<u32> = pairs.iter().map(|(vc, _)| vc.location.line_start).collect();
    lines.sort_unstable();
    assert_eq!(lines, vec![42, 42, 43, 43, 44, 44], "the rows the premise touched: {pairs:#?}");
    for (premised_vc, twin) in pairs {
        assert!(interval_proves(twin), "the interval lane proves the twin: {twin:#?}");
        assert!(trust_certify::certify_vc(twin).is_some(), "the kernel certifies the twin");
        assert!(
            interval_proves(premised_vc),
            "control: the premised VC was proved too (its certificate was only premise-bound)"
        );
    }
}

/// Negative control: `guarded_index`'s `*n += 1` (overflow and hardened twin) needs
/// the guard only the premise keeps across `a[0] = 1`; its twin is the false
/// refutation D96 exists to stop, so the interval lane does not prove it and the row
/// keeps its premised VC (and is demoted).
#[test]
fn noalias_premise_needed_row_keeps_its_premised_vc() {
    let func = load("argument_premise_guarded_index_mir.json");
    assert!(trust_vcgen::noalias_premise_would_fire(&func, &[1, 2]));
    let premised = generate(&func, &[], &[1, 2], &[]);
    let free = generate(&func, &[], &[], &[]);
    let pairs = shaped_with_twins(&premised, &free);
    assert!(!pairs.is_empty() && pairs.iter().all(|(vc, _)| vc.location.line_start == 53));
    for (_, twin) in pairs {
        assert!(!interval_proves(twin), "the twin needs the premise: {twin:#?}");
    }
}
