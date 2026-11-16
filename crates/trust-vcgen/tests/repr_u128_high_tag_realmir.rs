//! Real-MIR cover for REPR-U128-HIGH-TAG-1: a `#[repr(u128)]` tag above `i128::MAX`
//! made the arm for its variant vacuous, and every row in it was PROVED.
//!
//! `VariantDef::discriminant` is an `i128`. The extractor stored such a tag as the
//! lossy `val as i128` (`u128::MAX` as `-1`), and
//! `value_facts::build_discriminant_variant_range_facts` published
//! `_3 ∈ {0, -1, 5}` about the `u128` read `_3 = Discriminant(_1)`, while the
//! `SwitchInt` label for `B` renders the TRUE `u128::MAX`. The `B` arm was UNSAT.
//! Measured on `scratchpad/stage1-w22probe` (2026-10-11): `add_arm`'s `x + 1` and
//! `index_arm`'s `a[i]` read `proved` under the default policy and certify, and the
//! verify-off binaries panic there (`tests/ui/trust/repr_u128_high_tag_no_false_proof{,_run}.rs`).
//!
//! Fixtures (`-Ztrust-dump=mir-only:<dir>` on that compiler, `--edition 2021
//! --crate-type lib -Ztrust-verify=on -Ztrust-policy=advisory --cfg default`, the UI
//! fixture's `liars::add_arm` and `liars::index_arm`; absolute paths rewritten to
//! `<repo>/`):
//!
//!   repr_u128_high_tag_add_arm_mir.json    if let E::B = e { x + 1 } else { 0 }
//!   repr_u128_high_tag_index_arm_mir.json  match e { E::B => a[i], _ => 0 }
//!
//! with `#[repr(u128)] enum E { A = 0, B = u128::MAX, C = 5 }`. They carry the LOSSY
//! tag, exactly as that extractor wrote it. The extractor no longer does (it lowers
//! such an enum to `Unsupported`, the shape the last test pins); these dumps are the
//! SERIALIZED input the vcgen gate (`discriminant_tags_denote_dest_values`) exists for.
use std::collections::HashSet;

use trust_types::{BinOp, BlockId, Ty, VcKind, VerifiableFunction, VerificationResult};

#[path = "support/test_router.rs"]
mod test_router;

const SOLVER_STACK_BYTES: usize = 256 * 1024 * 1024;

fn load(name: &str) -> VerifiableFunction {
    let path = format!("{}/tests/fixtures/{name}_mir.json", env!("CARGO_MANIFEST_DIR"));
    let text = std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("fixture `{name}` must be readable: {e}"));
    serde_json::from_str(&text).unwrap_or_else(|e| panic!("fixture `{name}` must deserialize: {e}"))
}

/// Every row of `func` through the PRODUCTION generation entry the compiler calls,
/// decided by the in-process ay backend, with the hardened profile `hardened`.
fn rows(func: VerifiableFunction, hardened: bool) -> Vec<(VcKind, VerificationResult)> {
    std::thread::Builder::new()
        .stack_size(SOLVER_STACK_BYTES)
        .spawn(move || {
            let context = trust_vcgen::VcgenContext::for_function(func.def_path.clone());
            let db = trust_vcgen::SummaryDatabase::new();
            let ops: HashSet<(BlockId, usize)> = HashSet::new();
            let (solver_vcs, preclassified) =
                trust_vcgen::generate_vcs_with_discharge_and_summaries_configured_with_context_and_box_deref_ops(
                    &func, &db, hardened, &context, &ops,
                );
            let router = test_router::deterministic_test_router();
            let decided: Vec<_> = solver_vcs
                .into_iter()
                .map(|vc| {
                    let result = router.verify_one(&vc);
                    (vc.kind, result)
                })
                .collect();
            preclassified.into_iter().map(|(vc, result)| (vc.kind, result)).chain(decided).collect()
        })
        .expect("spawn")
        .join()
        .expect("generation thread")
}

fn rows_of(
    func: &VerifiableFunction,
    hardened: bool,
    kind: impl Fn(&VcKind) -> bool,
) -> Vec<VerificationResult> {
    rows(func.clone(), hardened).into_iter().filter(|(k, _)| kind(k)).map(|(_, r)| r).collect()
}

fn is_add_overflow(kind: &VcKind) -> bool {
    matches!(kind, VcKind::ArithmeticOverflow { op: BinOp::Add, .. })
}

fn is_index_bounds(kind: &VcKind) -> bool {
    matches!(kind, VcKind::IndexOutOfBounds)
}

/// The fixtures are what make this a regression test: the scrutinee's declared tags
/// carry the lossy `-1`, and the read lands in a `u128` destination.
#[test]
fn fixtures_carry_the_lossy_tag_read_into_a_u128() {
    for name in ["repr_u128_high_tag_add_arm", "repr_u128_high_tag_index_arm"] {
        let func = load(name);
        let Ty::Adt { variants, .. } = &func.body.locals[1].ty else {
            panic!("{name}: local 1 must be the lossy modeled enum: {:?}", func.body.locals[1].ty);
        };
        assert_eq!(
            variants.iter().map(|v| v.discriminant).collect::<Vec<_>>(),
            vec![0, -1, 5],
            "{name}: `u128::MAX` stored as -1"
        );
        let dest = func
            .body
            .blocks
            .iter()
            .flat_map(|b| &b.stmts)
            .find_map(|s| match s {
                trust_types::Statement::Assign {
                    place,
                    rvalue: trust_types::Rvalue::Discriminant(_),
                    ..
                } => Some(place.local),
                _ => None,
            })
            .expect("one Discriminant read");
        assert_eq!(func.body.locals[dest].ty, Ty::Int { width: 128, signed: false }, "{name}");
    }
}

/// THE REPRO. Before the fix: `Proved` (the `B` arm was UNSAT). The overflow is real
/// (`add_arm(E::B, 255)` panics), so it must be refuted.
#[test]
fn lossy_tag_does_not_prove_the_b_arm_overflow() {
    let func = load("repr_u128_high_tag_add_arm");
    for hardened in [false, true] {
        let add = rows_of(&func, hardened, is_add_overflow);
        assert_eq!(add.len(), 1, "one `x + 1` row (hardened={hardened}): {add:?}");
        assert!(
            matches!(add[0], VerificationResult::Failed { .. }),
            "the `B` arm is reachable at `u128::MAX`; a proof here stands on the false \
             membership `_3 ∈ {{0, -1, 5}}` (hardened={hardened}): {:?}",
            add[0]
        );
    }
}

/// THE REPRO, bounds shape. Before the fix: `Proved`. `index_arm(E::B, &[7], 1)` panics.
#[test]
fn lossy_tag_does_not_prove_the_b_arm_index() {
    let func = load("repr_u128_high_tag_index_arm");
    for hardened in [false, true] {
        let bounds = rows_of(&func, hardened, is_index_bounds);
        assert_eq!(bounds.len(), 1, "one `a[i]` row (hardened={hardened}): {bounds:?}");
        assert!(
            matches!(bounds[0], VerificationResult::Failed { .. }),
            "the `B` arm is reachable; `a[i]` with `i = 1` is out of bounds \
             (hardened={hardened}): {:?}",
            bounds[0]
        );
    }
}

/// THE FIXED EXTRACTION'S SHAPE. `ty_convert::lower_enum_adt` now lowers this enum to
/// the non-recursive `Unsupported` leaf. The body then (a) carries an `UnsupportedMir`
/// row for the declaration (the `recursive` relaxation must not apply), and (b) still
/// refutes the arm's row over the now-unconstrained `u128` read.
#[test]
fn unsupported_enum_shape_refutes_the_arm_and_stamps_the_declaration() {
    for (name, kind) in [
        ("repr_u128_high_tag_add_arm", is_add_overflow as fn(&VcKind) -> bool),
        ("repr_u128_high_tag_index_arm", is_index_bounds as fn(&VcKind) -> bool),
    ] {
        let mut func = load(name);
        func.body.locals[1].ty = Ty::Unsupported {
            kind: "TyKind::Adt".into(),
            detail: "enum repr_u128_high_tag_no_false_proof::liars::E: the tag of variant B has \
                     no i128 denotation (a #[repr(u128)] tag above i128::MAX); a modeled enum \
                     would carry a false discriminant (REPR-U128-HIGH-TAG-1)"
                .into(),
        };
        for hardened in [false, true] {
            let all = rows(func.clone(), hardened);
            assert!(
                all.iter().any(|(k, r)| matches!(k, VcKind::UnsupportedMir { .. })
                    && !matches!(r, VerificationResult::Proved { .. })),
                "{name}: the unsupported declaration must stamp an unproved row \
                 (hardened={hardened}): {all:?}"
            );
            let arm: Vec<_> = all.iter().filter(|(k, _)| kind(k)).map(|(_, r)| r).collect();
            assert_eq!(arm.len(), 1, "{name} (hardened={hardened}): {arm:?}");
            assert!(
                matches!(arm[0], VerificationResult::Failed { .. }),
                "{name}: the arm's row must be refuted (hardened={hardened}): {:?}",
                arm[0]
            );
        }
    }
}
