//! REAL-ARTIFACT regression guard for the OTHER half of the collapse repair:
//! it must not demote a real bug.
//!
//! The false-refutation fix restores a reachability condition to a block whose
//! path condition the walk COLLAPSED. Restoring it by writing one single-guard
//! PATH per in-edge back into the path map would hand it to every row of the
//! block and to every other consumer of the map;
//! `v2_formula_with_path_guards_recorded` lowers that to
//! `Or([And([g_e, body]) ..])` — the whole body CLONED once per in-edge.
//!
//! On a row that already carries its own violation condition that buys nothing
//! and costs a lot. This fixture is the compiler's OWN extracted MIR of
//!
//! ```rust,ignore
//! pub fn f(sel: u32, x: u32, y: u32) -> u32 {
//!     match sel {
//!         0 | 1 | .. | 64 => { let c = x ^ y; let d = c | 7; d * x }
//!         _ => 0,
//!     }
//! }
//! ```
//!
//! 65 switch arms share one target — one past `MAX_PATHS_PER_BLOCK`, so the
//! target SATURATES — and that target holds three arithmetic statements, the
//! last of which is a GENUINE unguarded `u32` multiply overflow. Multiplying
//! that row by the block's in-degree demoted it from REFUTED to
//! `Unknown{internal-error}`. A real violation silently turned into a decline is
//! a bug that SHIPS, and buying a false-refutation fix with one is not a trade
//! worth making.
//!
//! The repair is SCOPED by `v2_violation_is_content_free`: only a row with no
//! violation condition of its own — the one whose entire meaning IS the path
//! condition — is given the restored condition. Every row that carries content
//! keeps the size and the verdict it had before, which is what this file pins.

use trust_types::{VcKind, VerifiableFunction, VerificationCondition, VerificationResult};

fn load() -> VerifiableFunction {
    let path = format!(
        "{}/tests/data/switch_arms_shared_target_mul_overflow.json",
        env!("CARGO_MANIFEST_DIR")
    );
    let text = std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("MIR fixture {path} must be readable: {e}"));
    serde_json::from_str(&text)
        .unwrap_or_else(|e| panic!("MIR fixture {path} must deserialize: {e}"))
}

fn nodes(f: &trust_types::Formula) -> usize {
    1 + f.children().into_iter().map(nodes).sum::<usize>()
}

fn mul_row(vcs: &[VerificationCondition]) -> &VerificationCondition {
    vcs.iter()
        .find(|vc| matches!(&vc.kind, VcKind::ArithmeticOverflow { op, .. } if format!("{op:?}") == "Mul"))
        .unwrap_or_else(|| {
            panic!(
                "the fixture's whole value is its `Mul` overflow row: {:?}",
                vcs.iter().map(|vc| format!("{:?}", vc.kind)).collect::<Vec<_>>()
            )
        })
}

/// ANTI-VACUITY. The fixture only tests anything while its shared target is
/// actually SATURATED — 65 in-edges against a cap of 64. If rustc's lowering
/// drifts, or the cap moves, this file would pass for a reason unrelated to what
/// it guards.
#[test]
fn the_fixture_still_saturates_its_shared_target() {
    let func = load();
    let switch = func
        .body
        .blocks
        .iter()
        .find_map(|b| match &b.terminator {
            trust_types::Terminator::SwitchInt { targets, .. } => Some(targets),
            _ => None,
        })
        .expect("the fixture matches on `sel`");
    assert!(
        switch.len() > 64,
        "the shared target must exceed MAX_PATHS_PER_BLOCK to collapse at all; got {} arms",
        switch.len()
    );
    let shared = switch.first().map(|(_, t)| *t).expect("at least one arm");
    assert!(
        switch.iter().all(|(_, t)| *t == shared),
        "every arm must share ONE target — that is what makes the in-degree the \
         quantity under test"
    );
}

/// THE REGRESSION. A genuine, unguarded `u32` multiply overflow in the collapsed
/// block must still be REFUTED, with a counterexample.
#[test]
fn a_genuine_overflow_in_a_collapsed_block_is_still_refuted() {
    let vcs = trust_vcgen::generate_vcs(&load());
    let router = trust_router::Router::deterministic_in_process_ay(60_000);
    let results = router.verify_all(&vcs);
    let (vc, result) = results
        .iter()
        .find(|(vc, _)| {
            matches!(&vc.kind, VcKind::ArithmeticOverflow { op, .. } if format!("{op:?}") == "Mul")
        })
        .expect("the `Mul` row must still be emitted");
    let VerificationResult::Failed { counterexample, .. } = result else {
        panic!(
            "`(x ^ y | 7) * x` overflows u32 and the verifier says so; a collapse \
             repair that turns this into a decline ships the bug: {:?} -> {result:?}",
            vc.kind
        );
    };
    assert!(
        counterexample.is_some(),
        "and it must still name the values — a refutation without a witness is not \
         actionable"
    );
}

/// THE COST, pinned as a NUMBER rather than as a wall clock. The restored
/// condition must not reach a row that carries its own violation condition; if
/// it does, the row's formula grows by a factor of the block's in-degree — which
/// is what demoted the verdict the test above pins.
///
/// Both bounds are asserted: the exact size, so a change is noticed at all, and
/// the order of magnitude, so what the exact number is FOR stays legible. If a
/// fact-set change moves the exact size, re-measure it; if it moves past the
/// bound, the restore has reached a row it must not reach.
#[test]
fn the_content_carrying_row_is_not_multiplied_by_the_in_degree() {
    let vcs = trust_vcgen::generate_vcs(&load());
    let size = nodes(&mul_row(&vcs).formula);
    let in_degree = 65;
    assert!(
        size < in_degree * 10,
        "the `Mul` row must not be multiplied by the block's {in_degree} in-edges. \
         Got {size} nodes"
    );
    assert_eq!(
        size, 77,
        "the `Mul` row's size moved; re-measure and re-pin, or find out which pass \
         started conjoining onto it"
    );
}

/// SCOPE, from the other side: the repair conditions rows, it never prunes one,
/// and it must not turn a content-carrying row into the `PathConditionDegraded`
/// decline either.
#[test]
fn the_collapsed_block_declines_nothing() {
    let vcs = trust_vcgen::generate_vcs(&load());
    let kinds: Vec<String> = vcs.iter().map(|vc| format!("{:?}", vc.kind)).collect();
    assert!(
        !kinds.iter().any(|k| k.contains("PathConditionDegraded")),
        "a row with content of its own is never declined — the collapse is mere \
         imprecision for it: {kinds:?}"
    );
}
