// trust-integration-tests/tests/checker_core_is_whnf_emit_discharge_e2e.rs
//
// FULL-LOOP e2e for the checker-core STRUCTURAL postcondition `is_whnf(result)`:
// REAL extracted kernel-fn MIR  ->  trust-vcgen EMIT  ->  trust-certify DISCHARGE
// ->  clean kernel.
//
// This CONNECTS the two halves that were previously only exercised separately:
//   * EMIT: `trust_vcgen::generate_vcs` turns the `#[ensures] is_whnf(result)`
//     spec of a function into a `VcKind::Postcondition` VC carrying the opaque
//     `is_whnf(_0)` predicate over the return slot (as in
//     `checker_core_recursive_spec.rs`, which only paired it with the ARITHMETIC
//     `certify_violation` that FAILS CLOSED on `is_whnf`).
//   * DISCHARGE: `trust_certify::checker_core_is_whnf::certify_is_whnf_from_mir`
//     reads the SAME function's REAL MIR, extracts the returned `ExprKind` head,
//     and kernel-discharges `is_whnf(<that head>)` to a `CleanCic` via a real
//     `clean_kernel::TypeChecker::check_type`.
//
// The functions are REAL clean-kernel constructors whose fork-extracted MIR is
// committed under `crates/trust-certify/fixtures/checker_core_is_whnf_mir/`
// (`Expr::prop`/`Expr::sort` return an `ExprKind::Sort`; `Expr::app` returns
// `ExprKind::App`). So this is a for-all-over-the-function fact — the constructor
// ALWAYS returns that head — grounded on the literal MIR, with EMIT and DISCHARGE
// judging the SAME function.
//
// HONEST SCOPE: the postcondition here is the STRUCTURAL property `is_whnf(result)`
// on WHNF-returning CONSTRUCTORS (sort/pi heads). It is NOT the recursive whnf
// REDUCER's for-all (`forall e, whnf(e) in WHNF`) — that needs the fork's
// predicate-`#[ensures]` Call-arm grammar over `TypeChecker::whnf`'s MIR, an
// extraction-side item. This test closes the EMIT<->DISCHARGE connection for the
// reachable constructor fragment; it does not claim the reducer's universal.
//
// DISCRIMINATION: the non-WHNF `Expr::app` fixture EMITs the same VC but DISCHARGE
// FAILS CLOSED (App is not a WHNF head), so the discharge is genuinely gated on the
// MIR-derived head, not a rubber stamp.

use std::path::PathBuf;

use trust_certify::checker_core_is_whnf::certify_is_whnf_from_mir;
use trust_types::{Formula, VcKind, VerifiableFunction};
use trust_vcgen::generate_vcs;

/// Load a committed real-extracted-MIR fixture from the trust-certify crate and
/// attach the checker-core structural postcondition `is_whnf(result)` as its spec,
/// so the standard vcgen postcondition lane emits the `is_whnf(_0)` VC.
fn load_with_is_whnf_ensures(fixture_file: &str) -> VerifiableFunction {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../trust-certify/fixtures/checker_core_is_whnf_mir")
        .join(fixture_file);
    let json = std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("read MIR fixture {}: {e}", path.display()));
    let mut func: VerifiableFunction = serde_json::from_str(&json)
        .unwrap_or_else(|e| panic!("parse MIR fixture {}: {e}", path.display()));
    func.spec.ensures = vec!["is_whnf(result)".to_string()];
    func
}

/// Does `generate_vcs(func)` emit at least one `Postcondition` VC carrying the
/// opaque `is_whnf` predicate over the return slot `_0`?
fn emits_is_whnf_postcondition(func: &VerifiableFunction) -> bool {
    let vcs = generate_vcs(func);
    vcs.iter()
        .filter(|vc| matches!(vc.kind, VcKind::Postcondition))
        .any(|vc| {
            let mut saw = false;
            vc.formula.visit(&mut |f| {
                if let Formula::Pred(name, args) = f
                    && name.as_str() == "is_whnf"
                    && args.len() == 1
                    && args[0].var_name() == Some("_0")
                {
                    saw = true;
                }
            });
            saw
        })
}

/// FULL LOOP (WHNF constructor): the REAL MIR of `Expr::prop` (which returns an
/// `ExprKind::Sort`) both EMITs the `is_whnf(_0)` postcondition VC AND DISCHARGEs it
/// to a kernel-checked `CleanCic`. EMIT and DISCHARGE judge the SAME function, so the
/// emitted obligation `is_whnf(_0)` is exactly what the discharge closes.
#[test]
fn real_mir_prop_emits_and_discharges_is_whnf() {
    let func = load_with_is_whnf_ensures("clean_kernel.expr.Expr.prop.json");

    // EMIT (real vcgen).
    assert!(
        emits_is_whnf_postcondition(&func),
        "vcgen must EMIT an is_whnf(_0) Postcondition VC from the is_whnf(result) ensures"
    );

    // DISCHARGE (real MIR head extraction + kernel check).
    let ev = certify_is_whnf_from_mir(&func);
    assert!(
        matches!(ev, Some(trust_ir::ProofEvidence::CleanCic { .. })),
        "certify_is_whnf_from_mir must DISCHARGE Expr::prop's Sort head to a kernel-checked \
         CleanCic (the same is_whnf(_0) obligation vcgen emitted)"
    );
}

/// FULL LOOP (WHNF constructor, Pi head): the REAL MIR of `Expr::arrow` (returns an
/// `ExprKind::Pi`) both EMITs and DISCHARGEs the structural postcondition.
#[test]
fn real_mir_arrow_emits_and_discharges_is_whnf() {
    let func = load_with_is_whnf_ensures("clean_kernel.expr.Expr.arrow.json");
    assert!(
        emits_is_whnf_postcondition(&func),
        "vcgen must EMIT an is_whnf(_0) Postcondition VC for Expr::arrow"
    );
    assert!(
        matches!(
            certify_is_whnf_from_mir(&func),
            Some(trust_ir::ProofEvidence::CleanCic { .. })
        ),
        "certify_is_whnf_from_mir must DISCHARGE Expr::arrow's Pi head to a CleanCic"
    );
}

/// DISCRIMINATION (no masquerade): the non-WHNF `Expr::app` constructor (returns an
/// `ExprKind::App`) still EMITs the `is_whnf(_0)` VC from the same ensures, but the
/// DISCHARGE FAILS CLOSED — `App` is not a WHNF head, so `certify_is_whnf_from_mir`
/// returns `None`. This proves the discharge is genuinely gated on the MIR-derived
/// head (a for-all-over-the-function fact), not a rubber stamp that certifies any
/// function carrying the `is_whnf(result)` spec.
#[test]
fn real_mir_app_emits_but_discharge_fails_closed() {
    let func = load_with_is_whnf_ensures("clean_kernel.expr.Expr.app.json");

    // EMIT still happens (the VC comes from the spec, not the MIR head).
    assert!(
        emits_is_whnf_postcondition(&func),
        "vcgen still EMITs the is_whnf(_0) VC for Expr::app (from the ensures)"
    );

    // DISCHARGE must FAIL CLOSED: App is not a WHNF head.
    assert!(
        certify_is_whnf_from_mir(&func).is_none(),
        "certify_is_whnf_from_mir MUST fail closed on the non-WHNF App head (no false CleanCic)"
    );
}
