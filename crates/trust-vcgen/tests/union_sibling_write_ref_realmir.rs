// Trust (2026-10-12, UNION-SIBLING-WRITE-2; the review of INTERVAL-WRITE-LOCKSTEP-2): a
// write to a union field THROUGH A POINTER rewrites the overlapping siblings, and every
// write oracle missed it. UNION-SIBLING-WRITE-1 gave a direct field write (`u.b = n`)
// the union cover `u`, but took it on the syntactic place:
//
//  * a store `*r = n` through `r = &mut u.b` (MIR `(*_4) = copy _2`) is NAMED `u.1` by
//    the referent fold, but `(*_4)` has no `Field` projection, so it had no cover
//    (`r_ref`, `r_nested`, `r_narrow`);
//  * a pointer into a union field put only the borrowed place `u.1` on the whole-function
//    havoc list, so neither a call handed it (`r_call`) nor an opaque store through a
//    two-referent `&mut` (`r_two`) rebound `u.0`;
//  * a callee's write set, spelled in caller names, carried `p*.1` for `(*r).b = v` and
//    dropped the root `p` that covered `p*.0` (`r_param`, with the callee bodies in the
//    summary database, as the compiler installs them).
//
// Measured on the stage 1 of `0f03df468d` (`-Ztrust-verify=on -Ztrust-policy=advisory
// -Coverflow-checks=on`, `TRUST_ELIDE_DEBUG=1`): `r_ref`, `r_nested`, `r_narrow`,
// `r_call` and `r_param`'s shapes each elided their overflow check and printed the
// wrapped value where verify-off panics; `r_two`'s `overflow:add` row was PROVED (not
// elided). The fixtures are REAL extracted MIR of `fixtures/union_sibling_write_ref/
// union_ref_liars.rs` (`-Ztrust-dump=mir-only:<dir> -Ztrust-policy=advisory --edition
// 2021 --crate-type lib`, that stage 1; spans rewritten to `<dump-root>/`); the
// extractor is not touched by the fix. Each `r_*` liar panics at the witness its source
// names (verify-off); each `c_*` control is correct on every input and keeps its proof.
use trust_types::*;
use trust_vcgen::generate_vcs;

#[path = "support/test_router.rs"]
mod test_router;

fn load(name: &str) -> VerifiableFunction {
    let path = format!(
        "{}/tests/fixtures/union_sibling_write_ref/{name}.json",
        env!("CARGO_MANIFEST_DIR")
    );
    let json = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{path}: {e}"));
    serde_json::from_str(&json).expect("fixture MIR must deserialize")
}

fn router() -> trust_router::Router {
    test_router::deterministic_test_router()
}

/// The summary database the compiler installs: every local callee's extracted body,
/// keyed by its `def_path` (the name the caller's `Terminator::Call` carries). It turns
/// on the callee write-set refinement (`callee_write_set::refine_call_havoc_delta`).
fn summaries() -> trust_vcgen::SummaryDatabase {
    let mut db = trust_vcgen::SummaryDatabase::new();
    for callee in ["set", "set_b", "set_pb"] {
        let body = load(callee);
        db.insert(
            trust_vcgen::FunctionSummary::new(body.def_path.clone())
                .with_extracted_body(std::sync::Arc::new(body)),
        );
    }
    db
}

fn is_add_overflow(kind: &VcKind) -> bool {
    matches!(kind, VcKind::ArithmeticOverflow { op: BinOp::Add, .. })
}

const LIARS: [&str; 6] = ["r_ref", "r_nested", "r_narrow", "r_call", "r_two", "r_param"];
const CONTROLS: [&str; 4] = ["c_ref", "c_call", "c_param", "c_self"];

/// Every way this test reports a liar's `+` row as true: PROVED by the in-process ay
/// router, kernel-certified, or DISCHARGED by the interval pre-pass of the compiler's
/// entry (with and without the summary database).
fn proofs_of_the_add_row(name: &str) -> Vec<String> {
    let func = load(name);
    let mut out = Vec::new();
    let rows: Vec<VerificationCondition> =
        generate_vcs(&func).into_iter().filter(|vc| is_add_overflow(&vc.kind)).collect();
    assert!(!rows.is_empty(), "{name}: fixture premise (its `+` row)");
    for (vc, r) in router().verify_all(&rows) {
        if matches!(r, VerificationResult::Proved { .. }) {
            out.push(format!("{name}: {:?} PROVED", vc.kind));
        }
        if trust_certify::certify_vc(&vc).is_some() {
            out.push(format!("{name}: {:?} kernel-certified", vc.kind));
        }
    }
    let db = summaries();
    for (entry, (to_solve, discharged)) in [
        ("discharge", trust_vcgen::generate_vcs_with_discharge(&func)),
        ("summaries", trust_vcgen::generate_vcs_with_discharge_and_summaries(&func, &db)),
    ] {
        for (vc, r) in discharged.iter().filter(|(vc, _)| is_add_overflow(&vc.kind)) {
            out.push(format!("{name}: {:?} discharged on the {entry} entry: {r:?}", vc.kind));
        }
        let solve: Vec<VerificationCondition> =
            to_solve.into_iter().filter(|vc| is_add_overflow(&vc.kind)).collect();
        for (vc, r) in router().verify_all(&solve) {
            if matches!(r, VerificationResult::Proved { .. }) {
                out.push(format!("{name}: {:?} PROVED on the {entry} entry", vc.kind));
            }
        }
    }
    out
}

/// The `+` row of every liar is neither proved nor certified nor discharged, on any
/// entry. FAILS BEFORE: every liar's row was proved on some entry (`r_param`'s only with
/// the summary database, the lane the compiler drives).
#[test]
fn a_write_through_a_pointer_into_a_union_field_liar_is_never_proved() {
    let bad: Vec<String> = LIARS.iter().flat_map(|name| proofs_of_the_add_row(name)).collect();
    assert!(
        bad.is_empty(),
        "union sibling-write-through-a-pointer liars proved:\n{}",
        bad.join("\n")
    );
}

/// The controls keep their proof: a STRUCT's fields are disjoint (a store through
/// `&mut s.b`, a call handed it, a refined callee writing `(*r).b`), and a store through
/// `&mut u.a` defines the very value read back. Anti-vacuity for the liars, and the
/// precision pin of the fix: the cover is added only where a union is crossed.
#[test]
fn the_same_writes_over_a_struct_or_to_the_read_field_still_prove() {
    let db = summaries();
    let mut lost = Vec::new();
    for name in CONTROLS {
        let func = load(name);
        let (to_solve, discharged) =
            trust_vcgen::generate_vcs_with_discharge_and_summaries(&func, &db);
        let decided = discharged.iter().filter(|(vc, _)| is_add_overflow(&vc.kind)).count();
        let solve: Vec<VerificationCondition> =
            to_solve.into_iter().filter(|vc| is_add_overflow(&vc.kind)).collect();
        assert!(decided + solve.len() > 0, "{name}: fixture premise (its `+` row)");
        for (vc, r) in router().verify_all(&solve) {
            if !matches!(r, VerificationResult::Proved { .. }) {
                lost.push(format!("{name}: {:?} -> {r:?}", vc.kind));
            }
        }
    }
    assert!(lost.is_empty(), "controls lost their proof:\n{}", lost.join("\n"));
}
