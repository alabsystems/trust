// Trust (2026-10-11, SLICE-ZERO-SIZE-NAME-1): `panic_calls::slice_method_panic`, the
// call-site recognizer that MINTS core's slice rows over the call's own arguments
// (`n == 0` for `chunks*`/`rchunks*`/`windows`, `mid > len` for `split_at*`, `i >= len
// || j >= len` for `swap`), decided its callee by the last path segment alone. A call
// to a USER method merely named like one of them was therefore charged core's row and
// REFUTED: measured on the stage 1 of `1213387e6d` (`scratchpad/stage1-w24probe`,
// `scratchpad/scout24/szn/{ns2,ns3,sib}.rs`), each caller was refused (`[divzero]
// FAILED; counterexample: k = 0`, `[slice] FAILED`) while the callee's own row read
// `no_obligations | proved | trust-structural`, and stock rustc 1.97.1 ran the same
// calls and printed `7 7 0`.
//
// The fixtures are REAL extracted MIR (`-Ztrust-dump=mir-only:<dir>
// -Ztrust-policy=advisory --edition 2021 --crate-type lib`, the stage 1 of
// `1213387e6d`) of `fixtures/user_namesake_slice/{user_slice,renamed_slice,
// core_slice}.rs`, one caller per file, spans rewritten to `<dump-root>/`. The
// extractor is not touched by this fix, so these are the bodies the fixed compiler
// hands vcgen as well. `renamed_slice.rs` is `user_slice.rs` with every user method
// renamed off core's names (same bodies). On that stage 1, with `-Ztrust-verify=on`,
// `user_slice.rs` is refused with 21 errors under the default policy and under
// `certify`, while `renamed_slice.rs` is refused only for `r5` (a generic owner's
// method called from a generic fn: "a call it makes is discharged by no authenticated
// panic-freedom registry", a separate gap its namesake `p5` shares). Every
// user-namesake test here fails on the tail-only recognizer; the controls pin that
// core's own methods keep their rows and their verdicts.
use trust_types::*;
use trust_vcgen::generate_vcs;

#[path = "support/test_router.rs"]
mod test_router;

fn load(name: &str) -> VerifiableFunction {
    let path =
        format!("{}/tests/fixtures/user_namesake_slice/{name}.json", env!("CARGO_MANIFEST_DIR"));
    let json = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{path}: {e}"));
    serde_json::from_str(&json).expect("fixture MIR must deserialize")
}

fn router() -> trust_router::Router {
    test_router::deterministic_test_router()
}

/// Every call's rendered callee, in block order (the fixture premise).
fn callees(func: &VerifiableFunction) -> Vec<String> {
    func.body
        .blocks
        .iter()
        .filter_map(|b| match &b.terminator {
            Terminator::Call { func, .. } => Some(func.clone()),
            _ => None,
        })
        .collect()
}

/// The kinds the three tail arms mint: `DivisionByZero` (`n == 0`) and
/// `SliceBoundsCheck` (`mid > len`, `i >= len || j >= len`).
fn slice_rows(func: &VerifiableFunction) -> Vec<VerificationCondition> {
    generate_vcs(func)
        .into_iter()
        .filter(|vc| matches!(vc.kind, VcKind::DivisionByZero | VcKind::SliceBoundsCheck))
        .collect()
}

fn verdict(vc: &VerificationCondition) -> VerificationResult {
    router().verify_all(std::slice::from_ref(vc)).into_iter().next().expect("one verdict").1
}

const NAMESAKES: [(&str, &str); 8] = [
    ("p1", "user_slice::Grid::windows"),
    ("p2", "user_slice::Grid::chunks"),
    ("p3", "user_slice::Grid::rchunks_exact"),
    ("p4", "<user_slice::G2 as user_slice::Tiles>::chunks_exact"),
    ("p5", "user_slice::W::<[T]>::windows"),
    ("p6", "<[u8] as user_slice::Tr>::swap"),
    ("p7", "<[u8] as user_slice::Tr>::split_at"),
    ("p8", "<[u8] as user_slice::Tr>::windows"),
];

#[test]
fn a_call_to_a_user_method_named_like_a_core_slice_method_mints_no_row() {
    for (name, want_callee) in NAMESAKES {
        let func = load(name);
        assert_eq!(callees(&func), [want_callee], "{name}: fixture premise");
        let rows = slice_rows(&func);
        assert!(
            rows.is_empty(),
            "{name}: `{want_callee}` is a user method (total, no slice access); it owes \
             none of core's rows, got {:?}",
            rows.iter().map(|vc| (&vc.kind, vc.formula.to_smtlib())).collect::<Vec<_>>()
        );
    }
}

/// The namesake caller and its renamed twin now get the SAME obligations from vcgen:
/// no row is minted from the callee's name.
#[test]
fn a_slice_namesake_caller_gets_exactly_its_renamed_twins_obligations() {
    let shape = |func: &VerifiableFunction| -> Vec<(String, String)> {
        let mut rows: Vec<(String, String)> = generate_vcs(func)
            .iter()
            .map(|vc| (format!("{:?}", vc.kind), vc.formula.to_smtlib()))
            .collect();
        rows.sort();
        rows
    };
    for i in 1..=8 {
        let (namesake, twin) = (format!("p{i}"), format!("r{i}"));
        let (n, t) = (load(&namesake), load(&twin));
        assert_eq!(callees(&n).len(), 1, "{namesake}: fixture premise");
        assert_eq!(callees(&t).len(), 1, "{twin}: fixture premise");
        assert_eq!(
            shape(&n),
            shape(&t),
            "{namesake} (`{:?}`) must get exactly the obligations of its renamed twin {twin} \
             (`{:?}`)",
            callees(&n),
            callees(&t)
        );
    }
}

/// core's `windows` / `chunks` / `split_at` / `swap` keep exactly one row each,
/// refuted when the argument is unconstrained and proved under a dominating guard.
#[test]
fn cores_slice_methods_keep_their_row_and_their_verdict() {
    for (name, want_callee, kind, refuted) in [
        ("c1", "core::slice::<impl [u8]>::windows", VcKind::DivisionByZero, true),
        ("c2", "core::slice::<impl [u8]>::chunks", VcKind::DivisionByZero, true),
        ("c3", "core::slice::<impl [u8]>::split_at", VcKind::SliceBoundsCheck, true),
        ("c4", "core::slice::<impl [u8]>::swap", VcKind::SliceBoundsCheck, true),
        ("g1", "core::slice::<impl [u8]>::chunks", VcKind::DivisionByZero, false),
        ("g2", "core::slice::<impl [u8]>::swap", VcKind::SliceBoundsCheck, false),
    ] {
        let func = load(name);
        assert_eq!(callees(&func)[0], want_callee, "{name}: fixture premise");
        let rows = slice_rows(&func);
        assert_eq!(rows.len(), 1, "{name}: core's `{want_callee}` keeps exactly one row");
        assert_eq!(rows[0].kind, kind, "{name}");
        let v = verdict(&rows[0]);
        if refuted {
            assert!(
                matches!(v, VerificationResult::Failed { .. }),
                "{name}: an unconstrained argument reaches the panic: REFUTED; got {v:?}"
            );
        } else {
            assert!(
                matches!(v, VerificationResult::Proved { .. }),
                "{name}: the dominating guard must PROVE the row; got {v:?}"
            );
        }
    }
}

/// The fn-item deny-list keeps its answer for every spelling above: a `true` there
/// only withholds the vanilla admission of a sysroot item handed over as a value.
#[test]
fn the_fn_item_deny_list_answer_does_not_move() {
    for callee in NAMESAKES.iter().map(|(_, c)| *c).chain([
        "core::slice::<impl [u8]>::windows",
        "core::slice::<impl [u8]>::chunks",
        "core::slice::<impl [u8]>::split_at",
        "core::slice::<impl [u8]>::swap",
    ]) {
        assert!(trust_vcgen::callee_has_call_site_panic_family(callee), "`{callee}`");
    }
}
