//! REAL-ARTIFACT regression guard for SHIFT-BINDER-RESIDUE-1: the two shift-member
//! residues SELF-GUARDED-CONST-OPERAND-1 left, place and const-generic alike. In
//! each, the shift assert binder (`checked_vcs::v2_shift_assert_binds_statement`)
//! refused a canonical rustc chain, so the assert lane fell to its generic
//! `ArithmeticOverflow` row and the statement-lane `ShiftOverflow` row, sitting
//! under the assert's own `AssertHolds` guard, was never suppressed. That row is
//! UNSAT by construction and shipped as `proved` at the span of a shift that
//! panics.
//!
//! Every fixture loaded here is the compiler's OWN extracted verification input,
//! captured verbatim (the spans are already file-relative) with
//!
//! ```text
//! rustc --edition 2021 --crate-type lib -C debug-assertions=on \
//!       -Ztrust-dump=mir:<dir> shift_amount_arms.rs
//! ```
//!
//! by the stage 1 of `999b006b87` (`integ/wave23`) on 2026-10-11.
//! `shift_amount_arms.rs` is committed beside the dumps, and each
//! `shift_amount_<fn>.json` is the dump whose `"name"` is `<fn>`.
//!
//! # The two residues
//!
//! THE WIDTH. `(1i64 << n, 1i8 << n)` shifts the same widthless `Int(1)` by the
//! same amount twice. The binder read the shifted width through the by-operands
//! recovery, which takes the MINIMUM over every operand-matching shift: 8 for BOTH
//! asserts, so the first one (`Lt(n, 64)`) never bound. MEASURED on the stage 1 of
//! `999b006b87` (`scratchpad/review-w23-selfguarded/rev_c.rs`, default policy):
//! `rev_c` read `1 proved … of which 1 kernel-certified` (`summary: 0 trusted, 1
//! certified`), the proved row a `shift:left` at the first shift's span beside a
//! generic `overflow` FAILED at `N = 64`, and `rev_c::<64>()` panics there ("attempt
//! to shift left with overflow"). The place twin `rev_p(s: u32)` is the same on the
//! stages 1 of `5911b1325f` and `999b006b87`.
//!
//! THE SIGNED AMOUNT. rustc checks a signed amount through a same-width unsigned
//! cast temporary (`_2 = Cast(const N, u32); _3 = Lt(move _2, const 32_u32)`), and
//! the binder compared `_2` with the shift's `const N`. MEASURED on both stages 1:
//! `shl_ci` and `shl_s` read a generic `overflow` FAILED (`N = -1`) beside a
//! `shift:left` PROVED (`summary: 1 trusted, 0 certified, 1 failed`), and
//! `shl_ci::<{ -1 }>(1)` panics.
//!
//! # What each arm pins
//!
//! The positive arms run every safety row through the in-process ay router and
//! the clean-kernel certifier: each unguarded function panics for some argument or
//! instantiation, so every row must be REFUTED, none may certify, and each shift
//! must carry exactly ONE row (the assert lane's `ShiftOverflow`). The guarded twins
//! are safe, so none of their rows may be refuted. The forged arms change one field
//! of real input each, and each must leave the refused PAIR standing.

use trust_types::{BinOp, VcKind, VerifiableFunction, VerificationCondition, VerificationResult};

#[path = "support/test_router.rs"]
mod test_router;

const DATA: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/data/");

fn fixture_name(name: &str) -> String {
    format!("shift_amount_{name}")
}

fn load_json(name: &str) -> serde_json::Value {
    let file = fixture_name(name);
    let text = std::fs::read_to_string(format!("{DATA}{file}.json"))
        .unwrap_or_else(|e| panic!("real-MIR fixture `{file}` must be readable: {e}"));
    serde_json::from_str(&text)
        .unwrap_or_else(|e| panic!("real-MIR fixture `{file}` must parse as JSON: {e}"))
}

fn from_value(name: &str, value: serde_json::Value) -> VerifiableFunction {
    serde_json::from_value(value)
        .unwrap_or_else(|e| panic!("real-MIR fixture `{name}` must deserialize: {e}"))
}

fn load(name: &str) -> VerifiableFunction {
    from_value(name, load_json(name))
}

fn mutated(name: &str, mutate: impl FnOnce(&mut serde_json::Value)) -> VerifiableFunction {
    let mut value = load_json(name);
    mutate(&mut value);
    from_value(name, value)
}

/// Every row either lane can put at a shift's span. A shift the binder REFUSES
/// shows up as the PAIR `overflow(Shl)` + `shift(Shl)`; a bound one as `shift(Shl)`
/// alone.
fn shift_label(vc: &VerificationCondition) -> Option<String> {
    match &vc.kind {
        VcKind::ShiftOverflow { op, .. } => Some(format!("shift({op:?})")),
        VcKind::ArithmeticOverflow { op: op @ (BinOp::Shl | BinOp::Shr), .. } => {
            Some(format!("overflow({op:?})"))
        }
        _ => None,
    }
}

fn shift_rows(func: &VerifiableFunction) -> Vec<(String, VerificationCondition)> {
    trust_vcgen::generate_vcs(func)
        .into_iter()
        .filter_map(|vc| shift_label(&vc).map(|label| (label, vc)))
        .collect()
}

fn labels(func: &VerifiableFunction) -> Vec<String> {
    let mut out: Vec<String> = shift_rows(func).into_iter().map(|(label, _)| label).collect();
    out.sort();
    out
}

fn router() -> trust_router::Router {
    test_router::deterministic_test_router()
}

fn verdict(router: &trust_router::Router, vc: &VerificationCondition) -> VerificationResult {
    let results = router.verify_all(std::slice::from_ref(vc));
    let (_, result) = results.into_iter().next().expect("one verdict per VC");
    result
}

/// THE PROPERTY for an unguarded function: every shift row is REFUTED and none
/// kernel-certifies. A self-guarded statement row is UNSAT for every program, comes
/// back `Proved` and certifies, which is exactly what this rejects.
fn assert_every_row_refuted_and_none_certified(name: &str, func: &VerifiableFunction) {
    let router = router();
    let rows = shift_rows(func);
    assert!(!rows.is_empty(), "{name}: the fixture must carry its shift rows");
    for (label, vc) in &rows {
        let result = verdict(&router, vc);
        assert!(
            matches!(result, VerificationResult::Failed { .. }),
            "{name}: the `{label}` row must be REFUTED — the shift panics for some \
             argument or instantiation, and a `Proved` row here is the self-guarded \
             vacuity. Got {result:?}\nformula: {}",
            vc.formula.to_smtlib()
        );
        assert!(
            trust_certify::certify_vc(vc).is_none(),
            "{name}: the `{label}` row must not kernel-certify. formula: {}",
            vc.formula.to_smtlib()
        );
    }
}

/// THE PROPERTY for the two-shift fixtures: no shift row is `Proved` and none
/// kernel-certifies, and the WIDE shift's row (the one whose assert never bound) is
/// REFUTED. The narrow shift's row sits behind the first assert, and its formula
/// carries the first shift's `bvshl` definition; the in-process ay answers it
/// `Unknown` (incomplete), before this fix and after it, and the end-to-end run
/// reports it `runtime_checked`. `Unknown` is an honest gap; only `Proved` is the
/// lie this guards.
fn assert_no_row_proved_and_the_wide_row_refuted(name: &str, func: &VerifiableFunction) {
    let router = router();
    let rows = shift_rows(func);
    assert!(!rows.is_empty(), "{name}: the fixture must carry its shift rows");
    let mut wide_refuted = false;
    for (label, vc) in &rows {
        let result = verdict(&router, vc);
        assert!(
            !matches!(result, VerificationResult::Proved { .. }),
            "{name}: the `{label}` row must not be PROVED — the shift panics for some \
             argument or instantiation, and a `Proved` row here is the self-guarded \
             vacuity.\nformula: {}",
            vc.formula.to_smtlib()
        );
        assert!(
            trust_certify::certify_vc(vc).is_none(),
            "{name}: the `{label}` row must not kernel-certify. formula: {}",
            vc.formula.to_smtlib()
        );
        let width = vc.obligation.as_ref().and_then(|o| o.width);
        if width == Some(64) && matches!(result, VerificationResult::Failed { .. }) {
            wide_refuted = true;
        }
    }
    assert!(wide_refuted, "{name}: the i64 shift's row must be REFUTED (n = 64)");
}

/// The recorded shifted-operand width of each `ShiftOverflow` row, in source order.
fn shift_row_widths(func: &VerifiableFunction) -> Vec<Option<u32>> {
    let mut rows: Vec<(usize, usize, Option<u32>)> = shift_rows(func)
        .into_iter()
        .filter(|(_, vc)| matches!(vc.kind, VcKind::ShiftOverflow { .. }))
        .map(|(_, vc)| {
            let width = vc.obligation.as_ref().and_then(|o| o.width);
            (vc.location.line_start as usize, vc.location.col_start as usize, width)
        })
        .collect();
    rows.sort();
    rows.into_iter().map(|(_, _, width)| width).collect()
}

// ---------------------------------------------------------------------------
// THE WIDTH: two shifts of different widths share both operands.
// ---------------------------------------------------------------------------

#[test]
fn two_shifts_sharing_their_operands_each_keep_one_row() {
    // Before: the wide shift's assert never bound — `overflow(Shl)` beside the
    // statement-lane `shift(Shl)` — and only the narrow one did.
    for name in ["rev_c", "rev_p", "fwd_p"] {
        assert_eq!(
            labels(&load(name)),
            ["shift(Shl)", "shift(Shl)"],
            "{name}: each shift must carry exactly ONE row, the assert lane's, and no \
             statement-lane duplicate"
        );
    }
}

#[test]
fn a_wide_first_shift_is_refuted_and_no_row_proves() {
    // THE LIE: the i64 shift comes first, so its own assert is the only one in front
    // of it, and its statement row was proved (kernel-certified for `rev_c`) on
    // nothing but that assert.
    for name in ["rev_c", "rev_p"] {
        assert_no_row_proved_and_the_wide_row_refuted(name, &load(name));
    }
}

#[test]
fn a_narrow_first_shift_is_refuted_and_dominates_the_wide_one() {
    // `fwd_p` is `(1i8 << s, 1i64 << s)`. The i8 shift fails for `s >= 8`, and its
    // row is refuted. The i64 shift is reached only past the FIRST assert (`s < 8`),
    // so it really cannot fail: its row is a proof from the OTHER shift's check, not
    // from its own, and proves. (Before the fix it proved too, as a generic
    // `overflow(Shl)` beside the statement row.)
    let func = load("fwd_p");
    let router = router();
    let mut seen = Vec::new();
    for (label, vc) in shift_rows(&func) {
        let width = vc.obligation.as_ref().and_then(|o| o.width);
        let result = verdict(&router, &vc);
        match width {
            Some(8) => assert!(
                matches!(result, VerificationResult::Failed { .. }),
                "fwd_p: the i8 `{label}` row must be REFUTED (s = 8). Got {result:?}"
            ),
            Some(64) => assert!(
                matches!(result, VerificationResult::Proved { .. }),
                "fwd_p: the i64 `{label}` row is dominated by `s < 8` and must prove. \
                 Got {result:?}\nformula: {}",
                vc.formula.to_smtlib()
            ),
            other => panic!("fwd_p: unexpected shift row width {other:?}"),
        }
        seen.push(width);
    }
    seen.sort();
    assert_eq!(seen, [Some(8), Some(64)]);
}

#[test]
fn each_surviving_row_is_built_at_its_own_shift_width() {
    // The assert lane builds the row at the width the binder resolved at the BOUND
    // statement — the width of the row it suppresses — never the by-operands
    // minimum over both shifts.
    assert_eq!(shift_row_widths(&load("rev_c")), [Some(64), Some(8)]);
    assert_eq!(shift_row_widths(&load("rev_p")), [Some(64), Some(8)]);
    assert_eq!(shift_row_widths(&load("fwd_p")), [Some(8), Some(64)]);
}

#[test]
fn a_guard_with_the_other_shifts_width_does_not_bind() {
    // `assert(N < 8)` in front of the i64 shift is not that shift's UB check, even
    // though 8 is the by-operands minimum the binder used to compare against. The
    // first shift keeps the refused PAIR; the second still binds.
    let func = mutated("rev_c", |v| {
        let rvalue = &mut v["body"]["blocks"][0]["stmts"][0]["Assign"]["rvalue"]["BinaryOp"];
        assert_eq!(rvalue[0], "Lt", "fixture drift: bb0 must be the `Lt` guard");
        assert_eq!(rvalue[2]["Constant"]["Uint"][0], 64, "fixture drift: bb0 guards `N < 64`");
        rvalue[2]["Constant"]["Uint"][0] = serde_json::json!(8);
    });
    assert_eq!(labels(&func), ["overflow(Shl)", "shift(Shl)", "shift(Shl)"]);
}

// ---------------------------------------------------------------------------
// THE SIGNED AMOUNT: the check goes through rustc's `as uW` cast temporary.
// ---------------------------------------------------------------------------

#[test]
fn a_signed_shift_amount_keeps_one_refutable_row() {
    // Before: the PAIR — a generic `overflow` from the assert lane and the
    // vacuous `shift` row from the statement lane.
    for (name, label) in [
        ("shl_ci", "shift(Shl)"),
        ("shl_s", "shift(Shl)"),
        ("shr_ci8", "shift(Shr)"),
        ("shl_s64", "shift(Shl)"),
        // W = 128: the `BITS <= 2^(W-1)` bound must be computed without overflowing.
        ("shl_s128", "shift(Shl)"),
    ] {
        let func = load(name);
        assert_every_row_refuted_and_none_certified(name, &func);
        assert_eq!(labels(&func), [label], "{name}: exactly one row, the assert lane's");
    }
}

/// `bb0[0]`, the cast `_t = Cast(src, uW)` in front of the `Lt` guard.
fn cast_stmt(v: &mut serde_json::Value) -> &mut serde_json::Value {
    let cast = &mut v["body"]["blocks"][0]["stmts"][0]["Assign"]["rvalue"]["Cast"];
    assert!(cast.is_array(), "fixture drift: bb0[0] must be the amount's cast");
    cast
}

#[test]
fn a_cast_of_a_different_const_param_keeps_both_rows() {
    // `assert((M as u32) < 32)` does not guard `x << N`.
    let func = mutated("shl_ci", |v| {
        let param = &mut cast_stmt(v)[0]["Constant"]["ConstParam"];
        assert_eq!(param["name"], "N", "fixture drift: the cast must read `N`");
        param["index"] = serde_json::json!(1);
        param["name"] = serde_json::json!("M");
    });
    assert_eq!(labels(&func), ["overflow(Shl)", "shift(Shl)"]);
}

#[test]
fn a_truncating_cast_keeps_both_rows() {
    // `(N as u8) < 32` is not `0 <= N < 32`: `N = 256` passes it. The KIND of the
    // cast is pinned by its types (same width, signed to unsigned), so a cast to a
    // narrower target must not bind. The temporary and the `Lt`'s `BITS` constant are
    // retyped with it, so the mutant stays well typed and only the cast width moves.
    let func = mutated("shl_ci", |v| {
        let temp = cast_stmt(v)[1].clone();
        assert_eq!(temp["Int"]["width"], 32, "fixture drift: the cast targets u32");
        cast_stmt(v)[1]["Int"]["width"] = serde_json::json!(8);
        let local = v["body"]["blocks"][0]["stmts"][0]["Assign"]["place"]["local"].clone();
        let idx = local.as_u64().expect("the cast writes a whole local") as usize;
        v["body"]["locals"][idx]["ty"]["Int"]["width"] = serde_json::json!(8);
        let lt = &mut v["body"]["blocks"][0]["stmts"][1]["Assign"]["rvalue"]["BinaryOp"];
        assert_eq!(lt[0], "Lt", "fixture drift: bb0[1] must be the `Lt` guard");
        assert_eq!(lt[2]["Constant"]["Uint"], serde_json::json!([32, 32]), "fixture drift");
        lt[2]["Constant"]["Uint"][1] = serde_json::json!(8);
    });
    assert_eq!(labels(&func), ["overflow(Shl)", "shift(Shl)"]);
}

#[test]
fn an_unsigned_cast_source_keeps_both_rows() {
    // Only a SIGNED source has the `src < 0  <=>  src as uW >= 2^(W-1)` reading the
    // binding rests on. An unsigned const param on both sides (a same-width no-op
    // cast) is refused by the type pin, not by identity.
    let func = mutated("shl_ci", |v| {
        cast_stmt(v)[0]["Constant"]["ConstParam"]["signed"] = serde_json::json!(false);
        let shift = &mut v["body"]["blocks"][1]["stmts"][0]["Assign"]["rvalue"]["BinaryOp"];
        assert_eq!(shift[0], "Shl", "fixture drift: bb1[0] must be the shift");
        shift[2]["Constant"]["ConstParam"]["signed"] = serde_json::json!(false);
    });
    assert_eq!(labels(&func), ["overflow(Shl)", "shift(Shl)"]);
}

#[test]
fn a_source_rewritten_after_the_cast_keeps_both_rows() {
    // `s` is read by the cast, then overwritten before the shift reads it: the
    // assert guarded a value the shift does not shift by.
    let func = mutated("shl_s", |v| {
        let src = cast_stmt(v)[0].clone();
        let local = src["Copy"]["local"].as_u64().expect("fixture drift: the cast copies `s`");
        let stmts = v["body"]["blocks"][0]["stmts"].as_array_mut().expect("bb0 statements");
        let mut write = stmts[0].clone();
        write["Assign"]["place"] = serde_json::json!({ "local": local, "projections": [] });
        write["Assign"]["rvalue"] = serde_json::json!({ "Use": { "Constant": { "Int": 40 } } });
        stmts.insert(1, write);
    });
    assert_eq!(labels(&func), ["overflow(Shl)", "shift(Shl)"]);
}

// ---------------------------------------------------------------------------
// THE GUARDED TWINS: safe shifts must not be refuted by the bound rows.
// ---------------------------------------------------------------------------

#[test]
fn guarded_twins_have_no_refuted_shift_row() {
    let router = router();
    for name in ["rev_c_guarded", "shl_s_guarded"] {
        let func = load(name);
        let rows = shift_rows(&func);
        assert!(!rows.is_empty(), "{name}: the fixture must carry its shift rows");
        for (label, vc) in &rows {
            let result = verdict(&router, vc);
            assert!(
                !matches!(result, VerificationResult::Failed { .. }),
                "{name}: the `{label}` row must not be refuted — every shift here is \
                 guarded. Got {result:?}\nformula: {}",
                vc.formula.to_smtlib()
            );
        }
    }
}
