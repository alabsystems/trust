//! REAL-ARTIFACT regression guard for the shift-overflow obligation that is
//! still being CERTIFIED when the shift AMOUNT is FIELD-PROJECTED — the residual
//! `c67021cd0d` could not reach, in the same self-guarded-obligation family as
//! `divzero_canary_real_mir.rs` and `shift_canary_real_mir.rs`.
//!
//! Every fixture under `tests/data/` is the compiler's OWN extracted
//! verification input, captured verbatim with
//!
//! ```text
//! trustc --edition 2021 --crate-type lib -Ztrust-dump=mir:<dir> \
//!        crates/trust-vcgen/tests/data/projected_shift_arms.rs
//! ```
//!
//! so these are not hand-built approximations of the MIR — they are the MIR, and
//! `projected_shift_arms.rs` is committed beside them so every row re-derives.
//!
//! # What went wrong, and why counting rows hides it
//!
//! `let t = (x | 64) + 1; 1u32 << t` extracts (stage2 @ 17abbefc3) as
//!
//! ```text
//! bb0: _3 = CheckedBinaryOp(Add, _2, const 1u32); assert(!_3.1, Overflow(Add)) -> bb1
//! bb1: _4 = BinaryOp(Lt, Copy _3.0, const 32u32); assert(_4, Overflow(Shl))    -> bb2
//! bb2: _0 = BinaryOp(Shl, const 1u32, Copy _3.0)
//! ```
//!
//! The comparison input is `_3.0` — the value field of the `CheckedAdd` tuple —
//! and `v2_find_condition_binary_operands` refused any PROJECTED comparison
//! input. `c67021cd0d` deliberately made ONE predicate
//! (`v2_shift_assert_binds_statement`) serve both lanes so they "cannot drift
//! apart", so when it returns `None` BOTH lanes move at once:
//!
//!  * the ASSERT lane loses its `ShiftOverflow` row and falls through to the
//!    generic `VcKind::ArithmeticOverflow` row;
//!  * the STATEMENT lane keeps its VACUOUS row — it sits in the assert's target
//!    block, where the threaded `AssertHolds` guard makes its violation
//!    `_4 AND NOT _4`, UNSAT by construction for every program.
//!
//! So there is never a `shift:left` PAIR, and counting `shift:left` rows yields
//! ONE whether the shape is handled or broken — which looks like "no defect" but
//! IS the defect's signature. MEASURED on the arms below, advisory,
//! `-Ztrust-verify-output=json`: the canary shipped `overflow failed` +
//! `shift:left PROVED`, so the only `shift:left` row at the span of a genuinely-UB
//! shift read `proved`. The tests here therefore key on the PAIR
//! (`shift_family_rows`) and on VACUITY, never on the `shift:left` count alone.
//!
//! # Boundary
//!
//! `tuple_field_projected_shift` (`1u32 << p.0`) is a SECOND, independent root
//! cause and is not fixed by the projected-cond binder: its cond input is a
//! projection-free temporary, and the binding dies in
//! `v2_operands_structurally_equal`, which matches `(Copy, Copy)` / `(Move,
//! Move)` but not the `Copy _2` cond / `Move _2` shift spelling rustc emits
//! there. Its arm below asserts only that the surface never drops to zero, which
//! holds both today and after that spelling gap is closed.
//!
//! # Two arms were RED FROM BIRTH — measured 2026-08-25, and the direction matters
//!
//! `a_guard_over_a_different_field_does_not_suppress` and
//! `a_comparison_that_reads_its_own_flag_does_not_suppress` failed from the
//! commit that introduced them (`1baf0f3545`). Their forged bodies are
//! ILL-TYPED, so they never reached the binder they claim to test.
//!
//! THIS IS NOT A FAIL-OPEN, and that was established before anything was
//! touched. Both forgeries return exactly ONE row —
//! `UnsupportedMir { kind: "MalformedTrustIr", detail: "BinaryOp(Lt) does not
//! match the audited Rust binary operation operand/destination types" }` — and
//! nothing else. `validate_binary_assignment_types` requires a comparison's two
//! inputs to authenticate at ONE established type, and both forgeries spell
//! `Lt(<bool place>, const 32u32)`: `_3.1` is the `CheckedAdd` overflow flag and
//! `_4` is the shift assert's own flag, and neither is a `u32`. The whole
//! function is therefore refused, which is STRICTLY STRONGER than "both lanes
//! report": the router gives an `UnsupportedMir` row no backend plan at all and
//! grades it `Unknown` (`trust-router/src/router.rs`, `backend_trait.rs`), so no
//! obligation was suppressed — none was claimed.
//!
//! The evidence that nothing regressed, rather than the docs being trusted:
//!
//!  * the gate that refuses them landed in `4ca0cb0eac` (2026-08-21), and
//!    `validate_binary_assignment_types` + `exact_binary_input_type` are
//!    BYTE-IDENTICAL between `1baf0f3545` (2026-08-24, which added these arms)
//!    and HEAD — so the arms were red the moment they were written; and
//!  * deleting the self-read test from `v2_condition_binary_operands` outright
//!    leaves `self_reading_cond` UNCHANGED (still one `MalformedTrustIr` row).
//!    An arm that does not move when the rule it names is deleted was pinning
//!    nothing.
//!
//! WHAT REPLACED THEM.
//!
//!  * The projection-exactness arm is re-forged on `tuple_field_projected_shift`
//!    (`p: (u32, u32)`) — the one real extracted fixture in this directory whose
//!    tuple has TWO integer fields, so a cond over `p.1` guarding a shift by
//!    `p.0` is WELL-TYPED and reaches the binder. It ships with its own POSITIVE
//!    CONTROL (`an_aligned_field_guard_is_the_binding_positive_control`), which
//!    is what proves the crossed arm isolates the FIELD dimension and not some
//!    other refusal. MEASURED differential: crossed = 2 rows, aligned = 1 row;
//!    under a base-local-only identity (`pa.local == pb.local` in place of
//!    `pa == pb`) the crossed arm drops to 1 while the control stays at 1 — i.e.
//!    a guard over `p.1` suppresses the obligation about `p.0`, exactly the
//!    hazard, and the arm goes RED for it.
//!  * The self-read arm now pins the state that is actually reachable. The shape
//!    it wants is UNREACHABLE on well-typed IR and provably so: the `Lt`'s
//!    destination must be `bool`, so the flag local is `bool`, so no operand of
//!    that comparison can both overlap the flag's name and authenticate as the
//!    integer the shift amount is compared against. Nor can a name collision
//!    manufacture the overlap — `place_to_var_name` already demotes a source name
//!    shaped like another local's `_<k>` fallback token (measured: renaming `_3`
//!    to `_4` binds identically with the self-read test present and absent). The
//!    arm therefore pins the FAIL-CLOSED DISJUNCTION via
//!    `assert_no_laundered_shift_obligation`, and it RE-ARMS ITSELF: if the
//!    comparison type audit is ever widened to admit a bool-versus-integer `Lt`,
//!    the marker disappears and the arm reverts to demanding both lanes report,
//!    with no edit here.

use std::collections::HashMap;

use trust_types::{BinOp, Formula, VcKind, VerifiableFunction};

const DATA: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/data/");

fn load_json(name: &str) -> serde_json::Value {
    let text = std::fs::read_to_string(format!("{DATA}{name}.json"))
        .unwrap_or_else(|e| panic!("canary MIR fixture `{name}` must be readable: {e}"));
    serde_json::from_str(&text)
        .unwrap_or_else(|e| panic!("canary MIR fixture `{name}` must parse as JSON: {e}"))
}

fn load(name: &str) -> VerifiableFunction {
    // STRAIGHT FROM TEXT, never through `serde_json::Value`: its number type is
    // `PosInt(u64) | NegInt(i64) | Float(f64)`, so a 128-bit constant is
    // silently widened to `f64` on the hop and the derive then rejects it
    // ("invalid type: floating point ..., expected i128"). This bit
    // `negation_canary_real_mir`'s `negation_i128` arm for real; these fixtures
    // carry no 128-bit constant today, and now cannot start failing that way.
    let text = std::fs::read_to_string(format!("{DATA}{name}.json"))
        .unwrap_or_else(|e| panic!("canary MIR fixture `{name}` must be readable: {e}"));
    serde_json::from_str(&text)
        .unwrap_or_else(|e| panic!("canary MIR fixture `{name}` must deserialize: {e}"))
}

fn from_value(name: &str, value: serde_json::Value) -> VerifiableFunction {
    serde_json::from_value(value)
        .unwrap_or_else(|e| panic!("canary MIR fixture `{name}` must deserialize: {e}"))
}

/// The production path: the real generator, over the real extracted body.
fn shift_vcs(func: &VerifiableFunction) -> Vec<trust_types::VerificationCondition> {
    trust_vcgen::generate_vcs(func)
        .into_iter()
        .filter(|vc| matches!(vc.kind, VcKind::ShiftOverflow { .. }))
        .collect()
}

/// Every row either lane can put at a shift's span: the real `ShiftOverflow`
/// obligation AND the generic `ArithmeticOverflow` row the assert lane falls
/// through to when the binding is refused.
///
/// COUNTING `ShiftOverflow` ALONE CANNOT SEE THIS DEFECT. One predicate serves
/// both lanes, so when it refuses BOTH move: the assert lane downgrades to
/// `ArithmeticOverflow` and the statement lane keeps its vacuous row — one
/// `shift:left` row either way. This pair is what separates the states:
/// `(ShiftOverflow, ArithmeticOverflow{Shl})` = refused, a lone `ShiftOverflow`
/// = bound.
fn shift_family_rows(func: &VerifiableFunction) -> Vec<String> {
    trust_vcgen::generate_vcs(func)
        .into_iter()
        .filter_map(|vc| match &vc.kind {
            VcKind::ShiftOverflow { op, .. } => Some(format!("ShiftOverflow({op:?})")),
            VcKind::ArithmeticOverflow { op: op @ (BinOp::Shl | BinOp::Shr), .. } => {
                Some(format!("ArithmeticOverflow({op:?})"))
            }
            _ => None,
        })
        .collect()
}

/// Both lanes reported: the statement row survived AND the assert lane fell
/// through to its generic row (or, for the sole-entry arm, emitted its own
/// `ShiftOverflow`). Anything less means the suppression fired.
fn assert_both_lanes_report(tag: &str, func: &VerifiableFunction) {
    let rows = shift_family_rows(func);
    assert_eq!(
        rows.len(),
        2,
        "{tag}: a non-canonical shape must leave BOTH lanes reporting — duplicates \
         over-report, they never under-report. Got {rows:?}"
    );
}

/// Every visible whole-function admission refusal. `generate_vcs` collapses a
/// body that `crate::validate_function` rejects to exactly ONE of these and
/// drops the rest, so its presence is what distinguishes "refused" from
/// "silently produced nothing".
fn malformed_markers(func: &VerifiableFunction) -> Vec<String> {
    trust_vcgen::generate_vcs(func)
        .into_iter()
        .filter_map(|vc| match &vc.kind {
            VcKind::UnsupportedMir { kind, detail } if kind == "MalformedTrustIr" => {
                Some(detail.clone())
            }
            _ => None,
        })
        .collect()
}

/// THE FAIL-CLOSED DISJUNCTION. A forged shape may legitimately end in either of
/// two states, and this pins the boundary between them and the fail-OPEN one:
///
///  * BOTH LANES REPORT (two shift-family rows) — the body was admitted and the
///    binder refused to bind it. This is what every other arm in this section
///    aims at; or
///  * WHOLE-FUNCTION REFUSAL — the body never reached the binder because
///    `validate_binary_assignment_types` rejected it, and the function collapses
///    to one visible `UnsupportedMir { kind: "MalformedTrustIr" }` row. The
///    router returns an EMPTY backend plan for that row and grades it `Unknown`,
///    so no obligation is claimed about this function at all.
///
/// REJECTED, and these are the two ways this could go wrong: ONE shift-family
/// row means the suppression fired and took a real obligation with it; ZERO rows
/// with NO marker means the obligation vanished with nothing said about it.
///
/// Use this only where the strict form is UNREACHABLE. An arm that can be
/// well-typed belongs on `assert_both_lanes_report`, which is strictly stronger.
fn assert_no_laundered_shift_obligation(tag: &str, func: &VerifiableFunction) {
    let rows = shift_family_rows(func);
    let markers = malformed_markers(func);
    assert!(
        rows.len() == 2 || (rows.is_empty() && markers.len() == 1),
        "{tag}: a non-canonical shape must either leave BOTH lanes reporting or be \
         refused WHOLE-FUNCTION with one visible MalformedTrustIr marker. One \
         surviving row means the suppression fired; zero rows with no marker means \
         the obligation was lost silently. Got rows={rows:?} markers={markers:?}"
    );
}

/// Walk the VC's conjunctive skeleton, recording
///   * `defs` — flag definitions `flag = <condition>` (the MIR bool temps);
///   * `pos` / `neg` — flags asserted positively / negatively;
///   * `atoms` — every non-definition atom asserted positively.
fn collect(
    f: &Formula,
    defs: &mut HashMap<String, Formula>,
    pos: &mut Vec<String>,
    neg: &mut Vec<String>,
    atoms: &mut Vec<Formula>,
) {
    match f {
        Formula::And(parts) => {
            for p in parts {
                collect(p, defs, pos, neg, atoms);
            }
        }
        Formula::Not(inner) => match inner.as_ref() {
            Formula::Var(name, _) => neg.push(name.clone()),
            other => atoms.push(Formula::Not(Box::new(other.clone()))),
        },
        Formula::Var(name, _) => pos.push(name.clone()),
        Formula::Eq(a, b) => {
            // `flag = <condition>` is a DEFINITION, not an assertion of `flag`.
            if let Formula::Var(name, _) = a.as_ref() {
                defs.insert(name.clone(), b.as_ref().clone());
            } else if let Formula::Var(name, _) = b.as_ref() {
                defs.insert(name.clone(), a.as_ref().clone());
            } else {
                atoms.push(f.clone());
            }
        }
        other => atoms.push(other.clone()),
    }
}

fn same(a: &Formula, b: &Formula) -> bool {
    a.to_smtlib() == b.to_smtlib()
}

/// Whether `a` is the exact logical complement of `b` over identical operands.
fn complementary(a: &Formula, b: &Formula) -> bool {
    match (a, b) {
        (Formula::Lt(x, y), Formula::Ge(p, q))
        | (Formula::Ge(x, y), Formula::Lt(p, q))
        | (Formula::Le(x, y), Formula::Gt(p, q))
        | (Formula::Gt(x, y), Formula::Le(p, q)) => same(x, p) && same(y, q),
        (Formula::Not(inner), other) | (other, Formula::Not(inner)) => same(inner, other),
        _ => false,
    }
}

/// The flags this VC asserts while ALSO asserting the negation of their own
/// defining condition — `flag AND NOT flag`. Such a VC is UNSAT by construction:
/// it can only ever come back `proved`, and it proves nothing. That is precisely
/// the shape shipping as a `proved` `shift:left` row at the span of a
/// genuinely-false projected-amount shift overflow.
///
/// One level of definition is resolved on purpose: a second, unrelated shift
/// legitimately carries the FIRST shift's passed-assert flag as a path guard
/// while its own violation is about a different amount
/// (`two_distinct_projected_shift_amounts` is exactly that), and a crude
/// literal/complement scan would flag that honest obligation as vacuous.
fn vacuous_flags(vc: &trust_types::VerificationCondition) -> Vec<String> {
    let mut defs = HashMap::new();
    let (mut pos, mut neg, mut atoms) = (Vec::new(), Vec::new(), Vec::new());
    collect(&vc.formula, &mut defs, &mut pos, &mut neg, &mut atoms);
    let mut bad: Vec<String> = Vec::new();
    // Shift polarity: `flag` true, `NOT def(flag)` also asserted.
    for flag in &pos {
        if let Some(def) = defs.get(flag)
            && atoms.iter().any(|a| complementary(a, def))
        {
            bad.push(flag.clone());
        }
    }
    // Div/rem polarity, kept so this detector covers the whole family: `flag`
    // false, `def(flag)` asserted true.
    for flag in &neg {
        if let Some(def) = defs.get(flag)
            && atoms.iter().any(|a| same(a, def))
        {
            bad.push(flag.clone());
        }
    }
    bad.sort();
    bad.dedup();
    bad
}

fn assert_no_vacuous_obligation(name: &str, func: &VerifiableFunction) {
    for vc in shift_vcs(func) {
        let bad = vacuous_flags(&vc);
        assert!(
            bad.is_empty(),
            "{name}: a surviving shift obligation asserts {bad:?} while also asserting \
             the negation of its defining condition — UNSAT by construction, so it can \
             only ever be `proved`: {}",
            vc.formula.to_smtlib()
        );
    }
}

// ---------------------------------------------------------------------------
// The canaries. `shift_family_rows` is the differential: BEFORE the projected
// binding each of these carried `[ArithmeticOverflow(Shl), ShiftOverflow(Shl)]`
// — a `failed` generic row plus a `PROVED` vacuous one — and AFTER it carries
// the single real `ShiftOverflow` row the assert lane now emits.
// ---------------------------------------------------------------------------

#[test]
fn projected_shift_canary_keeps_exactly_one_non_vacuous_obligation() {
    // `let t = (x | 64) + 1; 1u32 << t` is genuinely UB (`t >= 65`). Before the
    // projected-cond binding this fixture's ONLY `shift:left` row was the
    // statement one, sitting under its own passed-assert guard — `proved` at the
    // span of a genuinely-false shift overflow.
    let name = "sentinel_projected_shift_overflow_must_not_prove";
    let func = load(name);
    assert_eq!(
        shift_family_rows(&func),
        vec!["ShiftOverflow(Shl)"],
        "the assert lane must emit the REAL shift obligation (not downgrade to the \
         generic overflow row) and the vacuous statement duplicate must be gone"
    );
    assert_no_vacuous_obligation(name, &func);
}

#[test]
fn projected_shr_canary_keeps_exactly_one_non_vacuous_obligation() {
    // The suppression and the binding are both per-opcode.
    let name = "sentinel_projected_shr_overflow_must_not_prove";
    let func = load(name);
    assert_eq!(shift_family_rows(&func), vec!["ShiftOverflow(Shr)"]);
    assert_no_vacuous_obligation(name, &func);
}

#[test]
fn unguarded_projected_shift_keeps_a_refutable_obligation() {
    // `let t = s + 1; x << t`: neither provable nor refutable by construction.
    // The obligation must survive, and it must be the REFUTABLE one — the row it
    // replaced could never fail.
    let name = "unguarded_projected_shift";
    let func = load(name);
    assert_eq!(shift_family_rows(&func), vec!["ShiftOverflow(Shl)"]);
    assert_no_vacuous_obligation(name, &func);
}

// ---------------------------------------------------------------------------
// THE SURFACE MUST NOT SHRINK. A suppression that deletes an honest row is a
// lost recovery, not a fix.
// ---------------------------------------------------------------------------

#[test]
fn provably_safe_projected_shift_keeps_a_dischargeable_obligation() {
    // `let t = (s & 15) + 1; 1u32 << t` is genuinely SAFE (`t <= 16`). Exactly
    // one REAL obligation must remain for the discharge lanes to prove: the
    // amount's own `s & 15` range fact is what contradicts `t >= 32`, not a
    // self-guard. MEASURED before this change: this arm already shipped a
    // `proved` verdict — but on a VACUOUS row, so it proved nothing.
    let name = "provably_safe_projected_shift";
    let func = load(name);
    assert_eq!(
        shift_family_rows(&func),
        vec!["ShiftOverflow(Shl)"],
        "the safe case keeps one real obligation to discharge; deleting it would be \
         a lost recovery, not a fix"
    );
    assert_no_vacuous_obligation(name, &func);
}

#[test]
fn two_distinct_projected_amounts_each_keep_their_own_obligation() {
    // `(x << (s + 1)) ^ (x << (t + 1))`: two projected amounts, two asserts, two
    // real obligations. A binding keyed on the BLOCK rather than on the AMOUNT
    // drops one of them.
    let name = "two_distinct_projected_shift_amounts";
    let func = load(name);
    assert_eq!(
        shift_family_rows(&func),
        vec!["ShiftOverflow(Shl)", "ShiftOverflow(Shl)"],
        "each distinct shift amount keeps exactly one real obligation"
    );
    assert_no_vacuous_obligation(name, &func);
}

#[test]
fn tuple_field_amount_keeps_its_obligation() {
    // `1u32 << p.0`: the SECOND root cause (see the module docs) — rustc emits
    // `_2 = Use(Copy _1.0); _3 = Lt(Copy _2, 32)` and then `Shl(1, Move _2)`, so
    // the cond input is projection-free and the binding dies on the Copy/Move
    // spelling instead. NOT fixed here; this arm deliberately pins only that the
    // surface never drops to zero for the shape, which holds both today and once
    // that spelling gap closes.
    let func = load("tuple_field_projected_shift");
    assert!(
        !shift_vcs(&func).is_empty(),
        "a field-projected shift amount must never lose its obligation entirely"
    );
}

// ---------------------------------------------------------------------------
// FAIL-CLOSED STRUCTURAL MUTATIONS. Each changes ONE field of the REAL canary
// artifact, taking the shape out of the canonical rustc chain, and the binding
// must switch off — leaving BOTH lanes reporting
// (`[ArithmeticOverflow(Shl), ShiftOverflow(Shl)]`). Under the loosening named
// on each arm the binder instead ACCEPTS, the statement row is deleted and the
// assert lane's row takes its place: one row, and the arm goes red.
// ---------------------------------------------------------------------------

/// The real canary MIR with one field replaced, then run through the generator.
fn canary_mutated(tag: &str, mutate: impl FnOnce(&mut serde_json::Value)) -> VerifiableFunction {
    let mut value = load_json("sentinel_projected_shift_overflow_must_not_prove");
    mutate(&mut value);
    from_value(tag, value)
}

/// bb1's `_4 = Lt(Copy _3.0, const 32u32)` — the cond definition most mutations
/// below reach through. Asserted, not assumed, so a fixture drift fails loudly.
fn cond_operands(v: &mut serde_json::Value) -> &mut serde_json::Value {
    let rvalue = &mut v["body"]["blocks"][1]["stmts"][0]["Assign"]["rvalue"]["BinaryOp"];
    assert_eq!(rvalue[0], "Lt", "fixture drift: bb1[0] must be the `Lt` cond definition");
    rvalue
}

/// bb2's `_0 = BinaryOp(Shl, const 1u32, Copy _3.0)` — the shift's AMOUNT operand.
fn shift_amount(v: &mut serde_json::Value) -> &mut serde_json::Value {
    let rvalue = &mut v["body"]["blocks"][2]["stmts"][0]["Assign"]["rvalue"]["BinaryOp"];
    assert_eq!(rvalue[0], "Shl", "fixture drift: bb2[0] must be the shift");
    &mut rvalue[2]
}

// ---------------------------------------------------------------------------
// The SECOND forgery base. `tuple_field_projected_shift` is the only real
// extracted fixture here whose tuple carries TWO integer fields
// (`p: (u32, u32)`), which is what makes a same-base/different-field guard
// WELL-TYPED — the `CheckedAdd` carrier `_3: (u32, bool)` cannot express one,
// because its only other field is the overflow flag and
// `Lt(<bool>, const 32u32)` fails the whole-function comparison type audit.
//
//   bb0: _2 = Use(Copy _1.0); _3 = Lt(Copy _2, const 32u32);
//        assert(move _3, Overflow(Shl)) -> bb1
//   bb1: _0 = BinaryOp(Shl, const 1u32, Move _2)
// ---------------------------------------------------------------------------

/// The real `tuple_field_projected_shift` MIR with a mutation applied.
fn tuple_mutated(tag: &str, mutate: impl FnOnce(&mut serde_json::Value)) -> VerifiableFunction {
    let mut value = load_json("tuple_field_projected_shift");
    mutate(&mut value);
    from_value(tag, value)
}

/// bb0's `_3 = Lt(Copy _2, const 32u32)` — the cond definition.
fn tuple_cond_operands(v: &mut serde_json::Value) -> &mut serde_json::Value {
    let rvalue = &mut v["body"]["blocks"][0]["stmts"][1]["Assign"]["rvalue"]["BinaryOp"];
    assert_eq!(rvalue[0], "Lt", "fixture drift: bb0[1] must be the `Lt` cond definition");
    rvalue
}

/// bb1's `_0 = BinaryOp(Shl, const 1u32, Move _2)` — the shift's AMOUNT operand.
fn tuple_shift_amount(v: &mut serde_json::Value) -> &mut serde_json::Value {
    let rvalue = &mut v["body"]["blocks"][1]["stmts"][0]["Assign"]["rvalue"]["BinaryOp"];
    assert_eq!(rvalue[0], "Shl", "fixture drift: bb1[0] must be the shift");
    &mut rvalue[2]
}

/// `Copy _<local>.<field>`. Both sides of the two tuple arms are spelled `Copy`
/// ON PURPOSE: the fixture as shipped reads `Copy _2` in the cond and `Move _2`
/// in the shift, and `v2_operands_structurally_equal` refuses that spelling
/// (the second root cause in the Boundary note above). Matching the spellings
/// takes that refusal off the table so the FIELD is the only thing left that can
/// decide either arm — which is precisely what the positive control measures.
fn tuple_field(local: u64, field: u64) -> serde_json::Value {
    serde_json::json!({ "Copy": { "local": local, "projections": [{ "Field": field }] } })
}

#[test]
fn a_downcast_projected_amount_does_not_suppress() {
    // FIELD projections only. Both the cond input and the shift's amount become
    // `_3<downcast 0>.0`, so operand identity, base stability, the width recovery
    // and sole entry all still pass — the projection KIND is the only thing left
    // to refuse it. A `Downcast` selects a variant that a tuple does not have;
    // admitting one would mean the binding cannot tell variants apart.
    // RED under: admitting any projection instead of `Projection::Field`.
    //
    // (`Deref` is the shape that rule really exists for — a read through a
    // pointer whose stores a def scan cannot see — but a `Deref` that type-checks
    // needs a reference-typed base, which rustc never emits for a shift amount,
    // so it cannot be planted on this artifact. `Downcast` is the stand-in.)
    //
    // IF THE SHIFT RULE IS EVER WIDENED to `checked_vcs`'s statically-addressed
    // allowlist — which admits `Downcast` — this arm must be re-pointed at a
    // projection the widened rule still refuses, NOT deleted.
    let func = canary_mutated("downcast_amount", |v| {
        let downcast = serde_json::json!({
            "Copy": { "local": 3, "projections": [{ "Downcast": 0 }, { "Field": 0 }] }
        });
        cond_operands(v)[1] = downcast.clone();
        *shift_amount(v) = downcast;
    });
    assert_both_lanes_report("downcast_amount", &func);
}

#[test]
fn a_second_store_to_the_amounts_base_local_does_not_suppress() {
    // The `CheckedAdd` that defines `_3` is duplicated AFTER the shift, so `_3`
    // has two definitions function-wide and `value_local_is_unstable` calls the
    // whole aggregate — and therefore `_3.0` — unstable. RED under: dropping the
    // base-local stability call. Nothing else catches it: the assert block's
    // later-write scan and the shift block's before-the-shift scan both look at
    // windows this write is outside of.
    let func = canary_mutated("unstable_base", |v| {
        let def = v["body"]["blocks"][0]["stmts"][1].clone();
        v["body"]["blocks"][2]["stmts"].as_array_mut().expect("bb2 stmts").push(def);
    });
    assert_both_lanes_report("unstable_base", &func);
}

#[test]
fn an_amount_rewritten_before_the_shift_does_not_suppress() {
    // The same `CheckedAdd` is inserted into the SHIFT's block, before the shift:
    // the assert then guarded a different value than the shift reads. RED under:
    // dropping the before-the-shift rewrite scan — though base-local stability
    // covers this particular body too, so it stays red unless BOTH are dropped.
    // The scan is kept as its own rule because it is what holds when the
    // intervening write is not to the amount's own base.
    let func = canary_mutated("rewritten_amount", |v| {
        let def = v["body"]["blocks"][0]["stmts"][1].clone();
        v["body"]["blocks"][2]["stmts"].as_array_mut().expect("bb2 stmts").insert(0, def);
    });
    assert_both_lanes_report("rewritten_amount", &func);
}

#[test]
fn a_guard_over_a_different_value_does_not_suppress() {
    // The cond is re-pointed to `_2`, the PRE-increment value, while the shift
    // still shifts by `_3.0`. Bare target identity is never suppression
    // authority. RED under: making the binding block-keyed. The width check and
    // the sole-entry check both still pass, so only operand identity refuses.
    let func = canary_mutated("crossed_cond", |v| {
        cond_operands(v)[1] = serde_json::json!({ "Copy": { "local": 2, "projections": [] } });
    });
    assert_both_lanes_report("crossed_cond", &func);
}

#[test]
fn an_aligned_field_guard_is_the_binding_positive_control() {
    // THE POSITIVE CONTROL for the arm below, and the reason that arm means
    // anything. Same forgery, same Copy/Copy spelling, cond and shift over the
    // SAME field: the binder must ACCEPT, leaving the single real obligation.
    //
    // Without this, `a_guard_over_a_different_field_does_not_suppress` proves
    // only "something refused" — and its predecessor died of exactly that, being
    // refused by the whole-function type audit while claiming to measure the
    // binder. This arm pins that every OTHER dimension (stability, width, sole
    // entry, polarity, opcode, projection kind, operand spelling) passes on this
    // body, so the field is the only variable between the two.
    let func = tuple_mutated("aligned_field", |v| {
        tuple_cond_operands(v)[1] = tuple_field(1, 0);
        *tuple_shift_amount(v) = tuple_field(1, 0);
    });
    assert_eq!(
        shift_family_rows(&func),
        vec!["ShiftOverflow(Shl)"],
        "a guard over the field the shift actually reads MUST bind; if this arm goes \
         red the crossed-field arm below is measuring some other refusal"
    );
    assert_no_vacuous_obligation("aligned_field", &func);
}

#[test]
fn a_guard_over_a_different_field_does_not_suppress() {
    // THE PROJECTION-EXACTNESS ARM, and the one that only exists because the rule
    // admits projections at all: the cond guards `p.1` while the shift reads
    // `p.0` — same base local, different field.
    //
    // Forged on `tuple_field_projected_shift` rather than on the sentinel because
    // the sentinel's `_3` is a `CheckedAdd` carrier `(u32, bool)`: re-pointing its
    // cond to `_3.1` compares a bool against `const 32u32`, which the
    // whole-function type audit refuses before the binder ever runs. That is how
    // the predecessor of this arm was red from birth — see the module header.
    // `p: (u32, u32)` has two integer fields, so this body is WELL-TYPED and
    // reaches the binder.
    //
    // RED under: comparing operands by base local instead of by whole `Place`.
    // MEASURED 2026-08-25 on this very body — with `v2_operands_structurally_equal`
    // weakened from `pa == pb` to `pa.local == pb.local`, this arm drops from 2
    // rows to 1 (the `p.1` guard suppresses the obligation about `p.0`) while the
    // positive control above stays at 1.
    let func = tuple_mutated("crossed_field", |v| {
        tuple_cond_operands(v)[1] = tuple_field(1, 1);
        *tuple_shift_amount(v) = tuple_field(1, 0);
    });
    assert_no_laundered_shift_obligation("crossed_field", &func);
}

#[test]
fn a_comparison_that_reads_its_own_flag_does_not_suppress() {
    // A forged `_4 = Lt(Copy _4, 32)` with the shift reading `_4`: the comparison
    // defines the very flag the terminator reads, so substituting it proves
    // nothing about the shift.
    //
    // THE SHAPE IS UNREACHABLE ON WELL-TYPED IR, and this arm pins the fail-closed
    // state it actually lands in rather than a state it cannot reach. The `Lt`'s
    // destination must be `bool` for the audit to admit it, so the flag local is
    // `bool`, so no operand of that comparison can BOTH overlap the flag's name
    // AND authenticate as the integer the shift amount is compared against. A name
    // collision cannot manufacture the overlap either: `place_to_var_name` already
    // demotes a source name shaped like another local's `_<k>` fallback token
    // (MEASURED: renaming `_3` to `_4` binds identically with the self-read test
    // present and absent). So today this body is refused WHOLE-FUNCTION with one
    // visible `MalformedTrustIr` marker, which claims nothing about the shift.
    //
    // The arm is still adversarial, and it RE-ARMS ITSELF: `assert_no_laundered_
    // shift_obligation` accepts only "both lanes report" or "refused with a
    // marker". If the comparison type audit is ever widened to admit a
    // bool-versus-integer `Lt`, the marker disappears and this arm immediately
    // demands both lanes report — i.e. it starts testing the self-read rule
    // (`place_names_overlap` in the projected path, `input == cond_place` in the
    // shipped one) the moment that rule becomes reachable, with no edit here.
    // DO NOT relax it to "zero rows is fine": zero rows with no marker is an
    // obligation lost in silence.
    let func = canary_mutated("self_reading_cond", |v| {
        let flag = serde_json::json!({ "Copy": { "local": 4, "projections": [] } });
        cond_operands(v)[1] = flag.clone();
        *shift_amount(v) = flag;
    });
    assert_no_laundered_shift_obligation("self_reading_cond", &func);
}

#[test]
fn a_lookalike_bits_constant_does_not_suppress() {
    // `Lt(_3.0, 16)` is not the u32 shift's `amount < 32` UB check. RED under:
    // dropping the shifted-width equality. Operand identity passes here — it is
    // the same place — so only the width check refuses.
    let func = canary_mutated("wrong_bits", |v| {
        let bits = &mut cond_operands(v)[2];
        assert_eq!(bits["Constant"]["Uint"][0], 32, "fixture drift: BITS must be 32");
        bits["Constant"]["Uint"][0] = serde_json::json!(16);
    });
    assert_both_lanes_report("wrong_bits", &func);
}

#[test]
fn an_inverted_assert_polarity_does_not_suppress() {
    // rustc's shift assert expects `true` — the cond IS the guard. RED under:
    // dropping `expected: true` from the terminator pattern.
    let func = canary_mutated("inverted_polarity", |v| {
        v["body"]["blocks"][1]["terminator"]["Assert"]["expected"] = serde_json::json!(false);
    });
    assert_both_lanes_report("inverted_polarity", &func);
}

#[test]
fn a_non_lt_comparison_does_not_suppress() {
    // `Le(_3.0, 32)` admits `_3.0 == 32`, which IS the UB case: a lookalike
    // comparison operator is not this shift's guard. RED under: accepting any
    // comparison opcode instead of `BinOp::Lt`.
    let func = canary_mutated("wrong_cmp", |v| {
        cond_operands(v)[0] = serde_json::json!("Le");
    });
    assert_both_lanes_report("wrong_cmp", &func);
}

#[test]
fn a_mismatched_opcode_does_not_suppress() {
    // An `Overflow(Shr)` assert does not guard a `Shl`. RED under: dropping the
    // `*assert_op != op` test.
    //
    // The lone arm whose assert lane reports NOTHING at the shift: its generic
    // fall-through looks for a unique `Shr` in the target and there is none, so
    // it emits a proof-gap row instead. The statement row is therefore the only
    // shift-family row, and it must be there.
    let func = canary_mutated("wrong_opcode", |v| {
        v["body"]["blocks"][1]["terminator"]["Assert"]["msg"] =
            serde_json::json!({ "Overflow": "Shr" });
    });
    assert_eq!(
        shift_family_rows(&func),
        vec!["ShiftOverflow(Shl)"],
        "an assert for the other shift opcode must not take this shift's obligation away"
    );
}

#[test]
fn a_second_entry_into_the_shift_block_does_not_suppress() {
    // THE SOLE-ENTRY ARM. A forged body must not launder the obligation through
    // an assert its executions can bypass: a new block jumps straight into the
    // shift's block, so the surviving assert row would not cover every execution.
    // RED under: deleting the `bypassed` scan. Here the binder itself still
    // succeeds, so the assert lane emits its own `ShiftOverflow` and BOTH rows
    // are kept — duplicates over-report, they never under-report.
    let func = canary_mutated("bypassed", |v| {
        let blocks = v["body"]["blocks"].as_array_mut().expect("blocks array");
        blocks.push(serde_json::json!({ "id": 3, "stmts": [], "terminator": { "Goto": 2 } }));
    });
    assert_eq!(
        shift_family_rows(&func),
        vec!["ShiftOverflow(Shl)", "ShiftOverflow(Shl)"],
        "a shift block with a second way in keeps BOTH rows"
    );
}
