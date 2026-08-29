// FALSIFICATION FIXTURES for the signed->unsigned `as` cast value relation
// (`guards::cast_definition_formula`), on REAL extracted MIR and decided by the
// real in-process ay solver.
//
// THE DEFECT. Three helpers sit on the `Rvalue::Cast` path and every one of them
// declines a signed->unsigned cast, each individually soundly:
// `is_modeled_identity_cast` (a negative source does not survive as identity),
// `widening_cast_result_range` (`*ss && !ds`), `narrowing_cast_result_range`
// (`*dw > *sw`). Their CONJUNCTION left the destination bounded only by its own
// type — a free variable — so a dominating `if x < 0 || x >= 16 { return 0; }`
// guard constrained the SOURCE and could never reach the cast RESULT.
//
// THE RELATION. Rust's `as` sign-extends to the destination width and
// reinterprets, so the result is the source's residue mod `2^to_w`. When
// `to_w >= from_w` the source range sits strictly inside `(-2^to_w, 2^to_w)` and
// the residue takes exactly two forms, giving the total value relation
// `dest == if src >= 0 { src } else { src + 2^to_w }`.
//
// EVERY fixture is PAIRED with its adversary, and both directions are
// load-bearing. The refute rows are not decoration: each one PANICS under stock
// rustc with `-C debug-assertions=on`, and each is exactly what a plausible
// wrong version of this relation would false-PROVE:
//
//   | refute fixture                  | the wrong relation it catches           |
//   |---------------------------------|-----------------------------------------|
//   | `s2u_negative_source_oob`       | plain `dest == src` (negatives dropped) |
//   | `s2u_negative_source_overflow`  | same, on an arithmetic obligation       |
//   | `s2u_samewidth_negative_oob`    | same, at `to_w == from_w`               |
//   | `s2u_narrowing_trunc_oob`       | the relation applied to a NARROWING cast|
//   | `s2u_narrowing_negative_oob`    | same, with a negative source            |
//
// The two narrowing rows are the UB-blessing care-point. A narrowing
// signed->unsigned cast truncates mod `2^to_w`, so `dest == src` is FALSE there;
// conjoined with the destination's own `[0, 2^to_w-1]` range it is CONTRADICTORY
// for a source outside that window, and a contradictory hypothesis set proves
// everything. `value_facts::truncate_nonneg_tag_as_int` records the same burn on
// the enum-discriminant lane. Both fixtures keep a source window that is entirely
// OUTSIDE `[0, 255]` precisely so the vacuity would be reachable.
//
// The fixtures are real MIR extracted with `-Ztrust-dump=mir-only:<dir>`, so the
// lowering under test is the one the compiler actually emits.
use trust_types::{Formula, VerifiableFunction, VerificationResult};

/// Stack for the solver thread: VC GENERATION and the solver search both recurse
/// over the whole formula, and libtest's default test-thread stack is smaller
/// than rustc's own verification thread. A harness allowance, not a production
/// claim.
const SOLVER_STACK_BYTES: usize = 16 * 1024 * 1024;

fn load(json: &str) -> VerifiableFunction {
    serde_json::from_str(json).expect("fixture MIR must deserialize")
}

/// Every obligation of `func`, decided by the real in-process ay.
fn verdicts(func: &VerifiableFunction) -> Vec<(String, VerificationResult)> {
    let func = func.clone();
    std::thread::Builder::new()
        .stack_size(SOLVER_STACK_BYTES)
        .spawn(move || {
            let vcs = trust_vcgen::generate_vcs(&func);
            let router = trust_router::Router::deterministic_in_process_ay(30_000);
            let results = router.verify_all(&vcs);
            vcs.iter()
                .zip(results)
                .map(|(vc, (_, result))| (format!("{:?}", vc.kind), result))
                .collect::<Vec<_>>()
        })
        .expect("spawn solver thread")
        .join()
        .expect("solver thread must not panic")
}

/// The function's obligations, all of them proved. `why` names the Rust program
/// property that makes this the CORRECT verdict.
fn assert_every_obligation_proved(json: &str, why: &str) {
    let func = load(json);
    let rows = verdicts(&func);
    assert!(!rows.is_empty(), "{}: fixture must carry at least one obligation", func.name);
    for (kind, result) in &rows {
        assert!(
            matches!(result, VerificationResult::Proved { .. }),
            "{} [{kind}]: {why} — this program cannot fault, so a non-proof is a FALSE \
             REFUTATION; got {result:?}",
            func.name
        );
    }
}

/// At least one obligation refuted. `why` names the input that PANICS.
fn assert_some_obligation_refuted(json: &str, why: &str) {
    let func = load(json);
    let rows = verdicts(&func);
    assert!(
        rows.iter().any(|(_, r)| matches!(r, VerificationResult::Failed { .. })),
        "{}: {why} — proving it means the cast relation is WRONG, not that the verifier \
         got stronger; got {rows:?}",
        func.name
    );
}

/// Every `Eq(Var(_), rhs)` conjunct of `formula`, as debug strings of the `rhs`.
fn definition_rhs_strings(formula: &Formula, out: &mut Vec<String>) {
    match formula {
        Formula::And(xs) | Formula::Or(xs) => {
            for x in xs {
                definition_rhs_strings(x, out);
            }
        }
        Formula::Not(x) => definition_rhs_strings(x, out),
        Formula::Implies(a, b) => {
            definition_rhs_strings(a, out);
            definition_rhs_strings(b, out);
        }
        Formula::Eq(lhs, rhs) => {
            if matches!(lhs.as_ref(), Formula::Var(..)) {
                out.push(format!("{rhs:?}"));
            }
        }
        _ => {}
    }
}

// --- the false refutation this lane exists to close -------------------------

/// `fn(a: &[u8; 16], x: i32) -> u8 { if x < 0 || x >= 16 { return 0; } a[x as usize] }`
///
/// THE HEADLINE: `i32 as usize`, the shape every guarded index conversion has.
#[test]
fn widening_signed_to_unsigned_guarded_index_proves() {
    assert_every_obligation_proved(
        include_str!("fixtures/s2u_widen_guarded_index.json"),
        "the guard pins x to [0, 16) and the cast is value-preserving there",
    );
}

/// `fn(x: i8) -> u64 { if x < 0 { return 0; } (x as u64) + 1 }` — a wide widening.
#[test]
fn widening_signed_to_unsigned_guarded_add_proves() {
    assert_every_obligation_proved(
        include_str!("fixtures/s2u_widen_i8_guarded_add.json"),
        "a non-negative i8 widens to at most 127, so `+ 1` cannot overflow u64",
    );
}

/// `fn(x: i32) -> u32 { if x < 0 || x > 100 { return 0; } (x as u32) + 1 }`
///
/// `to_w == from_w`: the same-width signedness reinterpret, which
/// `is_modeled_identity_cast` also declines.
#[test]
fn same_width_signed_to_unsigned_guarded_add_proves() {
    assert_every_obligation_proved(
        include_str!("fixtures/s2u_samewidth_guarded_add.json"),
        "the guard pins x to [0, 100] and the same-width cast is the identity there",
    );
}

/// The emitted definition is the TWO'S-COMPLEMENT relation, not a plain equality:
/// the negative arm must add the destination's modulus.
///
/// A structural row, so the shape is pinned even where a solver verdict happens to
/// coincide. `2^64` is the modulus of this fixture's `usize` destination. BOTH arms
/// are asserted: the non-negative one alone is a plain equality (which drops every
/// negative source), and the negative one alone would be equally wrong.
#[test]
fn the_emitted_definition_carries_both_twos_complement_arms() {
    let func = load(include_str!("fixtures/s2u_widen_guarded_index.json"));
    let vcs = trust_vcgen::generate_vcs(&func);
    let mut rhs = Vec::new();
    for vc in &vcs {
        definition_rhs_strings(&vc.formula, &mut rhs);
    }
    let source = "Var(\"x\", Int)".to_string();
    let wrapped = format!("Add({source}, Int({}))", 1u128 << 64);
    assert!(
        rhs.contains(&source),
        "the non-negative arm must define the cast result as the source itself; \
         definitions: {rhs:?}"
    );
    assert!(
        rhs.contains(&wrapped),
        "the negative arm must define the cast result as `src + 2^64`; a plain equality \
         would drop every negative source. definitions: {rhs:?}"
    );
}

// --- MUST STILL REFUTE ------------------------------------------------------

/// `fn(a: &[u8; 4], x: i32) -> u8 { if x >= 0 { return 0; } a[x as usize] }`
///
/// `-1i32 as usize` is `usize::MAX`. Runtime-checked: PANICS.
#[test]
fn negative_source_reinterpreted_as_huge_index_is_still_refuted() {
    assert_some_obligation_refuted(
        include_str!("fixtures/s2u_negative_source_oob.json"),
        "a negative source reinterprets to a huge unsigned index and goes out of bounds",
    );
}

/// `fn(x: i32) -> u64 { let y = x as u64; y + 1 }`
///
/// `x = -1` gives `y == u64::MAX`, so `y + 1` overflows. Runtime-checked: PANICS.
#[test]
fn negative_source_widened_then_incremented_is_still_refuted() {
    assert_some_obligation_refuted(
        include_str!("fixtures/s2u_negative_source_overflow.json"),
        "x = -1 widens to u64::MAX, so the increment overflows",
    );
}

/// `fn(a: &[u8; 16], x: i8) -> u8 { if x >= 0 { return 0; } a[(x as u8) as usize] }`
///
/// `-128i8 as u8` is `128`. Runtime-checked: PANICS. The same-width case, where
/// the relation DOES fire — so this row is what separates the correct `else` arm
/// from an inverted or dropped one.
#[test]
fn same_width_negative_source_index_is_still_refuted() {
    assert_some_obligation_refuted(
        include_str!("fixtures/s2u_samewidth_negative_oob.json"),
        "a negative i8 reinterprets into the upper half of u8 and goes out of bounds",
    );
}

/// `fn(a: &[u8; 4], x: i32) -> u8 { if x < 1000 || x > 1005 { return 0; } a[(x as u8) as usize] }`
///
/// `1000i32 as u8` is `232`. Runtime-checked: PANICS. The source window is
/// entirely above `u8::MAX`, so a relation that claimed `dest == src` here would
/// be CONTRADICTORY with the destination's own range and would prove the OOB
/// vacuously.
#[test]
fn narrowing_signed_to_unsigned_truncation_is_still_refuted() {
    assert_some_obligation_refuted(
        include_str!("fixtures/s2u_narrowing_trunc_oob.json"),
        "the narrowing cast drops the high bits and the truncated index leaves the array",
    );
}

/// `fn(a: &[u8; 4], x: i32) -> u8 { if x >= 0 { return 0; } a[(x as u8) as usize] }`
///
/// `-1i32 as u8` is `255`. Runtime-checked: PANICS. Narrowing AND negative — the
/// other half of the vacuity hazard.
#[test]
fn narrowing_negative_source_is_still_refuted() {
    assert_some_obligation_refuted(
        include_str!("fixtures/s2u_narrowing_negative_oob.json"),
        "a negative source truncates into the top of u8 and leaves the array",
    );
}

// --- control ----------------------------------------------------------------

/// `fn(a: &[u8; 16], x: u32) -> u8 { if x >= 16 { return 0; } a[x as usize] }`
///
/// UNSIGNED source: `is_modeled_identity_cast` already accepts it. This row holds
/// the "the new branch did not disturb the clean lanes" direction.
#[test]
fn unsigned_source_control_is_unchanged() {
    assert_every_obligation_proved(
        include_str!("fixtures/s2u_control_unsigned_index.json"),
        "an unsigned widening cast was already modeled as the identity",
    );
}
