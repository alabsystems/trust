// FALSIFICATION FIXTURES for the body-less rustc bit/arithmetic intrinsics,
// on REAL extracted MIR and decided by the real in-process ay solver.
//
// `crates/trust-vcgen/src/generate/intrinsic_semantics.rs` gives those
// intrinsics a value semantics. Unlike every other lane in the crate it ADDS
// facts to the hypothesis set, so its failure mode is a FALSE PROOF rather than
// an incompleteness. The exhaustive width-8 differential in
// `generate/intrinsic_semantics_tests.rs` checks the definitions against the
// real Rust operations; this file checks the OTHER half — that the definitions
// reach an actual obligation and that a wrong one would be caught.
//
// EVERY fixture below comes in a PAIR, and both directions are load-bearing:
//
//   * the PROVE row is what the lane exists to deliver. Before it, the
//     destination of an intrinsic call was an unconstrained havoc, so each of
//     these clauses was REFUTED with an absurd counterexample (measured on this
//     very corpus: `ctpop_u32_le32` refuted with `ctpop = 4294967295`).
//   * the REFUTE row is the falsification. Each one is TRUE under some specific
//     way of getting the definition wrong, and FALSE of the real intrinsic:
//
//     | refute fixture            | the wrong model it catches                |
//     |---------------------------|-------------------------------------------|
//     | `ctpop_u32_le31`          | an off-by-one width (`W-1` instead of `W`)|
//     | `ctpop_u8_le7`            | same, at width 8                          |
//     | `ctpop_u32_ge1`           | a nonzero lower bound (`ctpop(0) == 0`)   |
//     | `bswap_u32_be`            | a NO-OP `bswap` (identity at every width) |
//     | `bitrev_u8_one_wrong`     | a NO-OP `bitreverse`                      |
//     | `ctlz_u32_unguarded_le31` | `ctlz(0) == 0` — the `_nonzero` confusion |
//     | `sat_add_gt`              | a STRICT saturating-add lower bound       |
//
// THREE PROVE-DIRECTION ROWS DID NOT LAND, and they are asserted in their
// measured state by `residual_rows_are_decided_by_ay_but_not_strictly_certifiable`
// rather than quietly dropped. See that test for the evidence that the boundary
// is in the strict proof-certification layer and predates this lane.
//
// The fixtures are the real MIR extracted with `-Ztrust-dump=mir:<dir>` from
// `fx.rs` (each function's source is quoted at its test), so the callee spelling
// under test is the one the compiler actually emits —
// `@trust-rustc-intrinsic::core::intrinsics::ctpop::<u32>` — not a hand-built
// approximation of it.
//
// NOTE ON THE PROVE ROWS: they assert the ay verdict, not kernel certification.
// A `Proved` with no clean-kernel token is reported `Unknown` under
// `-Ztrust-policy=certify`, so these rows show the obligation is now DECIDABLE
// from the intrinsic's definition; whether the resulting BV-bridge term also
// mints a kernel certificate is a separate lane and is NOT claimed here.
use trust_types::{VcKind, VerifiableFunction, VerificationResult};

fn load(json: &str) -> VerifiableFunction {
    serde_json::from_str(json).expect("fixture MIR must deserialize")
}

/// Stack for the solver thread below.
///
/// MEASURED, and worth recording rather than hiding behind a magic number: the
/// `ctpop::<u32>` rows overflow libtest's DEFAULT 2 MiB test-thread stack in a
/// debug build (`thread '…' has overflowed its stack`) and pass at 4 MiB
/// (`RUST_MIN_STACK=4194304`, bisected). The depth comes from the 32-term
/// `int2bv`/`extract` sum, which every recursive `Formula` pass walks; the
/// solver search over the same term is what makes the FALSE rows slow (26 ms
/// when the clause is proved, ~26-34 s when a witness word must be constructed).
///
/// This is a test-harness allowance, NOT a production claim. rustc runs
/// compilation (and therefore verification) on a thread with
/// `rustc_interface::util::DEFAULT_STACK_SIZE` = 8 MiB in a RELEASE build, whose
/// frames are smaller than these, so the production margin is comfortable — but
/// that has not been measured end-to-end, because doing so needs a stage2
/// rebuild. It is one of the reasons `MAX_EXACT_INTRINSIC_WIDTH` is 32.
const SOLVER_STACK_BYTES: usize = 16 * 1024 * 1024;

/// The `#[ensures]` obligation of `func`, decided by the real in-process ay.
fn postcondition_verdict(func: &VerifiableFunction) -> VerificationResult {
    // BOTH halves run on the big-stack thread: VC GENERATION overflows the
    // default libtest stack too, not just the solver search (measured — moving
    // only the solver across left the overflow exactly where it was).
    let func = func.clone();
    std::thread::Builder::new()
        .stack_size(SOLVER_STACK_BYTES)
        .spawn(move || {
            let vcs = trust_vcgen::generate_vcs(&func);
            let post =
                vcs.iter().find(|vc| matches!(vc.kind, VcKind::Postcondition)).unwrap_or_else(
                    || panic!("{}: the ensures clause must produce a Postcondition VC", func.name),
                );
            let router = trust_router::Router::deterministic_in_process_ay(30_000);
            let results = router.verify_all(std::slice::from_ref(post));
            results.into_iter().next().expect("one verdict per VC").1
        })
        .expect("spawn solver thread")
        .join()
        .expect("solver thread must not panic")
}

fn assert_proved(json: &str) {
    let func = load(json);
    let verdict = postcondition_verdict(&func);
    assert!(
        matches!(verdict, VerificationResult::Proved { .. }),
        "{}: the clause is TRUE of the intrinsic and must be proved from its definition; \
         got {verdict:?}",
        func.name
    );
}

fn assert_not_proved(json: &str) {
    let func = load(json);
    let verdict = postcondition_verdict(&func);
    assert!(
        !matches!(verdict, VerificationResult::Proved { .. }),
        "{}: the clause is FALSE of the real intrinsic — proving it means the model is \
         WRONG, not that the verifier got stronger; got {verdict:?}",
        func.name
    );
}

// --- ctpop -----------------------------------------------------------------

/// `fn ctpop_u32_le32(x: u32) -> u32 ensures result <= 32 { ctpop(x) }`
///
/// THE HEADLINE. `x.count_ones() <= 32` was previously not merely unproved but
/// refutable: the intrinsic has no MIR, the only model was "cannot panic", and
/// the destination was a free `u32`.
#[test]
fn ctpop_result_is_bounded_by_the_argument_width() {
    assert_proved(include_str!("fixtures/intrinsic_ctpop_u32_le32_mir.json"));
}

/// `ensures result <= 31` — FALSE (`u32::MAX.count_ones() == 32`).
#[test]
fn ctpop_bound_is_not_off_by_one() {
    assert_not_proved(include_str!("fixtures/intrinsic_ctpop_u32_le31_mir.json"));
}

/// `fn ctpop_u8_le8(x: u8) -> u32 ensures result <= 8 { ctpop(x) }`
///
/// The width must come from the ARGUMENT type, not the destination: `ctpop`
/// returns `u32` for every `T`, so a model that read the dest width would give
/// `<= 32` here and this row would not prove.
#[test]
fn ctpop_width_comes_from_the_argument_not_the_u32_destination() {
    assert_proved(include_str!("fixtures/intrinsic_ctpop_u8_le8_mir.json"));
}

/// `ensures result <= 7` at width 8 — FALSE (`u8::MAX.count_ones() == 8`).
#[test]
fn ctpop_width8_bound_is_not_off_by_one() {
    assert_not_proved(include_str!("fixtures/intrinsic_ctpop_u8_le7_mir.json"));
}

/// `ensures result >= 1` — FALSE at `x == 0`.
#[test]
fn ctpop_has_no_spurious_nonzero_lower_bound() {
    assert_not_proved(include_str!("fixtures/intrinsic_ctpop_u32_ge1_mir.json"));
}

/// `requires x == 0 ensures result == 0` and `requires x == u32::MAX ensures
/// result == 32`. These need the EXACT sum-of-bits definition, not the range
/// bound — the bound alone leaves both open.
#[test]
fn ctpop_exact_definition_decides_the_two_extreme_words() {
    assert_proved(include_str!("fixtures/intrinsic_ctpop_u32_zero_is_zero_mir.json"));
    assert_proved(include_str!("fixtures/intrinsic_ctpop_u32_ones_is_32_mir.json"));
}

// --- bswap ------------------------------------------------------------------

/// `requires x == 0x01020304 ensures result == 0x04030201` — the endianness
/// discriminator. Only an exact byte cascade decides it.
#[test]
fn bswap_reverses_byte_order() {
    assert_proved(include_str!("fixtures/intrinsic_bswap_u32_le_mir.json"));
}

/// `requires x == 0x01020304 ensures result == 0x01020304` — FALSE. A `bswap`
/// modeled as a no-op (or as any involution that happens to fix this word) would
/// prove it.
#[test]
fn bswap_is_not_modeled_as_a_no_op() {
    assert_not_proved(include_str!("fixtures/intrinsic_bswap_u32_be_mir.json"));
}

/// `fn bswap_u8_identity(x: u8) -> u8 ensures result == x { bswap(x) }`
///
/// THE TRAP: at width 8 `swap_bytes` IS the identity. A definition that reverses
/// unconditionally fails exactly here and nowhere else.
#[test]
fn bswap_at_width_8_is_the_identity() {
    assert_proved(include_str!("fixtures/intrinsic_bswap_u8_identity_mir.json"));
}

// --- bitreverse -------------------------------------------------------------

/// `requires x == 1 ensures result == 128` at width 8.
#[test]
fn bitreverse_moves_the_lsb_to_the_msb() {
    assert_proved(include_str!("fixtures/intrinsic_bitrev_u8_one_mir.json"));
}

/// `requires x == 1 ensures result == 1` — FALSE. Separates `bitreverse` from
/// `bswap`, which IS the identity at this width.
#[test]
fn bitreverse_is_not_the_width8_identity() {
    assert_not_proved(include_str!("fixtures/intrinsic_bitrev_u8_one_wrong_mir.json"));
}

// --- ctlz / cttz: the zero edge --------------------------------------------

// `requires x >= 1 ensures result <= 31` over `ctlz` — the clause the zero-iff
// pair exists to deliver (`ctlz(x) == 32 <-> x == 0` plus the `[0, 32]` bound is
// what makes a `1 << (31 - lz)` shift defined) — is MEASURED as
// decided-but-not-strictly-certifiable, and is asserted in that state by
// `residual_rows_are_decided_by_ay_but_not_strictly_certifiable` below. It is
// deliberately NOT asserted as proved here.

/// `ensures result <= 31` over `ctlz` WITHOUT the `requires` — FALSE, because
/// `ctlz(0) == 32`.
///
/// This is the `_nonzero`-confusion fixture: rustc has SEPARATE
/// `ctlz_nonzero`/`cttz_nonzero` intrinsics that are UB at zero, and a model
/// that conflated them (or that assumed `ctlz(0) == 0`) would prove this row.
#[test]
fn ctlz_at_zero_is_the_width_not_zero() {
    assert_not_proved(include_str!("fixtures/intrinsic_ctlz_u32_unguarded_le31_mir.json"));
    // The positive statement of the same edge, for `cttz`:
    // `requires x == 0 ensures result == 32`.
    assert_proved(include_str!("fixtures/intrinsic_cttz_u32_zero_is_32_mir.json"));
}

// --- cttz / ctlz: the EXACT definitions (§5 step 1 remainder, 2026-08-30) ---
//
// Every fixture here comes from the same `-Ztrust-dump=mir:` recipe as the rest
// of this file (source quoted per test; stage1 trustc of 283d1906e6). The rows
// need the EXACT compositions — `cttz(x) = ctpop(!x & (x-1))`, `ctlz(x)` the
// same mask over the bit-reversed word — because the range + iff facts alone
// leave a constant interior value open in both directions.
//
// THE EQUATIONS RIDE A CONSTANT-ARGUMENT GATE, and the tests below pin all
// three sides of it (the measured table is at `intrinsic_semantics.rs`'s
// header): a LITERAL argument gets the definition (prove + refute rows), a
// free or merely `requires`-pinned parameter does not (gate rows), and the
// free-argument iff+range proof that the gate protects stays fast (the
// regression row).

/// `fn cttz_u8_lit8_is_3() -> u32 ensures result == 3 { cttz(8u8) }`
///
/// 8 is `0b1000`: an interior value the `[0, W]` bound and the zero-iff cannot
/// decide. Only the exact mask term pins 3 — and a mask built with `x + 1`, a
/// dropped `BvNot`, or a reversed subtraction all give a different count here.
/// The u32 row (`cttz(u32::MAX) == 0`) runs the same equation at the width
/// cap; the zero row (`cttz(0u8) == 8`) is the wrap-is-the-definition edge.
#[test]
fn cttz_exact_definition_decides_constant_interior_values() {
    assert_proved(include_str!("fixtures/intrinsic_cttz_u8_lit8_is_3_mir.json"));
    assert_proved(include_str!("fixtures/intrinsic_cttz_u8_lit0_is_8_mir.json"));
    assert_proved(include_str!("fixtures/intrinsic_cttz_u32_litmax_is_0_mir.json"));
}

/// `ensures result == 4` over `cttz(8u32)` — FALSE (`trailing_zeros == 3`).
/// An off-by-one in the mask (counting the lowest SET bit as well) proves it.
#[test]
fn cttz_exact_definition_is_not_off_by_one() {
    assert_not_proved(include_str!("fixtures/intrinsic_cttz_u32_lit8_is_not_4_mir.json"));
}

/// `ensures result == 1` over `cttz(0u8)` — FALSE (`cttz(0) == 8`).
///
/// The task-brief falsification row: a definition whose zero case leaks a
/// single count — or any `_nonzero` conflation — is caught here, exactly like
/// `count_ones(0) == 1` would be for `ctpop`.
#[test]
fn cttz_at_zero_is_the_width_not_one() {
    assert_not_proved(include_str!("fixtures/intrinsic_cttz_u8_lit0_is_not_1_mir.json"));
}

/// `ensures result == 7` over `ctlz(1u8)`, and `== 15` over `ctlz(1u16)`.
#[test]
fn ctlz_exact_definition_decides_constant_interior_values() {
    assert_proved(include_str!("fixtures/intrinsic_ctlz_u8_lit1_is_7_mir.json"));
    assert_proved(include_str!("fixtures/intrinsic_ctlz_u16_lit1_is_15_mir.json"));
}

/// `ensures result == 0` over `ctlz(1u8)` — FALSE (`leading_zeros == 7`).
///
/// THE REVERSAL DISCRIMINATOR: `cttz(1) == 0`, so a `ctlz` accidentally built
/// without the bit-reversal — the exact mistake the shared-mask composition
/// invites — would prove this row. It must stay unproved.
#[test]
fn ctlz_is_not_cttz_in_disguise() {
    assert_not_proved(include_str!("fixtures/intrinsic_ctlz_u8_lit1_is_not_0_mir.json"));
}

/// `fn cttz_u32_nonzero_le31(x: u32) requires x >= 1 ensures result <= 31` —
/// the free-argument shift-definedness clause, TRUE, decided by iff + range in
/// 8 ms (measured 2026-08-30).
///
/// THE REGRESSION GUARD FOR THE CONSTANT GATE. With the exact equation emitted
/// for this FREE argument the same row TIMES OUT at 120 s (measured — the
/// module-header table), so this test is what fails, by timeout, if someone
/// widens the gate without solving the Int<->BV interference. Its `ctlz` twin
/// is `ctlz_nonzero_upper_bound_is_proved` above.
#[test]
fn cttz_free_argument_shift_definedness_stays_fast_and_proved() {
    assert_proved(include_str!("fixtures/intrinsic_cttz_u32_nonzero_le31_mir.json"));
}

/// `requires x == 8 ensures result == 3` with a PARAMETER argument (and the
/// `ctlz` twin at `x == 1 -> == 31`) — TRUE of the intrinsic, but the argument
/// operand is `Copy(x)`, not a constant, so the exact equation is deliberately
/// NOT emitted and the rows must stay UNPROVED: range + iff bound the result
/// without pinning it.
///
/// THIS IS THE GATE'S PIN, in both directions: it fails the day the gate
/// widens to `requires`-pinned parameters. That widening must bring a fresh
/// measurement of the free-argument rows first — the interference the gate
/// exists to block lives exactly there.
#[test]
fn requires_pinned_parameters_stay_outside_the_constant_gate() {
    assert_not_proved(include_str!("fixtures/intrinsic_cttz_u32_eight_is_3_mir.json"));
    assert_not_proved(include_str!("fixtures/intrinsic_ctlz_u32_one_is_31_mir.json"));
}

// --- saturating intrinsics --------------------------------------------------

// `ensures result >= a` / `ensures result <= a` over the INTRINSIC spelling.
// The identical METHOD spelling was already modeled; the intrinsic form — which
// is what `#![feature(core_intrinsics)]` code and the method BODIES emit — fell
// through to a havoc because the recognizer required a `::num::` path. It now
// reaches the SAME clamp model, which the residual test below is what
// demonstrates: both spellings land on the identical strict-certification
// boundary, which is exactly what "reaches the same model" means here.

/// `requires x >= 1 ensures result <= 31` over the `ctlz` intrinsic — PROVED.
///
/// This row used to sit in the residual test below: ay decided it UNSAT and the
/// mandatory strict UNSAT-proof validation then rejected the proof with
/// `step tN uses unsupported theory lemma kind Generic in strict mode`, so the
/// honest verdict was `Unknown`. As of 2026-08-24 it certifies.
///
/// PROMOTED ON EVIDENCE, not on the say-so of the assertion that flagged it:
///
///   * The change is PER ROW, not a lost check. The other three residual rows still
///     return `Unknown` with `(incomplete self-check-rejected)` on the same path —
///     if strict validation had been dropped they would all have flipped together.
///   * STABLE: measured over three consecutive runs, `Proved` every time. A verdict
///     that appears only sometimes must not become an unconditional assertion.
///   * The negative controls still hold. `saturating_add_lower_bound_is_not_strict`
///     (a clause that is FALSE at `b == 0`), `bswap_is_not_modeled_as_a_no_op`,
///     `bitreverse_is_not_the_width8_identity`, `ctpop_has_no_spurious_nonzero_lower_bound`
///     and `ctpop_bound_is_not_off_by_one` all still fail to prove, so the lane is
///     not proving things indiscriminately.
///   * The proposition is true: `ctlz` of a nonzero `u32` lies in `0..=31`, and
///     reaches 32 only at `x == 0`, which the precondition excludes.
///     `ctlz_at_zero_is_the_width_not_zero` pins that boundary separately.
#[test]
fn ctlz_nonzero_upper_bound_is_proved() {
    assert_proved(include_str!("fixtures/intrinsic_ctlz_u32_nonzero_lt32_mir.json"));
}

/// THE RESIDUAL, stated rather than hidden.
///
/// Two shapes in this corpus are DECIDED by the facts — the ay engine computes
/// UNSAT — and are then rejected by the mandatory strict UNSAT-proof validation
/// with `step tN uses unsupported theory lemma kind Generic in strict mode`. The
/// verdict is `Unknown`, and `Unknown` is the honest answer: an uncertified UNSAT
/// proves nothing under `-Ztrust-policy=certify`. UNPROVED IS NOT PROVED, so these
/// rows are asserted in their MEASURED state rather than promoted.
///
///   * `sat_add_ge` / `sat_sub_le` — the saturating clamp model.
///
/// (`ctlz_u32_nonzero_lt32` was the third; it now certifies and has moved to
/// `ctlz_nonzero_upper_bound_is_proved` above. That it moved ALONE, while these
/// did not, is the evidence that the strict layer is still running here.)
///
/// THE MISSING PIECE IS NOT IN THIS LANE, and the third row below is the
/// evidence: `fixtures/sat_add_ge.json` is the ALREADY-SHIPPED METHOD spelling
/// (`core::num::<impl u32>::saturating_add`, the fixture
/// `tests/saturating_call_model.rs` covers), which predates this work and hits
/// the SAME boundary. The intrinsic spelling therefore reaches exactly the same
/// place the method spelling reaches — which is what "routed into the existing
/// clamp model" was supposed to mean — and the residual belongs to the strict
/// proof-certification layer's theory-lemma vocabulary, not to the definitions.
///
/// This test FAILS the day that layer learns the lemma kind — deliberately. Move
/// the row up to `assert_proved` then, on the same evidence the ctlz row required;
/// do not delete this comment without re-measuring.
#[test]
fn residual_rows_are_decided_by_ay_but_not_strictly_certifiable() {
    // Trust: `ctlz_u32_nonzero_lt32` was PROMOTED out of this list on 2026-08-25.
    // The strict-certification layer learned the lemma kind its clause needed, so
    // the row is now `Proved { strength: ProofStrength { reasoning: Smt, assurance:
    // SmtBacked } }` — measured, not assumed. This test asked for exactly that
    // move ("Promote the row to `assert_proved` and update the doc above"), and it
    // is asserted below rather than merely dropped: a row that silently stopped
    // being proved again would otherwise go unnoticed.
    //
    // The remaining three rows still sit at the boundary. Do NOT delete this test
    // when the last one is promoted; it is the instrument that tells you the
    // boundary moved.
    for (name, json) in [
        ("sat_add_ge (intrinsic spelling)", include_str!("fixtures/intrinsic_sat_add_ge_mir.json")),
        ("sat_sub_le (intrinsic spelling)", include_str!("fixtures/intrinsic_sat_sub_le_mir.json")),
        // The METHOD spelling of the same clause, already in the tree before this
        // lane existed: the boundary is NOT something the intrinsic lane introduced.
        ("sat_add_ge (method spelling, pre-existing)", include_str!("fixtures/sat_add_ge.json")),
    ] {
        let func = load(json);
        let verdict = postcondition_verdict(&func);
        assert!(
            !matches!(verdict, VerificationResult::Proved { .. }),
            "{name}: the strict-certification residual is GONE — this is progress, not a \
             regression. Promote the row to `assert_proved` and update the doc above. \
             Got {verdict:?}"
        );
    }

    // The promoted row, now asserted in the POSITIVE direction.
    let func = load(include_str!("fixtures/intrinsic_ctlz_u32_nonzero_lt32_mir.json"));
    let verdict = postcondition_verdict(&func);
    assert!(
        matches!(verdict, VerificationResult::Proved { .. }),
        "ctlz_u32_nonzero_lt32 was promoted on 2026-08-25 after the strict-certification \
         layer learned its lemma kind. Losing it again is a REGRESSION in that layer, not a \
         return to a known boundary. Got {verdict:?}"
    );
}

/// `ensures result > a` — FALSE at `b == 0`. Pins that the clamp model gives the
/// NON-strict bound and nothing stronger.
#[test]
fn saturating_add_lower_bound_is_not_strict() {
    assert_not_proved(include_str!("fixtures/intrinsic_sat_add_gt_mir.json"));
}
