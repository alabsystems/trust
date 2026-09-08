//! REAL-MIR matrix for the ENUM VARIANT PAYLOAD range fact.
//!
//! An enum payload read through `Downcast(v).Field(i)` used to lose its declared
//! integer range. `Ty::Adt::fields` is the FLAT union view an enum carries for
//! the `SetDiscriminant` lowering — `[("__tag", i64), ("__v0_0", …), …]` — so
//! `project_ty` answered a variant-relative `Field(i)` with flat slot `i`, and
//! for every `Downcast(v).Field(0)` that slot is `__tag: i64`. The bound
//! `resolve_field_scalar_range` then attached was not missing, it was WRONG, and
//! wrong in both directions at once:
//!
//! * a payload NARROWER than `i64` got only the vacuous `i64` range, so a safe
//!   obligation whose safety comes from the payload's own declared width was
//!   FALSE-REFUTED (`enum_payload_u8_mul`, measured at pristine HEAD as
//!   `overflow:mul FAILED … e@0.0 = 1431655766` for a `u8` payload);
//! * a payload wider in the unsigned direction (`u64`) got a range EXCLUDING its
//!   real values, deleting the only counterexample — a FALSE PROOF
//!   (`enum_payload_u64_overflow` and `enum_payload_variant1_u64_overflow`, both
//!   reported `proved` AND kernel-certified at pristine HEAD, for programs that
//!   panic at `u64::MAX`).
//!
//! Every fixture under `tests/fixtures/enum_payload_*_mir.json` /
//! `struct_field_mul_mir.json` is the compiler's OWN extracted verification
//! input, captured verbatim with
//!
//! ```text
//! trustc --edition 2021 --crate-type lib -Ztrust-dump=mir:<dir> <row>.rs
//! ```
//!
//! and edited only by minifying the JSON and rewriting the absolute `file` span
//! path to `<dump-root>/<row>.rs` (the same convention as `abs_guarded.json`).
//! The source of each row is quoted at its test.
//!
//! OPTIMISATION LEVEL IS PART OF THE CLAIM, and the two halves of the matrix do
//! not answer to it the same way. Re-extracting every row above with `-O` and
//! deciding both dumps: the `u64` FALSE PROOFS reproduce at BOTH levels — the
//! payload read stays a `Downcast(v).Field(i)` whatever the optimiser does — but
//! the NARROW-payload false refutations are a default-optimisation phenomenon,
//! because at `-O` rustc materialises the payload into a bare local first and
//! `conjoin_local_type_ranges` bounds THAT (the same mechanism the nested row
//! below documents). So the fixtures here are the DEFAULT-optimisation dumps:
//! that is the extraction in which both halves are live at once, and a matrix
//! built from `-O` dumps would have silently lost the false-refutation half.
//!
//! The REFUTE rows are the adversarial half and each one genuinely panics; the
//! panicking input is named in the test so the claim is checkable without
//! re-running the sweep.
//!
//! THE BLAST RADIUS IS ORDINARY RUST, NOT AN EXOTIC SHAPE. `Option<u64>` — the
//! commonest enum in the language — is in the class: `match e { Some(x) => x + 1,
//! None => 0 }` reported `2 proved, 0 failed`, both kernel-certified, at pristine
//! HEAD, for a function that panics on `Some(u64::MAX)`. In the class too: a
//! struct-variant payload, a tuple variant read at `.1`, a payload behind `&E`, a
//! three-variant enum, an enum nested in a struct, `#[repr(u8)]` with explicit
//! discriminants, a `u128` payload, and a single-variant enum. Each has its own
//! row below, and each row states its own pristine-HEAD verdict rather than
//! inheriting `Option<u64>`'s — the `u128` one was `Proved` WITHOUT a kernel
//! certificate, which is a different (weaker) starting point from the rest.
//!
//! And it was not confined to synthetic rows: two functions in
//! `crates/trust-clean/fixtures` are decided differently by this lane, one of
//! them a kernel-certified discharge that rested on the wrong bound. Both are
//! pinned at the end of this file.
//!
//! The PRE-P4 half of the matrix is the second failure mode, and it is the one a
//! `!variants.is_empty()` gate does not survive: `Ty::Adt::variants` is
//! `#[serde(default)]`, so a serialized `Ty::Adt` written before PHASE 4 (dump
//! fixtures, solver caches, proof certificates) deserializes with NO variants
//! while keeping the enum-shaped flat view. `pre_p4` below reproduces exactly
//! that wire shape from each populated fixture by deleting the `variants` key,
//! and asserts the resulting verdicts are unchanged in BOTH directions — the
//! false proofs stay refuted and the payload-width proofs stay proved. Both are
//! needed: the erased shape still declares the payload type in its `__v{v}_*`
//! slots, and only reading THAT slot (rather than flat slot `i`, the `__tag`)
//! produces both outcomes at once.

use trust_types::{VcKind, VerifiableFunction, VerificationResult};

fn load(json: &str) -> VerifiableFunction {
    serde_json::from_str(json).expect("fixture MIR must deserialize")
}

/// The PRE-P4 wire shape of a fixture: the same MIR with every `Ty::Adt`'s
/// `variants` KEY DELETED, which is what serialized `Ty::Adt` JSON older than
/// PHASE 4 actually looks like (the field is `#[serde(default)]`, so the key's
/// absence deserializes to an empty variant list while the enum-shaped flat
/// `fields` view — `[("__tag", i64), ("__v1_0", u64), …]` — is retained).
///
/// Derived from the shipped fixture rather than checked in as a second file, so
/// the two forms cannot drift and the ONLY difference is provably that key.
/// Asserts it deleted something: on a fixture with no populated `variants` this
/// helper would otherwise silently return the input and every assertion made
/// through it would be a restatement of the populated row.
fn pre_p4(json: &str) -> String {
    let mut value: serde_json::Value =
        serde_json::from_str(json).expect("fixture MIR must parse as JSON");
    let deleted = delete_populated_variants_keys(&mut value);
    assert!(
        deleted > 0,
        "pre_p4 must actually erase a populated `variants` list, or the row it \
         produces is just the populated row under another name"
    );
    serde_json::to_string(&value).expect("re-serialize")
}

/// Delete every `Adt.variants` key, returning how many NON-EMPTY ones were hit.
fn delete_populated_variants_keys(value: &mut serde_json::Value) -> usize {
    match value {
        serde_json::Value::Object(map) => {
            let mut deleted = 0;
            if let Some(serde_json::Value::Object(adt)) = map.get_mut("Adt")
                && let Some(variants) = adt.remove("variants")
                && variants.as_array().is_some_and(|v| !v.is_empty())
            {
                deleted += 1;
            }
            for v in map.values_mut() {
                deleted += delete_populated_variants_keys(v);
            }
            deleted
        }
        serde_json::Value::Array(items) => {
            items.iter_mut().map(delete_populated_variants_keys).sum()
        }
        _ => 0,
    }
}

/// VC generation and the solver search both run on this thread; libtest's
/// default 2 MiB is not enough for the recursive `Formula` walks these rows
/// produce.
const SOLVER_STACK_BYTES: usize = 32 * 1024 * 1024;

/// Decide the SAFETY obligations of `json` with the real in-process ay.
///
/// `Unreachable` is filtered out: every `match` over an exhaustive enum emits
/// one, it is about the `otherwise` arm rather than about any payload, and it is
/// proved identically before and after this lane — keeping it would let a row
/// pass on the wrong obligation.
fn safety_verdicts(json: &str) -> Vec<(VcKind, VerificationResult)> {
    let func = load(json);
    std::thread::Builder::new()
        .stack_size(SOLVER_STACK_BYTES)
        .spawn(move || {
            let vcs: Vec<_> = trust_vcgen::generate_vcs(&func)
                .into_iter()
                .filter(|vc| !matches!(vc.kind, VcKind::Unreachable))
                .collect();
            assert!(
                !vcs.is_empty(),
                "{}: the row must emit a safety obligation; an empty set would make \
                 every assertion below vacuous",
                func.name
            );
            let router = trust_router::Router::deterministic_in_process_ay(60_000);
            let results = router.verify_all(&vcs);
            vcs.iter().map(|vc| vc.kind.clone()).zip(results.into_iter().map(|(_, r)| r)).collect()
        })
        .expect("spawn solver thread")
        .join()
        .expect("solver thread must not panic")
}

/// Every safety obligation of a row that CANNOT fault must be proved.
fn assert_all_proved(json: &str, why: &str) {
    let name = load(json).name;
    for (kind, verdict) in safety_verdicts(json) {
        assert!(
            matches!(verdict, VerificationResult::Proved { .. }),
            "{name}: {kind:?} is safe because {why}, so it must be PROVED from the payload's \
             DECLARED variant field type; got {verdict:?}"
        );
    }
}

/// The named obligation of a row that CAN fault must not be proved.
///
/// Deliberately `!is_proved` rather than `is_failed`: `Unknown`/`Timeout` are
/// also acceptable outcomes for an obligation that must not be discharged, and
/// asserting the stronger `Failed` would make the test fail for a reason that is
/// not a soundness regression.
fn assert_not_proved(json: &str, want: fn(&VcKind) -> bool, witness: &str) {
    let name = load(json).name;
    let verdicts = safety_verdicts(json);
    let matching: Vec<_> = verdicts.iter().filter(|(k, _)| want(k)).collect();
    assert!(
        !matching.is_empty(),
        "{name}: the obligation this row exists to keep refutable was not emitted at all — \
         an absent obligation is not a discharged one. Emitted: {:?}",
        verdicts.iter().map(|(k, _)| k).collect::<Vec<_>>()
    );
    for (kind, verdict) in matching {
        assert!(
            !matches!(verdict, VerificationResult::Proved { .. }),
            "{name}: {kind:?} FAULTS at {witness} — proving it is a FALSE PROOF; got {verdict:?}"
        );
    }
}

fn is_overflow(k: &VcKind) -> bool {
    matches!(k, VcKind::ArithmeticOverflow { .. })
}
fn is_bounds(k: &VcKind) -> bool {
    matches!(k, VcKind::IndexOutOfBounds)
}
fn is_divzero(k: &VcKind) -> bool {
    matches!(k, VcKind::DivisionByZero | VcKind::RemainderByZero)
}

// ---------------------------------------------------------------------------
// MUST BE PROVED — safe, and safe BECAUSE of the payload's declared width.
// Each was REFUTED at pristine HEAD.
// ---------------------------------------------------------------------------

/// `enum E { A(u8), B(u16) }`
/// `match e { E::A(x) => (x as u32) * 3, E::B(_) => 0 }`
#[test]
fn u8_payload_multiplication_is_proved() {
    assert_all_proved(
        include_str!("fixtures/enum_payload_u8_mul_mir.json"),
        "a u8 payload is at most 255, so `x as u32 * 3` is at most 765",
    );
}

/// `enum E { A(u16), B(u8) }`
/// `match e { E::A(x) => (x as u32) * 3, E::B(_) => 0 }`
#[test]
fn u16_payload_multiplication_is_proved() {
    assert_all_proved(
        include_str!("fixtures/enum_payload_u16_mul_mir.json"),
        "a u16 payload is at most 65535, so `x as u32 * 3` is at most 196605",
    );
}

/// `enum E { A(u32), B(u8) }`
/// `match e { E::A(x) => (x as u64) * 3, E::B(_) => 0 }`
#[test]
fn u32_payload_multiplication_is_proved() {
    assert_all_proved(
        include_str!("fixtures/enum_payload_u32_mul_mir.json"),
        "a u32 payload is at most u32::MAX, so `x as u64 * 3` cannot exceed u64::MAX",
    );
}

/// `enum E { A(i8), B(u16) }`
/// `match e { E::A(x) => (x as i32) * 3, E::B(_) => 0 }`
///
/// The SIGNED payload row: the fact must carry `-128 <= x`, not just an upper
/// bound, or the negative half of the product is still unbounded.
#[test]
fn i8_payload_multiplication_is_proved() {
    assert_all_proved(
        include_str!("fixtures/enum_payload_i8_mul_mir.json"),
        "an i8 payload lies in [-128, 127], so `x as i32 * 3` lies in [-384, 381]",
    );
}

/// `enum E { A(u8), B(u16), C, D(i8) }`
/// `match e { E::A(x) => (x as u32) * 3, _ => 0 }`
///
/// Four variants, only ONE of them read — the fact must be selected by the
/// `Downcast`'s variant index rather than by any whole-type property.
#[test]
fn multivariant_enum_reading_one_arm_is_proved() {
    assert_all_proved(
        include_str!("fixtures/enum_payload_multivariant_mir.json"),
        "only variant A is read and its payload is a u8, at most 255",
    );
}

/// `enum E<T> { A(T), B }` at `E<u8>`
/// `match e { E::A(x) => (x as u32) * 3, E::B => 0 }`
#[test]
fn generic_enum_at_a_concrete_width_is_proved() {
    assert_all_proved(
        include_str!("fixtures/enum_payload_generic_u8_mir.json"),
        "the monomorphised payload is a u8, at most 255",
    );
}

/// `enum E { A(u64), B(u8) }`
/// `match e { E::B(x) => (x as u32) * 3, E::A(_) => 0 }`
///
/// The payload read is `Downcast(1).Field(0)`, and variant 1's field is the
/// NARROW one while variant 0's is `u64`. A lane that resolved the field
/// against variant 0 (or against the flat slot) would leave this refuted.
#[test]
fn second_variant_payload_is_proved_from_its_own_variant() {
    assert_all_proved(
        include_str!("fixtures/enum_payload_variant1_u8_mul_mir.json"),
        "variant B's payload is a u8, at most 255, so `x as u32 * 3` is at most 765",
    );
}

/// `enum E { A(u8), B(u16) }`
/// `match e { E::A(x) => n / (x as u32 + 1), E::B(_) => 0 }`
///
/// The DIVISOR row. Note precisely what the declared type does and does not
/// buy: a `u8`'s declared range is `[0, 255]` and INCLUDES zero, so no integer
/// payload's type ever excludes a zero divisor. What the range gives here is
/// that `x as u32 + 1` cannot WRAP — the add is in `[1, 256]` — and it is the
/// add's overflow obligation that this lane moves. The zero-divisor obligation
/// on this row is proved at pristine HEAD too and is asserted only so a
/// regression in it would surface.
#[test]
fn payload_plus_one_divisor_is_proved() {
    assert_all_proved(
        include_str!("fixtures/enum_payload_divisor_plus_one_mir.json"),
        "a u8 payload is at most 255, so `x as u32 + 1` is in [1, 256] — it neither \
         overflows nor is zero",
    );
}

// ---------------------------------------------------------------------------
// MUST NOT CHANGE — rows that were already decided correctly.
// ---------------------------------------------------------------------------

/// `struct S(pub u8); (s.0 as u32) * 3`
///
/// The pre-existing datatype-field-range row: a STRUCT `Ty::Adt` has no
/// `variants`, so it keeps the flat `project_ty` step and this stays proved.
#[test]
fn struct_field_range_is_unchanged() {
    assert_all_proved(
        include_str!("fixtures/struct_field_mul_mir.json"),
        "a u8 struct field is at most 255, so `s.0 as u32 * 3` is at most 765",
    );
}

/// `enum E { A(bool), B(u16) }`
/// `match e { E::A(b) => arr[b as usize], E::B(_) => 0 }` with `arr: &[u32; 2]`
///
/// A `bool` payload has no integer width, so `resolve_field_scalar_range` returns
/// `None` for it in both the old and the new walk; the row is proved by the
/// bool lane and must stay proved.
#[test]
fn bool_payload_is_unchanged() {
    assert_all_proved(
        include_str!("fixtures/enum_payload_bool_mir.json"),
        "a bool indexes 0 or 1 and the array has 2 elements",
    );
}

/// `enum Inner { P(u8), Q } enum Outer { X(Inner), Y }`
/// `match e { Outer::X(Inner::P(x)) => (x as u32) * 3, _ => 0 }`
///
/// The NESTED payload row, and it is honest about what moved: the verdict is
/// PROVED at pristine HEAD and PROVED now. rustc materialises the
/// `Downcast(0).Field(0).Downcast(0).Field(0)` read into a bare `u8` local
/// before the cast, and `conjoin_local_type_ranges` already bounded THAT local,
/// so the verdict here never depended on the payload fact. What DID move is the
/// resolution itself, from "no bound at all" to the declared `u8` — pinned at
/// the resolution layer by `enum_payload_range_tests::nested_variant_payload_
/// resolves_through_both_downcasts`, because a verdict assertion cannot see it.
#[test]
fn nested_enum_payload_is_proved() {
    assert_all_proved(
        include_str!("fixtures/enum_payload_nested_mir.json"),
        "the innermost payload is a u8, at most 255",
    );
}

// ---------------------------------------------------------------------------
// MUST STILL REFUTE — each of these PANICS. Proving one is a FALSE PROOF.
// ---------------------------------------------------------------------------

/// `enum E { A(u8), B(u16) }`
/// `match e { E::A(x) => arr[x as usize], E::B(_) => 0 }` with `arr: &[u32; 4]`
///
/// The payload's declared range `[0, 255]` is WIDER than the array, so the
/// bound must not discharge the index check.
#[test]
fn payload_indexing_a_shorter_array_still_refutes() {
    assert_not_proved(
        include_str!("fixtures/enum_payload_short_array_mir.json"),
        is_bounds,
        "every `E::A(x)` with `x >= 4` (index out of bounds on a 4-element array)",
    );
}

/// `enum E { A(u8), B(u16) }`
/// `match e { E::A(x) => n / (x as u32), E::B(_) => 0 }`
///
/// A `u8`'s declared range CONTAINS zero, so the divisor obligation must stay
/// refutable — this is the row that keeps the divisor claim honest.
#[test]
fn payload_divisor_that_can_be_zero_still_refutes() {
    assert_not_proved(
        include_str!("fixtures/enum_payload_div_zero_mir.json"),
        is_divzero,
        "`E::A(0)` (division by zero)",
    );
}

/// `enum E { A(u8), B(u16) }`
/// `match e { E::A(x) => x + 1, E::B(_) => 0 }`
///
/// A real overflow computed from a payload: the correct `[0, 255]` bound admits
/// `x = 255`, which is exactly the witness.
#[test]
fn real_overflow_from_a_payload_still_refutes() {
    assert_not_proved(
        include_str!("fixtures/enum_payload_u8_overflow_mir.json"),
        is_overflow,
        "`E::A(255)` (u8 add overflow)",
    );
}

/// `enum E { A(i8), B(u16) }`
/// `match e { E::A(x) => 127 - x, E::B(_) => 0 }`
///
/// Faults ONLY for a NEGATIVE payload, so it pins the fact's SIGNEDNESS: an
/// `i8` payload bounded as if it were unsigned would assert `0 <= x` and delete
/// every witness this row has.
#[test]
fn signed_payload_lower_bound_still_refutes() {
    assert_not_proved(
        include_str!("fixtures/enum_payload_i8_sub_mir.json"),
        is_overflow,
        "every `E::A(x)` with `x < 0` (i8 sub overflow, e.g. `E::A(-1)` giving 128)",
    );
}

/// `enum E { A(u64), B(u16) }`
/// `match e { E::A(x) => x + 1, E::B(_) => 0 }`
///
/// THE FALSE PROOF this lane closes. At pristine HEAD `trustc` reported this
/// function `2 proved, 0 failed` with both obligations kernel-certified,
/// because the flat-slot resolution bounded the `u64` payload to `__tag`'s
/// `i64` range and thereby deleted the `u64::MAX` witness.
#[test]
fn u64_payload_overflow_still_refutes() {
    assert_not_proved(
        include_str!("fixtures/enum_payload_u64_overflow_mir.json"),
        is_overflow,
        "`E::A(u64::MAX)` (u64 add overflow)",
    );
}

/// `enum E { A(u8), B(u64) }`
/// `match e { E::B(x) => x + 1, E::A(_) => 0 }`
///
/// The same false proof reached through `Downcast(1)`, and the mutation guard
/// for the variant INDEX: resolving this field against variant 0 would bound a
/// `u64` by `u8` and prove it. Also `2 proved, 0 failed`, kernel-certified, at
/// pristine HEAD.
#[test]
fn second_variant_u64_payload_overflow_still_refutes() {
    assert_not_proved(
        include_str!("fixtures/enum_payload_variant1_u64_overflow_mir.json"),
        is_overflow,
        "`E::B(u64::MAX)` (u64 add overflow)",
    );
}

// ---------------------------------------------------------------------------
// MUST STILL REFUTE — the ORDINARY-RUST breadth of the class.
//
// Every row below reported `N proved, 0 failed`, all kernel-certified, from
// pristine `trustc` (`-Ztrust-dump=mir:` on the quoted source), and every one
// panics. The panicking input is the one the runtime oracle found first.
// ---------------------------------------------------------------------------

/// `enum E { A { z: u8, a: u64 }, B(u16) }`
/// `match e { E::A { z: _, a } => a + 1, E::B(_) => 0 }`
///
/// A STRUCT variant, and the payload is its SECOND field: the read is
/// `Downcast(0).Field(1)`, so a lane that indexed the flat union view would
/// land on `__v0_a` — or, for `Field(0)`, on `__tag`.
#[test]
fn struct_variant_payload_still_refutes() {
    assert_not_proved(
        include_str!("fixtures/enum_payload_struct_variant_u64_mir.json"),
        is_overflow,
        "`E::A { z: 7, a: u64::MAX }` (u64 add overflow)",
    );
}

/// `enum E { A { b: u64, a: u8 }, B(u16) }`
/// `match e { E::A { b, a: _ } => b + 1, E::B(_) => 0 }`
///
/// The field-ORDER control for the row above: the `u64` is now field 0 of the
/// variant, so the two rows disagree on which variant-relative index carries
/// the wide payload and a lane keyed on the index rather than on the variant
/// cannot satisfy both.
#[test]
fn struct_variant_first_field_payload_still_refutes() {
    assert_not_proved(
        include_str!("fixtures/enum_payload_field_order_u64_mir.json"),
        is_overflow,
        "`E::A { b: u64::MAX, a: 3 }` (u64 add overflow)",
    );
}

/// `enum E { A(u8, u64), B(u16) }`
/// `match e { E::A(_, y) => y + 1, E::B(_) => 0 }`
///
/// A TUPLE variant read at `.1`, where variant-relative field 1 and flat slot 1
/// are different types (`u64` vs the flat view's `__v0_0: u8`).
#[test]
fn tuple_variant_second_payload_still_refutes() {
    assert_not_proved(
        include_str!("fixtures/enum_payload_tuple_second_u64_mir.json"),
        is_overflow,
        "`E::A(9, u64::MAX)` (u64 add overflow)",
    );
}

/// `enum E { A(u64), B(u16) }`
/// `fn f(e: &E) -> u64 { match e { E::A(x) => *x + 1, E::B(_) => 0 } }`
///
/// The payload behind a REFERENCE: the place is `Deref.Downcast(0).Field(0)`,
/// so the `Downcast` is not the first projection and the walk must carry the
/// pending variant across the `Deref` step.
#[test]
fn payload_behind_a_reference_still_refutes() {
    assert_not_proved(
        include_str!("fixtures/enum_payload_by_reference_u64_mir.json"),
        is_overflow,
        "`&E::A(u64::MAX)` (u64 add overflow)",
    );
}

/// `fn f(e: Option<u64>) -> u64 { match e { Some(x) => x + 1, None => 0 } }`
///
/// THE row that sizes the blast radius: `Option<u64>` is the commonest enum in
/// Rust, its payload read is the ordinary `Downcast(1).Field(0)`, and pristine
/// `trustc` reported this `2 proved, 0 failed` with both obligations
/// kernel-certified.
#[test]
fn option_u64_payload_still_refutes() {
    assert_not_proved(
        include_str!("fixtures/enum_payload_option_u64_mir.json"),
        is_overflow,
        "`Some(u64::MAX)` (u64 add overflow)",
    );
}

/// `enum E { A(u8), B(u64), C(u8) }`
/// `match e { E::B(x) => x + 1, E::A(_) => 0, E::C(_) => 0 }`
///
/// THREE variants with the wide payload in the MIDDLE one, so neither the first
/// nor the last variant's declared type bounds the read.
#[test]
fn three_variant_middle_payload_still_refutes() {
    assert_not_proved(
        include_str!("fixtures/enum_payload_three_variants_u64_mir.json"),
        is_overflow,
        "`E::B(u64::MAX)` (u64 add overflow)",
    );
}

/// `enum E { A(u64), B(u64) }`
/// `match e { E::A(x) => x + 1, E::B(y) => y + 2 }`
///
/// BOTH variants read, so both arms carry an overflow obligation and neither may
/// be discharged. A stock-rustc runtime oracle over `E::A(v)`/`E::B(v)` for `v`
/// in `0..=255`, `2^k-1 | 2^k | 2^k+1` for `k` in `8..=63`, and the four values
/// around `i64::MAX`/`u64::MAX` faults on three of them — `A(u64::MAX)`, and `B`
/// at both `u64::MAX` and `u64::MAX - 1` — identically with and without `-O`.
#[test]
fn both_variants_read_still_refute() {
    assert_not_proved(
        include_str!("fixtures/enum_payload_both_variants_u64_mir.json"),
        is_overflow,
        "`E::A(u64::MAX)`, `E::B(u64::MAX)` and `E::B(u64::MAX - 1)` (u64 add overflow)",
    );
}

/// `enum E { A(u64), B(u16) } struct S { e: E }`
/// `match s.e { E::A(x) => x + 1, E::B(_) => 0 }`
///
/// The enum NESTED IN A STRUCT: the place is `Field(0).Downcast(0).Field(0)`, so
/// the walk takes a genuine FLAT struct step and a variant-relative step in the
/// same projection chain and must not confuse them.
#[test]
fn enum_nested_in_a_struct_still_refutes() {
    assert_not_proved(
        include_str!("fixtures/enum_payload_in_struct_u64_mir.json"),
        is_overflow,
        "`S { e: E::A(u64::MAX) }` (u64 add overflow)",
    );
}

/// `#[repr(u8)] enum E { A(u8) = 7, B(u64) = 3 }`
/// `match e { E::B(x) => x + 1, E::A(_) => 0 }`
///
/// EXPLICIT discriminants that do not match the variant INDEX (variant 1 has tag
/// 3, variant 0 has tag 7). The payload's variant must be selected by the
/// `Downcast`'s index, never by the tag the path condition fixes.
#[test]
fn repr_u8_explicit_discriminant_payload_still_refutes() {
    assert_not_proved(
        include_str!("fixtures/enum_payload_repr_u8_explicit_disc_u64_mir.json"),
        is_overflow,
        "`E::B(u64::MAX)` (u64 add overflow)",
    );
}

/// `enum E { A(u128), B(u16) }`
/// `match e { E::A(x) => x + 1, E::B(_) => 0 }`
///
/// A `u128` payload: the flat `__tag: i64` range is narrower still against this
/// one, so it deleted an even larger share of the value space.
///
/// The one row in this block whose pristine-HEAD verdict was `Proved` WITHOUT a
/// clean-kernel certificate. It is a false proof of the ay verdict either way —
/// `-Ztrust-policy=certify` would have reported it `Unknown` while the default
/// policy accepted it — and it is called out here so the "kernel-certified"
/// wording on the `u64` rows is not read as covering this one.
#[test]
fn u128_payload_still_refutes() {
    assert_not_proved(
        include_str!("fixtures/enum_payload_u128_overflow_mir.json"),
        is_overflow,
        "`E::A(u128::MAX)` (u128 add overflow)",
    );
}

/// `enum E { A(u64) }`
/// `match e { E::A(x) => x + 1 }`
///
/// A SINGLE-variant enum. rustc still emits `Downcast(0)` for it, and the flat
/// view still leads with `__tag`, so the false proof was available here too —
/// and unlike the multi-variant rows this one has no `Unreachable` obligation to
/// dilute the count: pristine `trustc` reported `1 proved, 0 failed`.
#[test]
fn single_variant_enum_payload_still_refutes() {
    assert_not_proved(
        include_str!("fixtures/enum_payload_single_variant_u64_mir.json"),
        is_overflow,
        "`E::A(u64::MAX)` (u64 add overflow)",
    );
}

// ---------------------------------------------------------------------------
// PRE-P4 SERIALIZED INPUT — the same rows with `Ty::Adt::variants` ABSENT.
//
// `variants` is `#[serde(default)]`, so this is the shape every serialized
// `Ty::Adt` older than PHASE 4 deserializes to: an EMPTY variant list beside a
// RETAINED enum-shaped flat view. A resolver that keys "is this an enum?" on
// `!variants.is_empty()` reads these as structs, falls through to the flat step
// and answers `Downcast(v).Field(0)` with `__tag: i64` — the exact wrong bound
// the variant-aware walk exists to delete. Measured on the byte-identical JSON
// with one `variants` list emptied, the whole fix silently reverted:
// `2 obligations, 2 proved`, kernel-certified.
//
// The flat view has a SECOND answer, and it is the right one: the erasure hits
// `variants` only, so the payload's declared type is still there in the
// `__v{v}_{field}` slot the same lowering loop wrote. The rows below assert the
// SAME properties as their populated twins — refutes stay refuted AND (in
// `narrow_payload_rows_keep_their_bound_when_variants_are_absent`) proofs stay
// proved. They are not a second copy of the same test: a build whose enum test
// is `!variants.is_empty()` passes the populated rows and fails these, and a
// build that recovers the tag instead of the payload fails them in the other
// direction.
// ---------------------------------------------------------------------------

/// `Option<u64>` again, deserialized WITHOUT a `variants` key.
#[test]
fn option_u64_payload_still_refutes_with_variants_absent() {
    assert_not_proved(
        &pre_p4(include_str!("fixtures/enum_payload_option_u64_mir.json")),
        is_overflow,
        "`Some(u64::MAX)` (u64 add overflow)",
    );
}

/// `enum E { A(u64) }` again, deserialized WITHOUT a `variants` key.
#[test]
fn single_variant_payload_still_refutes_with_variants_absent() {
    assert_not_proved(
        &pre_p4(include_str!("fixtures/enum_payload_single_variant_u64_mir.json")),
        is_overflow,
        "`E::A(u64::MAX)` (u64 add overflow)",
    );
}

/// The base's two false-proof rows, deserialized WITHOUT a `variants` key.
#[test]
fn base_u64_payload_rows_still_refute_with_variants_absent() {
    assert_not_proved(
        &pre_p4(include_str!("fixtures/enum_payload_u64_overflow_mir.json")),
        is_overflow,
        "`E::A(u64::MAX)` (u64 add overflow)",
    );
    assert_not_proved(
        &pre_p4(include_str!("fixtures/enum_payload_variant1_u64_overflow_mir.json")),
        is_overflow,
        "`E::B(u64::MAX)` (u64 add overflow)",
    );
}

/// The pre-P4 shape keeps its PRECISION, and the two halves together are what
/// show the recovered bound is the payload's and not the tag's.
///
/// Erasing `variants` does not erase the declared payload type: the same
/// `lower_enum_adt` loop wrote it into the flat view as `__v{v}_{field}`, and
/// that half is not `#[serde(default)]`. So the narrow-payload rows stay PROVED
/// on the erased shape — while `base_u64_payload_rows_still_refute_with_variants_
/// absent` above shows the `u64` rows on the SAME erased shape stay REFUTED.
///
/// No single answer for `Downcast(v).Field(0)` can produce both outcomes except
/// the payload's own declared type. The `__tag: i64` answer proves the `u64`
/// rows (its range has no value above `i64::MAX`, deleting the witness) and
/// refutes the narrow ones (`x as u32 * 3` overflows somewhere in `i64`'s
/// range); no answer at all refutes both halves. That pair of assertions is the
/// discrimination this file rests on — neither half alone distinguishes the tag
/// from the payload.
#[test]
fn narrow_payload_rows_keep_their_bound_when_variants_are_absent() {
    for json in [
        include_str!("fixtures/enum_payload_u8_mul_mir.json"),
        include_str!("fixtures/enum_payload_u16_mul_mir.json"),
        include_str!("fixtures/enum_payload_u32_mul_mir.json"),
        include_str!("fixtures/enum_payload_i8_mul_mir.json"),
    ] {
        let erased = pre_p4(json);
        assert_all_proved(
            &erased,
            "the payload's declared width survives the `variants` erasure in the flat \
             view's `__v{v}_*` slot, which is also the slot `place_ty` types this place \
             with",
        );
    }
}

// ---------------------------------------------------------------------------
// THE CORPUS ROW THIS LANE ACTUALLY MOVES, AND WHAT IT COSTS.
// ---------------------------------------------------------------------------

/// A LIVE pre-P4 `Option<u64>` in the clean-kernel corpus, and the two clean-
/// kernel certificates this lane withdraws.
///
/// `crates/trust-clean/fixtures/census-m6-cleankernel-2026-07-08/`
/// `extract-foldmemo-dump/expr__types__BigNat__mul_big_capped.json` is real
/// extracted MIR from before PHASE 4: its `Option<u64>` locals carry the flat
/// view `[("__tag", i64), ("__v1_0", u64)]` and NO `variants` list. Two of its
/// `?`-desugar payload reads are `Downcast(1).Field(0)`, and at pristine HEAD
/// `project_ty` answered both with `__tag: i64` — so the emitted range fact said
/// a `u64` payload lies in `[i64::MIN, i64::MAX]`. That is the false-proof
/// direction (it deletes every witness above `i64::MAX`), and it is the same
/// misresolution `u64_payload_overflow_still_refutes` closes on a synthetic row;
/// this row shows it was not synthetic.
///
/// THE COST, stated because it is a build error on the lane that owns this
/// fixture: two `ArithmeticOverflow { op: Add, (u64, u64) }` obligations here are
/// ay-`Proved` before and after, but at pristine HEAD they were ALSO clean-kernel
/// certified and now are not. Under `-Ztrust-policy=certify` an ay `Proved` the
/// kernel does not certify is reported `Unknown`, so code of this shape on the
/// clean-kernel lane now needs a real bound.
///
/// That certificate was NOT lost to a missing fact — this lane supplies the
/// payload's declared `u64` range in the tag's place, and the certificate does
/// not come back. It rested on the tag bound itself: the two obligations'
/// formulas before and after are character-identical apart from the two literals
/// of that one conjunct, so `i64::MAX` as an upper bound on the payload is what
/// the kernel-checkable derivation used. It is a hypothesis the declared
/// `Option<u64>` never licensed, and withdrawing a certificate that rests on it
/// is this lane working, not a regression in it.
#[test]
fn pre_p4_option_u64_in_the_clean_kernel_corpus_is_bounded_by_the_payload() {
    let json = include_str!(
        "../../trust-clean/fixtures/census-m6-cleankernel-2026-07-08/extract-foldmemo-dump/\
         expr__types__BigNat__mul_big_capped.json"
    );
    let func = load(json);
    let adts: Vec<_> = func
        .body
        .locals
        .iter()
        .filter_map(|decl| match &decl.ty {
            trust_types::Ty::Adt { fields, variants, .. } if variants.is_empty() => {
                Some(fields.iter().map(|(name, _)| name.as_str()).collect::<Vec<_>>().join(","))
            }
            _ => None,
        })
        .collect();
    assert!(
        adts.contains(&"__tag,__v1_0".to_string()),
        "the fixture must still be the pre-P4 wire shape this test is about — an \
         enum-shaped flat view with NO variants list. Found: {adts:?}"
    );

    // The payload's own declared width, and specifically NOT the tag's signed one.
    let saw_payload_bound = std::thread::Builder::new()
        .stack_size(SOLVER_STACK_BYTES)
        .spawn(move || {
            let payload = "18446744073709551615";
            let tag = "9223372036854775807";
            let mut saw_payload_bound = false;
            for vc in trust_vcgen::generate_vcs(&func) {
                let rendered = format!("{:?}", vc.formula);
                for var in ["_19@1.0", "_28@1.0"] {
                    let signed = format!("Le(Var(\"{var}\", Int), Int({tag}))");
                    let unsigned = format!("Le(Var(\"{var}\", Int), Int({payload}))");
                    assert!(
                        !rendered.contains(&signed),
                        "{var} is an `Option<u64>` payload read through \
                         `Downcast(1).Field(0)`; bounding it by the `__tag: i64` slot \
                         excludes every value above i64::MAX and deletes the overflow \
                         witness"
                    );
                    saw_payload_bound |= rendered.contains(&unsigned);
                }
            }
            saw_payload_bound
        })
        .expect("spawn vcgen thread")
        .join()
        .expect("vcgen thread must not panic");
    assert!(
        saw_payload_bound,
        "and the declared `u64` range must actually be emitted for one of them — an \
         absent fact would pass the negative assertion above vacuously"
    );
}

/// The corpus row where the wrong bound was DISCHARGING an obligation: a
/// kernel-certified false proof in `crates/trust-clean/fixtures`.
///
/// `fold-crate-lambda-calculus-3.5.0/parser___convert_classic_tokens.json`
/// contains `Option<usize>` (`[("__tag", i64), ("__v1_0", u64)]`, `variants`
/// POPULATED — so this row is closed by the variant-aware walk itself, not by
/// the pre-P4 recovery above). The `Some(index)` payload flows into `index + 1`,
/// and the obligation's own facts are `index == _47@1.0` and the violation
/// `index + 1 > u64::MAX`. At pristine HEAD the path ALSO carried
/// `_47@1.0 <= i64::MAX` from the `__tag` slot, which makes the violation
/// unsatisfiable — so `trustc` reported the row `Proved` AND clean-kernel
/// certified it, for a `usize` payload that its declared type permits to be
/// `usize::MAX`.
///
/// The consequence runs the other way from `pre_p4_option_u64_…` above and is
/// the same kind of disclosure: this fixture had TWO proved obligations and now
/// has one. That is a discharge withdrawn from a shipped corpus function, not a
/// certificate lost to a completeness gap — the hypothesis it rested on is false
/// of the program. Whether `index` can actually reach `usize::MAX` at runtime is
/// a reachability question the verifier does not answer here; what it may not do
/// is assume the payload away.
#[test]
fn the_wrong_tag_bound_was_discharging_a_corpus_obligation() {
    let json = include_str!(
        "../../trust-clean/fixtures/fold-crate-lambda-calculus-3.5.0/\
         parser___convert_classic_tokens.json"
    );
    let func = load(json);
    let decided = std::thread::Builder::new()
        .stack_size(SOLVER_STACK_BYTES)
        .spawn(move || {
            let vcs = trust_vcgen::generate_vcs(&func);
            let router = trust_router::Router::deterministic_in_process_ay(60_000);
            let results = router.verify_all(&vcs);
            vcs.iter()
                .zip(results)
                .filter(|(vc, _)| {
                    is_overflow(&vc.kind) && format!("{:?}", vc.formula).contains("_47@1.0")
                })
                .map(|(vc, (_, verdict))| (format!("{:?}", vc.formula), verdict))
                .collect::<Vec<_>>()
        })
        .expect("spawn solver thread")
        .join()
        .expect("solver thread must not panic");
    assert_eq!(
        decided.len(),
        1,
        "the fixture must still contain exactly the one overflow obligation over the \
         `Option<usize>` payload that this test is about; an absent row would make the \
         assertion below vacuous"
    );
    let (formula, verdict) = &decided[0];
    assert!(
        !formula.contains("Le(Var(\"_47@1.0\", Int), Int(9223372036854775807))"),
        "the `__tag: i64` upper bound on the payload is the hypothesis that discharged \
         this row at pristine HEAD; it may not come back"
    );
    assert!(
        formula.contains("Le(Var(\"_47@1.0\", Int), Int(18446744073709551615))"),
        "and the payload's own declared `usize` range must be there instead — an absent \
         fact would pass the assertion above vacuously"
    );
    assert!(
        !matches!(verdict, VerificationResult::Proved { .. }),
        "`index + 1` on a payload the declared type allows to be `usize::MAX` must not \
         be discharged; got {verdict:?}"
    );
}
