//! Real-MIR end-to-end cover for the UNINHABITED MATCH ARM false REFUTATION, on MIR
//! extracted with `-Ztrust-dump=mir:<dir>` (equivalently `mir-only:<dir>`) from the
//! four source programs below — not a hand-built approximation of the lowering.
//!
//! THE DEFECT, measured at HEAD on this exact fixture:
//!
//!     pub fn void_003(r: Result<u8, Infallible>) -> u8 {
//!         match r { Ok(v) => v, Err(e) => match e {} }
//!     }
//!     [unreach] FAILED (ay-in-process); counterexample: _2 = 1, __trust_mir__discr_r = 0
//!
//! `Infallible` has no inhabitants, so the `Err` arm is dead by construction and the
//! program is CORRECT — the verifier ACCUSED it and failed the build. The declared tag
//! set `{0, 1}` is what made the `Unreachable` block's path condition `_2 != 0`
//! satisfiable; filtering the dead variant out pins `_2 == 0` and refutes it.
//!
//! The lowering itself corroborates the fact rather than merely tolerating it: for
//! `enum E3 { A(u8), B(Infallible), C(u8) }`, rustc's own `SwitchInt` targets are
//! `[(0, ..), (2, ..)]` — it never emits an edge for the uninhabited `B`. The
//! verifier's tag set was the only place tag 1 still existed.
//!
//! THREE OF THE FOUR FIXTURES ARE THE ADVERSARIAL DIRECTION, and they are the reason
//! this file exists: dropping a tag STRENGTHENS a globally published premise, so an
//! over-eager filter is a FALSE PROOF. Each of the three is MUTATION-CHECKED — the
//! assertion named below FAILS when `inhabited_enum_variant_tag_set` is mutated to
//! `.filter(|(v, _)| v.discriminant == 0)`, i.e. to drop LIVE tags:
//!
//!  * `dead_and_live_panic` keeps the REACHABLE `unreachable!()` of a LIVE sibling
//!    variant refuted AT ITS LIVE-TAG WITNESS;
//!  * `live_arm_oob` keeps BOTH out-of-range array reads refuted, each at ITS OWN
//!    live tag;
//!  * `all_dead_source` keeps the two real `+` overflows of a body whose scrutinee
//!    enum is WHOLLY uninhabited refuted — the end-to-end form of the caller's
//!    fail-closed `tags.is_empty()` guard, which it also kills when removed.
//!
//! MUTATION LEDGER. This file previously carried a canary captioned "proving it
//! would be a FALSE PROOF" that NO behaviour of `inhabited_enum_variant_tag_set`
//! could falsify — including one that deletes every live tag (see
//! `live_variant_arms_keep_their_out_of_bounds_reads_refuted` for why, and for the
//! join-linkage gap that made it inert). Shape-tightening does not detect that;
//! only mutation does. Each mutant below was applied and BUILT AND RUN; the tests
//! named go red:
//!
//!     NO-OP           return the declared set    err_arm_is_proved, live_sibling_*,
//!                                                live_variant_arms_*
//!     KEEP-TAG-0      `.filter(discriminant      live_sibling_*, live_variant_arms_*,
//!                     == 0)`, deleting LIVE tags wholly_uninhabited_scrutinee_*
//!     INVERTED        keep only the DEAD         err_arm_is_proved, live_sibling_*,
//!                     variants                   live_variant_arms_*
//!     EMPTY-SET GUARD publish the empty          wholly_uninhabited_scrutinee_*
//!     REMOVED         membership (`false`)
//!     TYPE WIDENED    `[T; 0]` uninhabited,      (unit only: zero_length_array_*,
//!                     unions read as products,    union_payload_declines,
//!                     `adt_kind: None` as enum    un_migrated_adt_kind_declines)
//!     DATATYPE        a by-name `Ty::Datatype`   (unit only: datatype_positional_*)
//!     FILTERED        filtered too
//!     DEPTH FAILS     budget exhaustion answers  (unit only: deep_nesting_fails_closed)
//!     OPEN            "uninhabited"
//!
//! The bare count assertions here are vacuity guards, not adversarial ones: no
//! mutant kills them, and their job is to stop the assertions after them from
//! iterating over an empty list.
use trust_types::{CounterexampleValue, VcKind, VerifiableFunction, VerificationResult};

#[path = "support/test_router.rs"]
mod test_router;

fn load(json: &str) -> VerifiableFunction {
    serde_json::from_str(json).expect("fixture MIR must deserialize")
}

fn router() -> trust_router::Router {
    test_router::deterministic_test_router()
}

/// Every generated VC of `func`, paired with its verdict from the SAME in-process ay
/// backend the compiler's analysis seams use.
fn rows(func: &VerifiableFunction) -> Vec<(VcKind, VerificationResult)> {
    let r = router();
    trust_vcgen::generate_vcs(func)
        .into_iter()
        .map(|vc| (vc.kind.clone(), r.verify_one(&vc)))
        .collect()
}

fn unreachable_rows(func: &VerifiableFunction) -> Vec<VerificationResult> {
    rows(func)
        .into_iter()
        .filter(|(kind, _)| matches!(kind, VcKind::Unreachable))
        .map(|(_, result)| result)
        .collect()
}

fn is_failed(result: &VerificationResult) -> bool {
    matches!(result, VerificationResult::Failed { .. })
}

/// Whether `result` is a refutation whose witness assigns `name` (SSA-version suffix
/// stripped) the integer `value`. Pinning the VALUE, not just the verdict, is what
/// makes a "still refuted" assertion say something: a refutation that moved to a
/// different tag is a different claim about the program.
fn refuted_at(result: &VerificationResult, name: &str, value: i128) -> bool {
    let VerificationResult::Failed { counterexample: Some(ce), .. } = result else {
        return false;
    };
    ce.assignments.iter().any(|(n, v)| {
        n.split('#').next() == Some(name) && matches!(v, CounterexampleValue::Int(x) if *x == value)
    })
}

/// `match r { Ok(v) => v, Err(e) => match e {} }` over `Result<u8, Infallible>`.
/// The `Unreachable` arm must be PROVED — and must KERNEL-CERTIFY. `certify_vc`
/// returning `Some` is the `ResultProofAuthority::KernelCertified` evidence, one of
/// the authorities the compiler's `is_static_proof_for` accepts as a static
/// discharge; a bare solver `Proved` carrying NO authority falls through to the
/// `runtime_checked`/`unknown` buckets instead. Pinning it is what separates "the
/// solver returned UNSAT" from "the obligation is discharged".
#[test]
fn uninhabited_err_arm_is_proved_unreachable() {
    let func = load(include_str!("fixtures/uninhabited_void_003_mir.json"));
    let vcs = trust_vcgen::generate_vcs(&func);
    let r = router();
    let mut unreachable_seen = 0;
    for vc in &vcs {
        if !matches!(vc.kind, VcKind::Unreachable) {
            continue;
        }
        unreachable_seen += 1;
        let result = r.verify_one(vc);
        assert!(
            matches!(result, VerificationResult::Proved { .. }),
            "the uninhabited `Err` arm's Unreachable block must be UNSAT — a model here is \
             the FALSE REFUTATION of correct Rust; got {result:?}\nformula: {:?}",
            vc.formula
        );
        assert!(
            trust_certify::certify_vc(vc).is_some(),
            "the proof must kernel-certify; a `Proved` with no proof authority is counted \
             runtime-checked, not discharged\nformula: {:?}",
            vc.formula
        );
    }
    assert_eq!(unreachable_seen, 1, "the fixture has exactly one Unreachable block");
}

/// ADVERSARIAL. `enum E3 { A(u8), B(Infallible), C(u8) }` with
///
/// ```ignore
/// match e { E3::A(v) => v, E3::B(_) => 0, E3::C(_) => unreachable!() }
/// ```
///
/// `B` is dead so tag 1 is correctly dropped, but `C` is LIVE: the `unreachable!()` arm
/// is genuinely reachable at tag 2. Proving it away would be a FALSE PROOF. The fixture
/// carries both directions as two separate rows, and this test pins BOTH:
///
///  * the switch's `otherwise` edge is an `Unreachable` block rustc reaches only at a
///    phantom tag. MEASURED: refuted at HEAD with `_2 = 1` — the DEAD tag — and PROVED
///    (and kernel-certified) with the filter.
///  * the `unreachable!()` lowers to `core::panicking::panic("…entered unreachable
///    code")`, which `v2_is_unreachable_sentinel_panic` turns into a panic-family
///    `Assertion`. MEASURED: refuted at `_2 = 2` — the LIVE tag — BOTH at HEAD and with
///    the filter, witness byte-identical. MUTATION-CHECKED: dropping the live tags makes
///    that row `Proved` and this assertion fires.
///
/// WHY THE `panic!` SPELLING AND NOT `unreachable_unchecked`. MEASURED on the
/// `match e { E3::A(v) => v, _ => unsafe { unreachable_unchecked() } }` fixture this test
/// used to load: it emits exactly TWO rows, `Unreachable` and
/// `Assertion { message: "[unsafe] missing SAFETY comment on unsafe block" }`. The
/// `unreachable_unchecked` call (a `Terminator::Call` with `target: null`) gets NO
/// undefined-behavior obligation at all; the only `Assertion` is that LINT row, `Failed`
/// with an EMPTY counterexample, byte-identical at HEAD and with the filter. A test that
/// counted refuted `Assertion` rows there would have passed even if the filter WRONGLY
/// DROPPED THE LIVE TAG — it guarded nothing. Hence: pin the KIND, the VERDICT and the
/// WITNESS VALUE, on a row that is a real obligation.
#[test]
fn a_live_sibling_variant_keeps_its_reachable_panic_refuted() {
    let func = load(include_str!("fixtures/uninhabited_dead_and_live_panic_mir.json"));
    let vcs = trust_vcgen::generate_vcs(&func);
    let r = router();
    let all: Vec<_> = vcs.iter().map(|vc| (vc, r.verify_one(vc))).collect();

    let unreachable: Vec<_> =
        all.iter().filter(|(vc, _)| matches!(vc.kind, VcKind::Unreachable)).collect();
    assert_eq!(unreachable.len(), 1, "the fixture has exactly one Unreachable block");
    assert!(
        matches!(unreachable[0].1, VerificationResult::Proved { .. }),
        "the phantom-tag Unreachable must be proved; got {:?}",
        unreachable[0].1
    );
    assert!(
        trust_certify::certify_vc(unreachable[0].0).is_some(),
        "the proof must kernel-certify; a `Proved` with no proof authority is counted \
         runtime-checked, not discharged"
    );

    let panics: Vec<_> = all
        .iter()
        .filter(|(vc, _)| {
            matches!(&vc.kind, VcKind::Assertion { message } if message.contains("panic call"))
        })
        .collect();
    assert_eq!(
        panics.len(),
        1,
        "the reachable `unreachable!()` must produce exactly one panic-call Assertion row — \
         without it the witness check below would be vacuous: {:?}",
        all.iter().map(|(vc, _)| &vc.kind).collect::<Vec<_>>()
    );
    assert!(
        refuted_at(&panics[0].1, "_2", 2),
        "the REACHABLE `unreachable!()` (variant `C`) must stay refuted AT THE LIVE TAG \
         `_2 = 2`; proving it — or refuting it at some other tag — would mean the filter \
         deleted a tag a value can actually take: {:?}",
        panics[0].1
    );
}

/// ADVERSARIAL, the false-proof canary. `enum Idx { A(u8), B(Infallible), C(u8), D(u8),
/// E(u8) }` indexed into `[u8; 3]`, with the index read PER ARM:
///
/// ```ignore
/// match x {
///     Idx::A(i) => a[(i & 1) as usize],   // in range — Proved
///     Idx::B(_) => 0,                     // dead: rustc emits no switch edge for it
///     Idx::C(i) => a[(i & 1) as usize],   // in range — Proved
///     Idx::D(i) => a[i as usize],         // LIVE tag 3, out of range — MUST refute
///     Idx::E(i) => a[i as usize],         // LIVE tag 4, out of range — MUST refute
/// }
/// ```
///
/// Tag 1 is dead and correctly dropped; tags 3 and 4 are LIVE, and each guards its OWN
/// block, so each unguarded read carries the path condition `_3 == 3` / `_3 == 4` over
/// the discriminant destination `_3`. MUTATION-CHECKED: with
/// `inhabited_enum_variant_tag_set` mutated to `.filter(|(v, _)| v.discriminant == 0)`
/// the published membership contradicts both path conditions, both rows flip to
/// `Proved` (kernel-certified!), and the `refuted.len() == 2` assertion below fires.
///
/// WHY PER-ARM AND NOT `let d = match x { .. }; a[d]`, which is the shape this test
/// first shipped with. MEASURED on that fixture: its single `[bounds]` row is refuted at
/// `__trust_mir__discr_x = 0, d = 3` — discriminant `A`, whose arm assigns `d = 0`, yet
/// `d = 3`. The four-way join never ties `d` to its per-path constant, so the refutation
/// never consults the tag set at all and the row stays `Failed` under EVERY behaviour of
/// the filter, including one that deletes every live tag. That is a real gap in the join
/// linkage and a separate lane's fix; here it is only the reason the canary must not be
/// written over a joined index. Shape-tightening a vacuous assertion does not make it
/// fire — only a mutant can tell you that.
#[test]
fn live_variant_arms_keep_their_out_of_bounds_reads_refuted() {
    let func = load(include_str!("fixtures/uninhabited_live_arm_oob_mir.json"));
    let all = rows(&func);
    let bounds: Vec<_> = all
        .iter()
        .filter(|(kind, _)| matches!(kind, VcKind::IndexOutOfBounds | VcKind::SliceBoundsCheck))
        .collect();
    assert_eq!(bounds.len(), 4, "the fixture indexes the array once per live arm: {all:?}");
    let refuted: Vec<_> = bounds.iter().filter(|(_, result)| is_failed(result)).collect();
    assert_eq!(
        refuted.len(),
        2,
        "exactly the two UNMASKED reads — the `D`/`E` arms, whose tags are LIVE and whose \
         index is out of range — must stay refuted; proving either is a FALSE PROOF of \
         real UB: {bounds:?}"
    );
    for tag in [3, 4] {
        assert!(
            refuted.iter().any(|(_, result)| refuted_at(result, "_3", tag)),
            "one surviving refutation must put the discriminant `_3` at the LIVE tag {tag}; \
             a refutation that moved off it is a different claim about the program: \
             {refuted:?}"
        );
    }
    // The dead variant's own arm is still discharged, so the fix is doing its job here too.
    // The count is asserted first on purpose: `all` over an EMPTY list is vacuously true,
    // so without it a fixture that stopped emitting an Unreachable row would pass silently.
    let unreach = unreachable_rows(&func);
    assert_eq!(unreach.len(), 1, "the fixture has exactly one Unreachable block: {unreach:?}");
    assert!(
        unreach.iter().all(|result| matches!(result, VerificationResult::Proved { .. })),
        "the uninhabited variant's Unreachable arm must be proved in the same body: {unreach:?}"
    );
}

/// ADVERSARIAL, and the end-to-end form of the caller's fail-closed empty-set guard.
/// `enum AllDead { A(Infallible), B(Infallible) }` matched in a body that also does two
/// real `u8` additions. EVERY variant is uninhabited, so the filter empties the tag set
/// and `build_discriminant_variant_range_facts` must publish NO fact: these facts are
/// GLOBAL to the function, and the empty membership is the unsatisfiable `false`, which
/// would discharge every other obligation in the body at a stroke.
///
/// MUTATION-CHECKED, and this is the assertion that makes the guard testable end to end
/// rather than only at unit granularity: with the caller's `if tags.is_empty() { continue }`
/// removed, both `+` rows flip from `Failed` to `Proved` — two real overflows proved away
/// by a premise about a place the body never reads. The over-eager tag filter kills it
/// too.
#[test]
fn a_wholly_uninhabited_scrutinee_keeps_the_body_s_own_obligations_refuted() {
    let func = load(include_str!("fixtures/uninhabited_all_dead_source_mir.json"));
    let all = rows(&func);
    let adds: Vec<_> =
        all.iter().filter(|(kind, _)| matches!(kind, VcKind::ArithmeticOverflow { .. })).collect();
    assert_eq!(adds.len(), 2, "the body has exactly two `u8` additions: {all:?}");
    for (kind, result) in &adds {
        assert!(
            is_failed(result),
            "`k + 1` / `k + 2` genuinely overflow at `k = u8::MAX`; proving one because the \
             SCRUTINEE is uninhabited would be a false proof from an unsatisfiable global \
             premise: {kind:?} => {result:?}"
        );
    }
}
