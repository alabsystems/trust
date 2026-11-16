//! REAL-ARTIFACT lane test: the body relation for a postcondition over a SHIFT.
//!
//! # The defect
//!
//! There are TWO emitters of a body shift in this crate and they do not spell
//! the shift COUNT the same way.
//!
//! * `contracts::rust_shift_amount_formula` emits the masked count
//!   `BvAnd(IntToBv(k, w), w - 1, w)`.
//! * `chc::try_binop_to_formula` emits the whole shift as
//!   `BvToInt(BvShl(IntToBv(lhs, w), IntToBv(rhs, w), w), w, signed)` — count
//!   UNMASKED. That is the spelling a real body's `_3 = Shl(_4, const 1)` block
//!   definition arrives in.
//!
//! `contracts::machine_faithful_shift_amount` authenticates only the first, so
//! the declared-width translator refused a body definition this same crate had
//! written. MEASURED before the fix, on the REAL extracted MIR of
//! `ay-proof-common`'s `Literal::positive` (`Literal(var.0 << 1)`):
//!
//! ```text
//! unverifiable source specification (machine-arithmetic ensures conjoined body
//!   facts outside the declared-width fragment)
//! blocking conjunct:
//!   Eq(_3, BvToInt(BvShl(IntToBv(_4, 32), IntToBv(1, 32), 32), 32, false))
//! ```
//!
//! while the byte-equivalent `Literal(var.0 * 2)` body proved. Two spellings of
//! one `u32` operation, one of them unreadable.
//!
//! # What the fix admits, and only that
//!
//! An unmasked count is accepted when the mask is provably the IDENTITY on it:
//! an integer literal `k` with `0 <= k < width`. Every supported Rust integer
//! width is a power of two, so `k & (width - 1) == k` there, and the translation
//! emitted is byte-identical to the authenticated spelling's. A count `>= width`,
//! a negative literal, and every SYMBOLIC count still decline in that UNMASKED
//! spelling.
//!
//! # 2026-10-03: the CHC emitter masks every count
//!
//! The unmasked spelling was not only unreadable, it was WRONG for a count
//! `>= width`: a plain MIR `Shl` (no overflow `Assert`) shifts by
//! `count.rem_euclid(width)`, while the unmasked `bvshl` yields `0`.
//! `chc::try_binop_to_formula` now emits the masked count, so the out-of-range
//! and symbolic rewrites below no longer decline: they are read with Rust's
//! semantics, the false clause is REFUTED, and the clause Rust's value makes
//! true is PROVED. Before, these two tests asserted that no obligation was
//! produced at all, on the premise that Rust has no value for a count of 32 —
//! true of `ShlUnchecked` and of a shift behind rustc's `Overflow(Shl)` assert,
//! false of the plain `Shl` these rewrites build (`tests/plain_shift_count_mask.rs`
//! pins the same semantics on hand-built checks-off bodies).

use trust_types::{VcKind, VerifiableFunction, VerificationResult};

#[path = "support/test_router.rs"]
mod test_router;

const FIXTURES: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/fixtures/");

fn load(name: &str) -> VerifiableFunction {
    let text = std::fs::read_to_string(format!("{FIXTURES}{name}.json"))
        .unwrap_or_else(|e| panic!("fixture `{name}` must be readable: {e}"));
    serde_json::from_str(&text).unwrap_or_else(|e| panic!("fixture `{name}` must deserialize: {e}"))
}

fn posts(func: &VerifiableFunction) -> Vec<trust_types::VerificationCondition> {
    trust_vcgen::generate_vcs(func)
        .into_iter()
        .filter(|vc| matches!(vc.kind, VcKind::Postcondition))
        .collect()
}

fn refusals(func: &VerifiableFunction) -> Vec<String> {
    trust_vcgen::generate_vcs(func)
        .into_iter()
        .filter_map(|vc| match vc.kind {
            VcKind::UnsupportedMir { kind, detail } if kind == "SpecUnverifiable" => Some(detail),
            _ => None,
        })
        .collect()
}

/// Some obligation is REFUTED (a solver counterexample), and none is proved.
fn refuted(vcs: &[trust_types::VerificationCondition]) -> bool {
    let router = test_router::deterministic_test_router();
    let outcomes: Vec<_> = vcs
        .iter()
        .map(|vc| router.verify_all(std::slice::from_ref(vc)).into_iter().next().unwrap().1)
        .collect();
    outcomes.iter().any(|r| matches!(r, VerificationResult::Failed { .. }))
        && !outcomes.iter().any(|r| matches!(r, VerificationResult::Proved { .. }))
}

fn proved(vcs: &[trust_types::VerificationCondition]) -> bool {
    let router = test_router::deterministic_test_router();
    !vcs.is_empty()
        && vcs.iter().all(|vc| {
            matches!(
                router.verify_all(std::slice::from_ref(vc)).into_iter().next().unwrap().1,
                VerificationResult::Proved { .. }
            )
        })
}

/// A CONSTANT-count shift in the body is readable in the declared-width lane.
/// `ensures ret.0 == var.0 * 2` over `Literal(var.0 << 1)`: the clause
/// multiplies, the body shifts, and in `u32` those are the same function — so
/// this is a statement about the code and not the code restated.
#[test]
fn constant_count_shift_body_is_readable_in_the_declared_width_lane() {
    let func = load("ay_literal_positive_shl");
    let vcs = posts(&func);
    assert!(
        !vcs.is_empty(),
        "the shift body must not fall closed at translation; refusals: {:?}",
        refusals(&func)
    );
    assert!(proved(&vcs), "`ret.0 == var.0 * 2` over `Literal(var.0 << 1)` must be discharged");
}

/// The refutation direction must survive: a shift body whose postcondition is
/// FALSE has to stay refuted, not become provable because the count now reads.
#[test]
fn a_false_postcondition_over_a_shift_body_is_still_refuted() {
    let func = load("ay_literal_positive_mutant");
    let vcs = posts(&func);
    assert!(!vcs.is_empty(), "the mutant must produce a real obligation");
    let router = test_router::deterministic_test_router();
    let outcomes: Vec<_> = vcs
        .iter()
        .map(|vc| router.verify_all(std::slice::from_ref(vc)).into_iter().next().unwrap().1)
        .collect();
    assert!(
        outcomes.iter().any(|r| matches!(r, VerificationResult::Failed { .. })),
        "`ret.0 == var.0 * 2 + 1` over `Literal(var.0 << 1)` must be REFUTED; got {outcomes:?}"
    );
}

/// An OUT-OF-RANGE count is the case where the mask is NOT the identity.
/// Rewriting the fixture's PLAIN `Shl` count to `32` at width 32 gives the
/// shift Rust's value `var.0 << (32 & 31) == var.0` — the fixture's own
/// `Overflow(Shl)` assert guards the ORIGINAL count, not the rewritten one. The
/// false `ret.0 == var.0 * 2` must be refuted (never wrapped into a proof), and
/// `ret.0 == var.0` must prove.
#[test]
fn an_out_of_range_constant_count_takes_rusts_mask() {
    let mut func = load("ay_literal_positive_shl");
    let mut rewritten = false;
    for block in &mut func.body.blocks {
        for stmt in &mut block.stmts {
            if let trust_types::Statement::Assign {
                rvalue: trust_types::Rvalue::BinaryOp(trust_types::BinOp::Shl, _, rhs),
                ..
            } = stmt
            {
                *rhs = trust_types::Operand::Constant(trust_types::ConstValue::Int(32));
                rewritten = true;
            }
        }
    }
    assert!(rewritten, "fixture must contain a `Shl` whose count can be rewritten");
    let vcs = posts(&func);
    assert!(!vcs.is_empty(), "the masked count must be readable; refusals: {:?}", refusals(&func));
    assert!(
        refuted(&vcs),
        "`ret.0 == var.0 * 2` over `var.0 << 32` (Rust: `var.0 << 0`) must be REFUTED"
    );

    // `ret.0 == var.0 * 1` rather than `ret.0 == var.0`: a clause with machine
    // arithmetic is the one the declared-width lane reads, where `var.0` is a
    // 32-bit value. The arithmetic-free spelling goes to the Int-sorted lane, which
    // carries no range for the parameter's field and refutes it at
    // `var.0 = 2^32 + 1` for a reason that has nothing to do with shifts. All three
    // carriers of the fixture's `ensures` are replaced, so no stale `* 2` clause
    // rides along.
    set_ensures_times(&mut func, 1);
    assert!(
        proved(&posts(&func)),
        "`ret.0 == var.0 * 1` over `var.0 << 32` is Rust's masked value and must be discharged"
    );
}

/// Replace every carrier of the fixture's one `ensures` — the lowered contract,
/// the source text and the parsed formula — with `result.0 == var.0 * k`.
fn set_ensures_times(func: &mut VerifiableFunction, k: i128) {
    use trust_types::{Formula, Sort};
    func.contracts[0].body =
        format!("__trust_lowered_compiler_contract__:(result.0) == ((var.0) * ({k}))");
    func.spec.ensures = vec![format!("(result.0) == ((var.0) * ({k}))")];
    func.postconditions = vec![Formula::Eq(
        Box::new(Formula::Var("_0.0".into(), Sort::Int)),
        Box::new(Formula::Mul(
            Box::new(Formula::Var("var.0".into(), Sort::Int)),
            Box::new(Formula::Int(k)),
        )),
    )];
}

/// A SYMBOLIC count is now emitted MASKED, so it is read with Rust's semantics
/// instead of declining. Same fixture, count replaced by the parameter's own
/// field: `var.0 << (var.0 & 31)` is not `var.0 * 2` (at `var.0 == 2` it is 8),
/// so the clause must be refuted — never proved.
#[test]
fn a_symbolic_count_is_masked_and_a_false_clause_refuted() {
    let mut func = load("ay_literal_positive_shl");
    let mut rewritten = false;
    for block in &mut func.body.blocks {
        for stmt in &mut block.stmts {
            if let trust_types::Statement::Assign {
                rvalue: trust_types::Rvalue::BinaryOp(trust_types::BinOp::Shl, _, rhs),
                ..
            } = stmt
            {
                *rhs = trust_types::Operand::Copy(trust_types::Place {
                    local: 1,
                    projections: vec![trust_types::Projection::Field(0)],
                });
                rewritten = true;
            }
        }
    }
    assert!(rewritten, "fixture must contain a `Shl` whose count can be rewritten");
    let vcs = posts(&func);
    assert!(!vcs.is_empty(), "the masked count must be readable; refusals: {:?}", refusals(&func));
    assert!(
        refuted(&vcs),
        "`ret.0 == var.0 * 2` over `var.0 << var.0` must be REFUTED, never proved"
    );
}

/// The pair of constructor discriminators on ay's REAL bodies, and their
/// coherence check. Each is true of every literal its constructor can return
/// and false as a logical statement about a free `result.0`; each is the OTHER
/// constructor's exact relation negated, so a lane that proved both against one
/// body would be incoherent.
#[test]
fn ay_constructor_discriminators_prove_and_do_not_collide() {
    for name in ["ay_literal_positive_discriminator", "ay_literal_negative_discriminator"] {
        let func = load(name);
        let vcs = posts(&func);
        assert!(!vcs.is_empty(), "{name}: no obligation; refusals {:?}", refusals(&func));
        assert!(proved(&vcs), "{name}: must be discharged");
    }

    // `positive`'s body must NOT satisfy `negative`'s discriminator. Same real
    // MIR as `ay_literal_positive_shl`, clause swapped to the one true only of
    // the ODD encoding.
    let mut crossed = load("ay_literal_positive_shl");
    crossed.contracts[0].body =
        "__trust_lowered_compiler_contract__:(result.0) != ((var.0) * (2))".to_string();
    assert!(
        !proved(&posts(&crossed)),
        "`positive`'s body must not satisfy `negative`'s discriminator"
    );
}
