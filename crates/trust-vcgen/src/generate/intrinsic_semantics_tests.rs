// The soundness net for `intrinsic_semantics`.
//
// That module is the only place in this crate that ADDS facts to the hypothesis
// set, so a wrong definition there is not an incompleteness — it is a FALSE
// PROOF. These tests are therefore differential against the REAL Rust operation
// and EXHAUSTIVE at width 8 (all 256 inputs, both signednesses), not
// shape assertions over the emitted term.
//
// The evaluator below is deliberately GENERIC SMT-LIB: it knows `int2bv`,
// `extract`, `concat` and `bv2int` and nothing whatsoever about intrinsics. A
// definition that reverses the wrong way, uses the wrong bit index, reads the
// wrong signedness or is off by one in the width therefore FAILS here — the
// evaluator has no matching mistake to make. `evaluator_agrees_with_smtlib_by_hand`
// pins the evaluator itself to hand-computed SMT-LIB values first, so the two
// halves of the differential cannot drift together.

use trust_types::{
    BasicBlock, BlockId, Formula, LocalDecl, Operand, Place, Sort, SourceSpan, Terminator, Ty,
    UnwindEdge, VerifiableBody, VerifiableFunction,
};

use super::intrinsic_semantics::{
    ValueModeledIntrinsic, bitreverse_bits, bswap_bits, classify_value_modeled_intrinsic,
    ctpop_value, marked_saturating_intrinsic, value_modeled_intrinsic_facts,
};
use super::{saturating_add_sub_method, saturating_call_dest_value};

const MARK: &str = trust_types::TRUST_RUSTC_INTRINSIC_PATH_PREFIX;

// ---------------------------------------------------------------------------
// A generic, intrinsic-blind SMT-LIB evaluator for the emitted fragment.
// ---------------------------------------------------------------------------

/// A concrete value of one of the two sorts the definitions use.
#[derive(Clone, Copy, Debug, PartialEq)]
enum V {
    /// Mathematical integer (SMT `Int`).
    Int(i128),
    /// Bitvector: `val` is the unsigned reading, already masked to `width`.
    Bv {
        val: u128,
        width: u32,
    },
    Bool(bool),
}

impl V {
    fn int(self) -> i128 {
        match self {
            V::Int(i) => i,
            other => panic!("expected Int, got {other:?}"),
        }
    }
    fn bv(self) -> (u128, u32) {
        match self {
            V::Bv { val, width } => (val, width),
            other => panic!("expected BitVec, got {other:?}"),
        }
    }
    fn boolean(self) -> bool {
        match self {
            V::Bool(b) => b,
            other => panic!("expected Bool, got {other:?}"),
        }
    }
}

fn mask(width: u32) -> u128 {
    if width >= 128 { u128::MAX } else { (1u128 << width) - 1 }
}

/// Evaluate `f` under `env` using textbook SMT-LIB semantics.
///
/// * `((_ int2bv w) t)` is `t mod 2^w` — for a negative `t` that is the
///   two's-complement pattern, which is the whole reason the definitions can be
///   stated once for both signednesses.
/// * `((_ extract i j) x)` takes bits `i..=j` with bit 0 the LSB.
/// * `(concat a b)` places `a` in the HIGH bits.
/// * `bv2int` is unsigned; the signed reading subtracts `2^w` when the top bit
///   is set.
fn eval(f: &Formula, env: &[(&str, i128)]) -> V {
    match f {
        Formula::Var(name, sort) => {
            let v = env
                .iter()
                .find(|(n, _)| *n == name.as_str())
                .unwrap_or_else(|| panic!("unbound variable {name}"))
                .1;
            assert_eq!(*sort, Sort::Int, "the definitions only bind Int-sorted variables");
            V::Int(v)
        }
        Formula::Int(i) => V::Int(*i),
        Formula::Bool(b) => V::Bool(*b),
        Formula::Add(a, b) => V::Int(eval(a, env).int() + eval(b, env).int()),
        Formula::Sub(a, b) => V::Int(eval(a, env).int() - eval(b, env).int()),
        Formula::IntToBv(a, w) => {
            let x = eval(a, env).int();
            // `x mod 2^w`, mathematical (non-negative) remainder.
            let m = 1i128.checked_shl(*w).expect("test widths stay under 127");
            let r = ((x % m) + m) % m;
            V::Bv { val: r as u128, width: *w }
        }
        Formula::BvExtract { inner, high, low } => {
            let (val, width) = eval(inner, env).bv();
            assert!(high >= low && *high < width, "extract out of range");
            let w = high - low + 1;
            V::Bv { val: (val >> low) & mask(w), width: w }
        }
        Formula::BvConcat(a, b) => {
            let (hi, hw) = eval(a, env).bv();
            let (lo, lw) = eval(b, env).bv();
            V::Bv { val: (hi << lw) | lo, width: hw + lw }
        }
        Formula::BvToInt(a, w, signed) => {
            let (val, width) = eval(a, env).bv();
            assert_eq!(width, *w, "declared BvToInt width must match the term's width");
            if *signed && width < 128 && (val >> (width - 1)) & 1 == 1 {
                V::Int(val as i128 - (1i128 << width))
            } else {
                V::Int(val as i128)
            }
        }
        Formula::Eq(a, b) => V::Bool(eval(a, env) == eval(b, env)),
        Formula::Ge(a, b) => V::Bool(eval(a, env).int() >= eval(b, env).int()),
        Formula::Le(a, b) => V::Bool(eval(a, env).int() <= eval(b, env).int()),
        Formula::Gt(a, b) => V::Bool(eval(a, env).int() > eval(b, env).int()),
        Formula::Lt(a, b) => V::Bool(eval(a, env).int() < eval(b, env).int()),
        Formula::Implies(a, b) => V::Bool(!eval(a, env).boolean() || eval(b, env).boolean()),
        Formula::And(xs) => V::Bool(xs.iter().all(|x| eval(x, env).boolean())),
        Formula::Or(xs) => V::Bool(xs.iter().any(|x| eval(x, env).boolean())),
        Formula::Not(x) => V::Bool(!eval(x, env).boolean()),
        Formula::Ite(c, t, e) => {
            if eval(c, env).boolean() {
                eval(t, env)
            } else {
                eval(e, env)
            }
        }
        other => panic!("the emitted fragment must not contain {other:?}"),
    }
}

fn x_var() -> Formula {
    Formula::Var("x".into(), Sort::Int)
}

/// The evaluator is the other half of every differential below, so pin IT to
/// hand-computed SMT-LIB values before trusting a single comparison.
#[test]
fn evaluator_agrees_with_smtlib_by_hand() {
    let bv = |f: &Formula| eval(f, &[("x", 0)]).bv();
    // ((_ int2bv 8) (- 1)) = #xFF   — the two's-complement bridge.
    assert_eq!(bv(&Formula::IntToBv(Box::new(Formula::Int(-1)), 8)), (0xFF, 8));
    // ((_ int2bv 8) 300) = #x2C     — reduction mod 2^8.
    assert_eq!(bv(&Formula::IntToBv(Box::new(Formula::Int(300)), 8)), (0x2C, 8));
    // ((_ extract 3 0) #xAB) = #xB  — bit 0 is the LSB.
    assert_eq!(
        bv(&Formula::BvExtract {
            inner: Box::new(Formula::IntToBv(Box::new(Formula::Int(0xAB)), 8)),
            high: 3,
            low: 0,
        }),
        (0xB, 4)
    );
    // ((_ extract 7 4) #xAB) = #xA
    assert_eq!(
        bv(&Formula::BvExtract {
            inner: Box::new(Formula::IntToBv(Box::new(Formula::Int(0xAB)), 8)),
            high: 7,
            low: 4,
        }),
        (0xA, 4)
    );
    // (concat #xAA #x01) = #xAA01   — the FIRST argument is the HIGH half.
    assert_eq!(
        bv(&Formula::BvConcat(
            Box::new(Formula::IntToBv(Box::new(Formula::Int(0xAA)), 8)),
            Box::new(Formula::IntToBv(Box::new(Formula::Int(0x01)), 8)),
        )),
        (0xAA01, 16)
    );
    // bv2int / bv2int_signed of #xFF.
    let ff = || Box::new(Formula::IntToBv(Box::new(Formula::Int(255)), 8));
    assert_eq!(eval(&Formula::BvToInt(ff(), 8, false), &[]).int(), 255);
    assert_eq!(eval(&Formula::BvToInt(ff(), 8, true), &[]).int(), -1);
}

// ---------------------------------------------------------------------------
// EXHAUSTIVE width-8 differentials against the real Rust operations.
// ---------------------------------------------------------------------------

/// Every `u8` bit pattern, presented both as the unsigned Int the model sees for
/// a `u8` local and as the signed Int it sees for an `i8` local.
fn all_width8_inputs() -> impl Iterator<Item = (u8, i128, i128)> {
    (0u16..=255).map(|v| (v as u8, i128::from(v as u8), i128::from(v as u8 as i8)))
}

#[test]
fn ctpop_exhaustive_width8_matches_rust() {
    let def = ctpop_value(&x_var(), 8);
    let mut checked = 0;
    for (byte, unsigned_x, signed_x) in all_width8_inputs() {
        let expected = i128::from(byte.count_ones());
        assert_eq!(eval(&def, &[("x", unsigned_x)]).int(), expected, "ctpop(u8 {byte:#04x})");
        // The SAME definition must hold when the local is `i8` and the Int lane
        // therefore carries a negative value: population count is a function of
        // the bit pattern, and `int2bv` recovers it.
        assert_eq!(eval(&def, &[("x", signed_x)]).int(), expected, "ctpop(i8 {})", byte as i8);
        checked += 1;
    }
    assert_eq!(checked, 256, "all 256 width-8 inputs must be checked");
}

#[test]
fn bswap_width8_is_the_identity_not_a_reversal() {
    // THE TRAP: `u8::swap_bytes` is the identity. A definition that "reverses"
    // unconditionally passes every wider width and fails only here.
    let def = Formula::BvToInt(Box::new(bswap_bits(&x_var(), 8).expect("width 8")), 8, false);
    for (byte, unsigned_x, _) in all_width8_inputs() {
        assert_eq!(
            eval(&def, &[("x", unsigned_x)]).int(),
            i128::from(byte.swap_bytes()),
            "bswap(u8 {byte:#04x}) must be the identity"
        );
        assert_eq!(eval(&def, &[("x", unsigned_x)]).int(), i128::from(byte));
    }
}

#[test]
fn bswap_exhaustive_width16_matches_rust() {
    let unsigned =
        Formula::BvToInt(Box::new(bswap_bits(&x_var(), 16).expect("width 16")), 16, false);
    let signed = Formula::BvToInt(Box::new(bswap_bits(&x_var(), 16).expect("width 16")), 16, true);
    for v in 0u32..=0xFFFF {
        let u = v as u16;
        assert_eq!(
            eval(&unsigned, &[("x", i128::from(u))]).int(),
            i128::from(u.swap_bytes()),
            "bswap(u16 {u:#06x})"
        );
        let s = u as i16;
        assert_eq!(
            eval(&signed, &[("x", i128::from(s))]).int(),
            i128::from(s.swap_bytes()),
            "bswap(i16 {s})"
        );
    }
}

#[test]
fn bswap_width32_and_width64_match_rust_on_asymmetric_patterns() {
    // A byte-order mistake is invisible on a palindrome, so every case here has
    // four/eight DISTINCT bytes.
    let d32 = Formula::BvToInt(Box::new(bswap_bits(&x_var(), 32).expect("width 32")), 32, false);
    for v in [0x0102_0304u32, 0xDEAD_BEEF, 0x0000_00FF, 0xFF00_0000, u32::MAX, 0, 1] {
        assert_eq!(
            eval(&d32, &[("x", i128::from(v))]).int(),
            i128::from(v.swap_bytes()),
            "bswap(u32 {v:#010x})"
        );
    }
    // The literal the falsification fixture checks: 0x01020304 -> 0x04030201.
    assert_eq!(eval(&d32, &[("x", 0x0102_0304)]).int(), 0x0403_0201);
    let d64 = Formula::BvToInt(Box::new(bswap_bits(&x_var(), 64).expect("width 64")), 64, false);
    for v in [0x0102_0304_0506_0708u64, 0xDEAD_BEEF_CAFE_F00D, u64::MAX, 0, 1] {
        assert_eq!(
            eval(&d64, &[("x", i128::from(v))]).int(),
            i128::from(v.swap_bytes()),
            "bswap(u64 {v:#018x})"
        );
    }
}

#[test]
fn bitreverse_exhaustive_width8_matches_rust() {
    let unsigned = Formula::BvToInt(Box::new(bitreverse_bits(&x_var(), 8)), 8, false);
    let signed = Formula::BvToInt(Box::new(bitreverse_bits(&x_var(), 8)), 8, true);
    for (byte, unsigned_x, signed_x) in all_width8_inputs() {
        assert_eq!(
            eval(&unsigned, &[("x", unsigned_x)]).int(),
            i128::from(byte.reverse_bits()),
            "bitreverse(u8 {byte:#04x})"
        );
        assert_eq!(
            eval(&signed, &[("x", signed_x)]).int(),
            i128::from((byte as i8).reverse_bits()),
            "bitreverse(i8 {})",
            byte as i8
        );
    }
    // The edge that separates bitreverse from bswap at this width.
    assert_eq!(eval(&unsigned, &[("x", 1)]).int(), 128);
}

#[test]
fn bitreverse_width32_and_width64_match_rust() {
    let d32 = Formula::BvToInt(Box::new(bitreverse_bits(&x_var(), 32)), 32, false);
    for v in [1u32, 0x8000_0000, 0x0102_0304, 0xDEAD_BEEF, u32::MAX, 0] {
        assert_eq!(
            eval(&d32, &[("x", i128::from(v))]).int(),
            i128::from(v.reverse_bits()),
            "bitreverse(u32 {v:#010x})"
        );
    }
    let d64 = Formula::BvToInt(Box::new(bitreverse_bits(&x_var(), 64)), 64, false);
    for v in [1u64, 0x8000_0000_0000_0000, 0x0102_0304_0506_0708, u64::MAX, 0] {
        assert_eq!(
            eval(&d64, &[("x", i128::from(v))]).int(),
            i128::from(v.reverse_bits()),
            "bitreverse(u64 {v:#018x})"
        );
    }
}

#[test]
fn bswap_and_bitreverse_are_not_the_same_definition() {
    // Guards against a copy-paste that would make one of the two silently wrong
    // at every width above 8 while both exhaustive tests still passed on the
    // (symmetric) cases they share.
    let bs = Formula::BvToInt(Box::new(bswap_bits(&x_var(), 16).expect("16")), 16, false);
    let br = Formula::BvToInt(Box::new(bitreverse_bits(&x_var(), 16)), 16, false);
    assert_ne!(eval(&bs, &[("x", 1)]).int(), eval(&br, &[("x", 1)]).int());
    assert_eq!(eval(&bs, &[("x", 1)]).int(), 256);
    assert_eq!(eval(&br, &[("x", 1)]).int(), 0x8000);
}

// ---------------------------------------------------------------------------
// The PRODUCTION path: every emitted fact must be TRUE of the real result, and
// must not be vacuous.
// ---------------------------------------------------------------------------

/// `fn f(x: T) -> R { _2 = <callee>(copy x) }` — one call, one successor.
fn intrinsic_fn(arg_ty: Ty, dest_ty: Ty, callee: &str) -> VerifiableFunction {
    VerifiableFunction {
        name: "f".into(),
        def_path: "f".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: Some("_0".into()) },
                LocalDecl { index: 1, ty: arg_ty, name: Some("x".into()) },
                LocalDecl { index: 2, ty: dest_ty, name: Some("r".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        func: callee.into(),
                        args: vec![Operand::Copy(Place::local(1))],
                        dest: Place::local(2),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                        is_unsafe_sig: false,
                        callee_identity: None,
                        is_foreign: false,
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: Ty::Unit,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

fn u8_fn(name: &str, dest_ty: Ty) -> VerifiableFunction {
    intrinsic_fn(
        Ty::Int { width: 8, signed: false },
        dest_ty,
        &format!("{MARK}core::intrinsics::{name}::<u8>"),
    )
}

fn i8_fn(name: &str, dest_ty: Ty) -> VerifiableFunction {
    intrinsic_fn(
        Ty::Int { width: 8, signed: true },
        dest_ty,
        &format!("{MARK}core::intrinsics::{name}::<i8>"),
    )
}

fn facts_of(func: &VerifiableFunction) -> Vec<Formula> {
    let subject = Formula::Var("r".into(), Sort::Int);
    let (dest, facts) =
        value_modeled_intrinsic_facts(func, &func.body.blocks[0].terminator, &subject)
            .expect("the fixture is a recognized value-modeled intrinsic call");
    assert_eq!(dest.local, 2);
    facts
}

/// The soundness property, stated directly: with the destination bound to the
/// value the REAL Rust operation returns, every emitted fact must evaluate TRUE.
/// A definition that is wrong for even one of the 256 inputs fails here.
///
/// The companion property — that the facts are not vacuous — is checked by
/// `..._facts_reject_a_wrong_result`.
fn assert_facts_true_for_all_width8(
    func: &VerifiableFunction,
    real: impl Fn(u8) -> i128,
    signed_arg: bool,
) {
    let facts = facts_of(func);
    assert!(!facts.is_empty());
    for (byte, unsigned_x, signed_x) in all_width8_inputs() {
        let x = if signed_arg { signed_x } else { unsigned_x };
        let env = [("x", x), ("r", real(byte))];
        for fact in &facts {
            assert!(
                eval(fact, &env).boolean(),
                "fact false for input {byte:#04x} (x = {x}, r = {}): {fact:?}",
                real(byte)
            );
        }
    }
}

/// The facts must PIN the result: for every input there must be a wrong value
/// of `r` that some fact refutes. Without this a definition could be trivially
/// true (e.g. `0 <= r` alone) and the test above would still pass.
fn assert_facts_reject(
    func: &VerifiableFunction,
    real: impl Fn(u8) -> i128,
    wrong: impl Fn(i128) -> i128,
    signed_arg: bool,
) {
    let facts = facts_of(func);
    for (byte, unsigned_x, signed_x) in all_width8_inputs() {
        let x = if signed_arg { signed_x } else { unsigned_x };
        let bad = wrong(real(byte));
        let env = [("x", x), ("r", bad)];
        assert!(
            facts.iter().any(|f| !eval(f, &env).boolean()),
            "no fact rejects the WRONG result {bad} for input {byte:#04x} — the model is vacuous"
        );
    }
}

#[test]
fn ctpop_facts_are_true_and_exact_for_every_width8_input() {
    let u32_dest = Ty::Int { width: 32, signed: false };
    assert_facts_true_for_all_width8(
        &u8_fn("ctpop", u32_dest.clone()),
        |b| i128::from(b.count_ones()),
        false,
    );
    assert_facts_true_for_all_width8(
        &i8_fn("ctpop", u32_dest.clone()),
        |b| i128::from((b as i8).count_ones()),
        true,
    );
    assert_facts_reject(
        &u8_fn("ctpop", u32_dest.clone()),
        |b| i128::from(b.count_ones()),
        |r| r + 1,
        false,
    );
    assert_facts_reject(
        &u8_fn("ctpop", u32_dest),
        |b| i128::from(b.count_ones()),
        |r| r - 1,
        false,
    );
}

#[test]
fn bswap_facts_are_true_and_exact_for_every_width8_input() {
    let u8_ty = Ty::Int { width: 8, signed: false };
    let i8_ty = Ty::Int { width: 8, signed: true };
    assert_facts_true_for_all_width8(
        &u8_fn("bswap", u8_ty.clone()),
        |b| i128::from(b.swap_bytes()),
        false,
    );
    assert_facts_true_for_all_width8(
        &i8_fn("bswap", i8_ty),
        |b| i128::from((b as i8).swap_bytes()),
        true,
    );
    assert_facts_reject(&u8_fn("bswap", u8_ty), |b| i128::from(b.swap_bytes()), |r| r + 1, false);
}

#[test]
fn bitreverse_facts_are_true_and_exact_for_every_width8_input() {
    let u8_ty = Ty::Int { width: 8, signed: false };
    let i8_ty = Ty::Int { width: 8, signed: true };
    assert_facts_true_for_all_width8(
        &u8_fn("bitreverse", u8_ty.clone()),
        |b| i128::from(b.reverse_bits()),
        false,
    );
    assert_facts_true_for_all_width8(
        &i8_fn("bitreverse", i8_ty),
        |b| i128::from((b as i8).reverse_bits()),
        true,
    );
    assert_facts_reject(
        &u8_fn("bitreverse", u8_ty),
        |b| i128::from(b.reverse_bits()),
        |r| r + 1,
        false,
    );
}

#[test]
fn ctlz_and_cttz_facts_are_true_for_every_width8_input_including_zero() {
    let u32_dest = Ty::Int { width: 32, signed: false };
    // THE EDGE CASE: `ctlz(0) == 8` and `cttz(0) == 8`, NOT 0. Rust's
    // `leading_zeros`/`trailing_zeros` agree, and the `_nonzero` intrinsics —
    // which are UB at zero — are excluded from the model entirely.
    assert_eq!(0u8.leading_zeros(), 8);
    assert_eq!(0u8.trailing_zeros(), 8);
    assert_facts_true_for_all_width8(
        &u8_fn("ctlz", u32_dest.clone()),
        |b| i128::from(b.leading_zeros()),
        false,
    );
    assert_facts_true_for_all_width8(
        &u8_fn("cttz", u32_dest.clone()),
        |b| i128::from(b.trailing_zeros()),
        false,
    );
    assert_facts_true_for_all_width8(
        &i8_fn("ctlz", u32_dest.clone()),
        |b| i128::from((b as i8).leading_zeros()),
        true,
    );
    assert_facts_true_for_all_width8(
        &i8_fn("cttz", u32_dest.clone()),
        |b| i128::from((b as i8).trailing_zeros()),
        true,
    );

    // The bound is deliberately NOT exact here (see the module header), so the
    // vacuity check is the specific one the facts DO decide: `r == W` forces
    // `x == 0`, and a nonzero `x` therefore cannot have `W` leading zeros.
    let facts = facts_of(&u8_fn("ctlz", u32_dest.clone()));
    for (byte, unsigned_x, _) in all_width8_inputs() {
        let env = [("x", unsigned_x), ("r", 8)];
        let all_true = facts.iter().all(|f| eval(f, &env).boolean());
        assert_eq!(
            all_true,
            byte == 0,
            "`ctlz == 8` must be consistent with x == 0 and refuted otherwise (x = {byte:#04x})"
        );
        // The range bound must refute anything outside [0, 8].
        for bad in [-1i128, 9, 4_294_967_295] {
            let env = [("x", unsigned_x), ("r", bad)];
            assert!(
                facts.iter().any(|f| !eval(f, &env).boolean()),
                "ctlz result {bad} is outside [0, 8] and must be refuted"
            );
        }
    }
}

// ---------------------------------------------------------------------------
// Recognizer strictness. The model asserts a VALUE, so any path a user crate can
// spell must decline.
// ---------------------------------------------------------------------------

#[test]
fn marked_intrinsic_recognizer_accepts_the_measured_stage2_spelling() {
    // Exactly what `-Ztrust-dump=mir:` emitted for `core::intrinsics::ctpop(x)`
    // on the stage2 compiler, and the truncated `intrinsics::<name>` form the
    // corpora dumps carry.
    for (path, want) in [
        ("core::intrinsics::ctpop::<u32>", ValueModeledIntrinsic::Ctpop),
        ("std::intrinsics::ctlz::<u64>", ValueModeledIntrinsic::Ctlz),
        ("intrinsics::cttz::<u8>", ValueModeledIntrinsic::Cttz),
        ("core::intrinsics::bswap::<i16>", ValueModeledIntrinsic::Bswap),
        ("core::intrinsics::bitreverse::<usize>", ValueModeledIntrinsic::Bitreverse),
    ] {
        assert_eq!(
            classify_value_modeled_intrinsic(&format!("{MARK}{path}")),
            Some(want),
            "{path} must classify"
        );
    }
}

#[test]
fn marked_intrinsic_recognizer_fails_closed() {
    let decline = |p: &str| {
        assert_eq!(classify_value_modeled_intrinsic(p), None, "{p} must decline");
        assert_eq!(marked_saturating_intrinsic(p), None, "{p} must decline");
    };
    // UNMARKED — a user crate can write `core::intrinsics::ctpop` as a module
    // path, so without the compiler-stamped marker the value model is refused.
    decline("core::intrinsics::ctpop::<u32>");
    decline("intrinsics::ctpop");
    // Forged crate root / extra segments after the marker.
    decline(&format!("{MARK}evil::intrinsics::ctpop::<u32>"));
    decline(&format!("{MARK}a::b::intrinsics::ctpop"));
    decline(&format!("{MARK}core::intrinsics::ctpop::extra"));
    decline(&format!("{MARK}core::notintrinsics::ctpop"));
    decline(&format!("{MARK}ctpop"));
    // A user function whose crate happens to be named `core` cannot reach this
    // lane at all, because the marker is stamped by `TyCtxt`, not by spelling.
    decline("mycrate::intrinsics::ctpop");
}

#[test]
fn marked_intrinsic_recognizer_excludes_partial_siblings() {
    // `ctlz_nonzero`/`cttz_nonzero` are `unsafe` and UB at zero: they carry a
    // PRECONDITION a caller can violate, so they must be proved, never modeled.
    // Conflating them with the total forms would license `ctlz(0) == 0`.
    for name in ["ctlz_nonzero", "cttz_nonzero", "unchecked_add", "unchecked_shl", "transmute"] {
        assert_eq!(
            classify_value_modeled_intrinsic(&format!("{MARK}core::intrinsics::{name}::<u32>")),
            None,
            "{name} is partial or unmodeled and must decline"
        );
    }
}

#[test]
fn saturating_intrinsic_lane_admits_add_and_sub_but_never_mul() {
    assert_eq!(
        marked_saturating_intrinsic(&format!("{MARK}core::intrinsics::saturating_add::<u32>")),
        Some("saturating_add")
    );
    assert_eq!(
        marked_saturating_intrinsic(&format!("{MARK}std::intrinsics::saturating_sub::<i64>")),
        Some("saturating_sub")
    );
    // `library/core/src/intrinsics/mod.rs` declares NO `saturating_mul`
    // intrinsic. A marked path spelling one is a misextraction or a forgery.
    assert_eq!(
        marked_saturating_intrinsic(&format!("{MARK}core::intrinsics::saturating_mul::<u32>")),
        None
    );
    // The METHOD recognizer still accepts all three, and now also routes the
    // intrinsic spelling to the SAME clamp construction.
    assert_eq!(
        saturating_add_sub_method("core::num::<impl u32>::saturating_mul"),
        Some("saturating_mul")
    );
    assert_eq!(
        saturating_add_sub_method(&format!("{MARK}core::intrinsics::saturating_add::<u32>")),
        Some("saturating_add")
    );
    assert_eq!(saturating_add_sub_method("mycrate::saturating_add"), None);
}

/// The saturating INTRINSIC spelling must reach the same exact clamp value the
/// METHOD spelling already had — checked exhaustively over all 65 536 `u8` pairs
/// and all 65 536 `i8` pairs, so the saturation boundary is verified at both
/// ends and for both signednesses.
#[test]
fn saturating_intrinsic_clamp_exhaustive_width8_matches_rust() {
    for (signed, add) in [(false, true), (false, false), (true, true), (true, false)] {
        let name = if add { "saturating_add" } else { "saturating_sub" };
        let ty = Ty::Int { width: 8, signed };
        let func = VerifiableFunction {
            name: "f".into(),
            def_path: "f".into(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::Unit, name: Some("_0".into()) },
                    LocalDecl { index: 1, ty: ty.clone(), name: Some("a".into()) },
                    LocalDecl { index: 2, ty: ty.clone(), name: Some("b".into()) },
                    LocalDecl { index: 3, ty: ty.clone(), name: Some("r".into()) },
                ],
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![],
                        terminator: Terminator::Call {
                            unwind: UnwindEdge::Unreachable,
                            func: format!("{MARK}core::intrinsics::{name}::<x8>"),
                            args: vec![
                                Operand::Copy(Place::local(1)),
                                Operand::Copy(Place::local(2)),
                            ],
                            dest: Place::local(3),
                            target: Some(BlockId(1)),
                            span: SourceSpan::default(),
                            atomic: None,
                            is_unsafe_sig: false,
                            callee_identity: None,
                            is_foreign: false,
                        },
                    },
                    BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
                ],
                arg_count: 2,
                return_ty: Ty::Unit,
                datatype_defs: Default::default(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };
        let (dest, value) = saturating_call_dest_value(&func, &func.body.blocks[0].terminator)
            .expect("the marked saturating intrinsic must reach the clamp model");
        assert_eq!(dest.local, 3);
        for lhs in 0u16..=255 {
            for rhs in 0u16..=255 {
                let (a, b, expected) = if signed {
                    let (a, b) = (lhs as u8 as i8, rhs as u8 as i8);
                    let e = if add { a.saturating_add(b) } else { a.saturating_sub(b) };
                    (i128::from(a), i128::from(b), i128::from(e))
                } else {
                    let (a, b) = (lhs as u8, rhs as u8);
                    let e = if add { a.saturating_add(b) } else { a.saturating_sub(b) };
                    (i128::from(a), i128::from(b), i128::from(e))
                };
                assert_eq!(
                    eval(&value, &[("a", a), ("b", b)]).int(),
                    expected,
                    "{name} signed={signed} a={a} b={b}"
                );
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Gates and cost.
// ---------------------------------------------------------------------------

#[test]
fn a_non_integer_argument_is_not_modeled() {
    // The intrinsics are declared `<T: Copy>`, so only the TYPE pins the model to
    // an integer. A float / pointer / ADT argument must leave the dest havoc'd.
    let func = intrinsic_fn(
        Ty::Float { width: 32 },
        Ty::Int { width: 32, signed: false },
        &format!("{MARK}core::intrinsics::ctpop::<f32>"),
    );
    let subject = Formula::Var("r".into(), Sort::Int);
    assert!(
        value_modeled_intrinsic_facts(&func, &func.body.blocks[0].terminator, &subject).is_none()
    );
}

#[test]
fn a_reassigned_destination_or_argument_is_not_modeled() {
    use trust_types::{Rvalue, Statement};
    // Destination written twice: the fact would be stale at one of the two uses.
    let mut func = u8_fn("ctpop", Ty::Int { width: 32, signed: false });
    func.body.blocks[1].stmts.push(Statement::Assign {
        place: Place::local(2),
        rvalue: Rvalue::Use(Operand::Constant(trust_types::ConstValue::Uint(7, 32))),
        span: SourceSpan::default(),
    });
    let subject = Formula::Var("r".into(), Sort::Int);
    assert!(
        value_modeled_intrinsic_facts(&func, &func.body.blocks[0].terminator, &subject).is_none()
    );

    // Argument mutably borrowed: `let p = &mut x; *p = other;` rewrites `x`
    // without a visible def of `x`, so every fact naming `x` would go stale.
    let mut func = u8_fn("ctpop", Ty::Int { width: 32, signed: false });
    func.body.blocks[1].stmts.push(Statement::Assign {
        place: Place::local(0),
        rvalue: Rvalue::Ref { mutable: true, place: Place::local(1) },
        span: SourceSpan::default(),
    });
    assert!(
        value_modeled_intrinsic_facts(&func, &func.body.blocks[0].terminator, &subject).is_none()
    );
}

#[test]
fn above_the_width_cap_the_exact_expansion_is_declined_and_only_the_bound_remains() {
    let subject = Formula::Var("r".into(), Sort::Int);
    // 64 and 128 are both above `MAX_EXACT_INTRINSIC_WIDTH` (32 — see its doc for
    // the measured refutation cost that set it). `ctpop` keeps its `[0, W]`
    // range, which is what still makes `x.count_ones() <= 64` provable, and drops
    // the exact expansion.
    for width in [64u32, 128] {
        let func = intrinsic_fn(
            Ty::Int { width, signed: false },
            Ty::Int { width: 32, signed: false },
            &format!("{MARK}core::intrinsics::ctpop::<u{width}>"),
        );
        let (_, facts) =
            value_modeled_intrinsic_facts(&func, &func.body.blocks[0].terminator, &subject)
                .unwrap();
        assert_eq!(facts.len(), 2, "range only at width {width}: {facts:?}");
        assert!(facts.iter().all(|f| matches!(f, Formula::Ge(..) | Formula::Le(..))));

        // `bswap`/`bitreverse` have no bound to fall back on — every value of `T`
        // is a possible result — so they emit NOTHING rather than a partial claim.
        for name in ["bswap", "bitreverse"] {
            let func = intrinsic_fn(
                Ty::Int { width, signed: false },
                Ty::Int { width, signed: false },
                &format!("{MARK}core::intrinsics::{name}::<u{width}>"),
            );
            assert!(
                value_modeled_intrinsic_facts(&func, &func.body.blocks[0].terminator, &subject)
                    .is_none(),
                "{name} must decline above the width cap at width {width}"
            );
        }
    }
    // …and at 32 the exact expansion IS emitted (range + definition).
    let func = intrinsic_fn(
        Ty::Int { width: 32, signed: false },
        Ty::Int { width: 32, signed: false },
        &format!("{MARK}core::intrinsics::ctpop::<u32>"),
    );
    let (_, facts) =
        value_modeled_intrinsic_facts(&func, &func.body.blocks[0].terminator, &subject).unwrap();
    assert_eq!(facts.len(), 3, "range + exact definition at width 32: {facts:?}");
}

/// Pins the term-count table in the module header, so a future "optimization"
/// that silently multiplies the emitted term size shows up as a failing row
/// rather than as a solver timeout in someone else's crate.
#[test]
fn emitted_term_counts_match_the_documented_cost_table() {
    fn nodes(f: &Formula) -> usize {
        match f {
            Formula::Add(a, b) | Formula::BvConcat(a, b) => 1 + nodes(a) + nodes(b),
            Formula::IntToBv(a, _) | Formula::BvToInt(a, _, _) => 1 + nodes(a),
            Formula::BvExtract { inner, .. } => 1 + nodes(inner),
            _ => 1,
        }
    }
    fn depth(f: &Formula) -> usize {
        match f {
            Formula::Add(a, b) | Formula::BvConcat(a, b) => 1 + depth(a).max(depth(b)),
            Formula::IntToBv(a, _) | Formula::BvToInt(a, _, _) => 1 + depth(a),
            Formula::BvExtract { inner, .. } => 1 + depth(inner),
            _ => 1,
        }
    }
    // DEPTH is the load-bearing column: a left-nested fold made these terms `W`
    // deep and overflowed a 2 MiB stack in the recursive `Formula` passes. The
    // balanced fold keeps the node count identical and makes the depth
    // logarithmic — `ceil(log2 W)` combine levels over a 3-node leaf
    // (`BvToInt(BvExtract(IntToBv(Var)))` is 4 for `ctpop`, 3 for the cascades).
    for (width, ctpop_d, bitrev_d, bswap_d) in
        [(8u32, 7, 6, 3), (16, 8, 7, 4), (32, 9, 8, 5), (64, 10, 9, 6), (128, 11, 10, 7)]
    {
        assert_eq!(depth(&ctpop_value(&x_var(), width)), ctpop_d, "ctpop depth W={width}");
        assert_eq!(
            depth(&bitreverse_bits(&x_var(), width)),
            bitrev_d,
            "bitreverse depth W={width}"
        );
        assert_eq!(depth(&bswap_bits(&x_var(), width).unwrap()), bswap_d, "bswap depth W={width}");
    }
    for (width, ctpop_n, bitrev_n, bswap_n) in [
        (8u32, 39, 31, 3),
        (16, 79, 63, 7),
        (32, 159, 127, 15),
        (64, 319, 255, 31),
        (128, 639, 511, 63),
    ] {
        assert_eq!(nodes(&ctpop_value(&x_var(), width)), ctpop_n, "ctpop W={width}");
        assert_eq!(nodes(&bitreverse_bits(&x_var(), width)), bitrev_n, "bitreverse W={width}");
        assert_eq!(nodes(&bswap_bits(&x_var(), width).unwrap()), bswap_n, "bswap W={width}");
    }
}
