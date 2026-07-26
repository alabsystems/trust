// Unit tests for the M4 strict-mode arithmetic FLOOR (deterministic, one
// fragment, fidelity-checked vs the trust-js-interp oracle). These are NOT
// tests of the autoformalization tier — there is no LLM, no intent, no native
// install here.

use super::*;

fn verified(js: &str) -> VerifiedLowering {
    match lower_and_verify(js) {
        Ok(v) => v,
        Err(e) => panic!("expected a verified lowering for {js:?}, got refusal: {e:?}"),
    }
}

fn refusal(js: &str) -> Refusal {
    match lower_and_verify(js) {
        Ok(v) => panic!("expected a refusal for {js:?}, got a lowering: {v:?}"),
        Err(e) => e,
    }
}

// ---------------------------------------------------------------------------
// (1) POSITIVE — pure-arith functions lower and verify bit-equal to the oracle.
// ---------------------------------------------------------------------------

#[test]
fn positive_add_mul() {
    let v = verified("function f(a,b){return a+b*2}");
    assert_eq!(v.rust_source, "fn f(p0: f64, p1: f64) -> f64 { p0 + p1 * 2.0 }");
    assert_eq!(
        v.ir,
        ArithIr::Add(
            Box::new(ArithIr::Param(0)),
            Box::new(ArithIr::Mul(Box::new(ArithIr::Param(1)), Box::new(ArithIr::Lit(2.0)),)),
        )
    );
    assert!(v.ledger.all_equal);
    assert!(v.ledger.samples_checked > 0);
    assert!(v.ledger.first_divergence.is_none());
}

#[test]
fn positive_neg_square_plus_one() {
    let v = verified("function g(x){return -(x*x) + 1}");
    assert_eq!(v.rust_source, "fn g(p0: f64) -> f64 { -(p0 * p0) + 1.0 }");
    assert!(v.rust_source.contains("fn g("));
    assert!(v.ledger.all_equal);
}

#[test]
fn positive_diff_over() {
    let v = verified("function h(a,b,c){return (a-b)/c}");
    assert_eq!(v.rust_source, "fn h(p0: f64, p1: f64, p2: f64) -> f64 { (p0 - p1) / p2 }");
    assert!(v.ledger.all_equal);
    // arity 3 => the full 18^3 product exceeds the 4096 cap, so it is capped.
    assert!(v.ledger.samples_checked <= crate::fidelity::pin().max_samples());
}

#[test]
fn positive_remainder_proves_js_mod_equals_f64_mod() {
    // This one PROVES, per input, that JS `%` == Rust `f64 %`: the interp oracle
    // (independent semantics) and eval_ir agree bit-for-bit on every sample, or
    // the lowering would have refused. A VerifiedLowering here IS the proof.
    let v = verified("function r(a,b){return a%b}");
    assert_eq!(v.rust_source, "fn r(p0: f64, p1: f64) -> f64 { p0 % p1 }");
    assert!(v.ledger.all_equal, "JS % diverged from f64 % on the corpus");
    assert!(v.ledger.first_divergence.is_none());

    // Independently re-run the whole corpus and confirm bit-for-bit agreement,
    // so the "% matched on every sample" claim is asserted, not just implied.
    let samples = build_samples(2);
    let mut matched = 0usize;
    for input in &samples {
        let rust = eval_ir(&v.ir, input);
        let js = oracle_eval("function r(a,b){return a%b}", "r", input)
            .expect("oracle must return a number for a%b on every sample");
        assert!(
            same_js_number(js, rust),
            "JS%({:?})={} but f64%={}",
            input,
            projection_number_repr(js),
            projection_number_repr(rust)
        );
        matched += 1;
    }
    assert_eq!(matched, v.ledger.samples_checked);
    assert!(matched >= 300, "expected the full arity-2 product (~324), got {matched}");
}

#[test]
fn positive_unary_plus_is_folded_identity() {
    // Unary `+` on a number is the identity; it folds away (no Pos node), and
    // the fidelity check confirms bit-equality with the oracle.
    let v = verified("function p(a){return +a + +(a*a)}");
    assert_eq!(
        v.ir,
        ArithIr::Add(
            Box::new(ArithIr::Param(0)),
            Box::new(ArithIr::Mul(Box::new(ArithIr::Param(0)), Box::new(ArithIr::Param(0)),)),
        )
    );
    assert!(v.ledger.all_equal);
}

// ---------------------------------------------------------------------------
// (1b) EXACT-STRING precedence/associativity render pins (cheap, no rustc).
//      These catch a `render_rust` regression FAST — a dropped paren, a wrong
//      associativity, or a mis-rendered literal — independently of the fidelity
//      check (which only ever exercises `eval_ir`, never the rendered string).
//      The compile-and-check test (src/compile_check.rs) then PROVES, via the
//      real rustc, that each of these strings MEANS what `eval_ir` computes.
//      Every expected string below is semantically-correct precedence.
// ---------------------------------------------------------------------------

/// Render straight from the fragment gate + renderer (no oracle, no rustc).
fn rendered(js: &str) -> String {
    let Lowered { name, arity, bindings, ret } =
        lower(js).unwrap_or_else(|e| panic!("{js:?} should lower, got refusal: {e:?}"));
    render_rust(&bindings, &ret, &name, arity)
}

#[test]
fn render_precedence_exact_strings() {
    let cases: &[(&str, &str)] = &[
        // Left-assoc `-`: `a-b-c` is `(a-b)-c`, so NO parens.
        (
            "function s(a,b,c){return a-b-c}",
            "fn s(p0: f64, p1: f64, p2: f64) -> f64 { p0 - p1 - p2 }",
        ),
        // Right-nested `-` MUST keep its parens (`a-(b-c)` != `a-b-c`).
        (
            "function sr(a,b,c){return a-(b-c)}",
            "fn sr(p0: f64, p1: f64, p2: f64) -> f64 { p0 - (p1 - p2) }",
        ),
        // Left-assoc `/`: `a/b/c` is `(a/b)/c`, NO parens.
        (
            "function d(a,b,c){return a/b/c}",
            "fn d(p0: f64, p1: f64, p2: f64) -> f64 { p0 / p1 / p2 }",
        ),
        // Right-nested `/` MUST keep its parens.
        (
            "function dr(a,b,c){return a/(b/c)}",
            "fn dr(p0: f64, p1: f64, p2: f64) -> f64 { p0 / (p1 / p2) }",
        ),
        // `*` binds tighter than `-`, so `a-b*c` needs no parens.
        (
            "function m(a,b,c){return a-b*c}",
            "fn m(p0: f64, p1: f64, p2: f64) -> f64 { p0 - p1 * p2 }",
        ),
        // Forcing `-` before `*` MUST keep the parens around the difference.
        (
            "function mp(a,b,c){return (a-b)*c}",
            "fn mp(p0: f64, p1: f64, p2: f64) -> f64 { (p0 - p1) * p2 }",
        ),
        // Unary minus over a product parenthesizes the product.
        ("function ng(a,b){return -(a*b)}", "fn ng(p0: f64, p1: f64) -> f64 { -(p0 * p1) }"),
        // Double negation MUST render `-(-p0)` (never the invalid `--p0`).
        ("function nn(a){return -(-a)}", "fn nn(p0: f64) -> f64 { -(-p0) }"),
        // Left-assoc `%`.
        (
            "function rem(a,b,c){return a%b%c}",
            "fn rem(p0: f64, p1: f64, p2: f64) -> f64 { p0 % p1 % p2 }",
        ),
        // The max ternary.
        (
            "function mx(a,b){return a>b?a:b}",
            "fn mx(p0: f64, p1: f64) -> f64 { if p0 > p1 { p0 } else { p1 } }",
        ),
        // Nested ternary (sign).
        (
            "function sgn(a){return a>0?1:(a<0?-1:0)}",
            "fn sgn(p0: f64) -> f64 { if p0 > 0.0 { 1.0 } else { if p0 < 0.0 { -1.0 } else { 0.0 } } }",
        ),
        // Compound-condition clamp ternary.
        (
            "function cl(x,lo,hi){return x<lo?lo:(x>hi?hi:x)}",
            "fn cl(p0: f64, p1: f64, p2: f64) -> f64 { if p0 < p1 { p1 } else { if p0 > p2 { p2 } else { p0 } } }",
        ),
    ];
    for (js, expected) in cases {
        assert_eq!(&rendered(js), expected, "render mismatch for {js:?}");
    }
}

// ---------------------------------------------------------------------------
// (2) NEGATIVE controls — each REFUSES with the right reason, emits nothing.
// ---------------------------------------------------------------------------

#[test]
fn negative_string_concat() {
    // `a + "x"` might be string concat: refuse at the string operand.
    match refusal("function s(a,b){return a+\"x\"}") {
        Refusal::UnsupportedConstruct { construct } => {
            assert!(construct.contains("string literal"), "got {construct}");
        }
        other => panic!("expected UnsupportedConstruct(string literal), got {other:?}"),
    }
}

#[test]
fn negative_comparison() {
    // Comparisons are now IN the fragment, but `a<b` types to Bool, so a function
    // whose WHOLE return is a bare comparison is out of the numeric-result
    // fragment and is refused (nothing emitted) — a different, still-sound reason
    // than the pre-extension `UnsupportedConstruct`.
    match refusal("function c(a,b){return a<b}") {
        Refusal::NonNumericResult { .. } => {}
        other => panic!("expected NonNumericResult for a bare comparison, got {other:?}"),
    }
}

#[test]
fn negative_call() {
    // A member-call whose object is NOT the `Math` builtin (here a free `obj`) is
    // not a supported call: only a direct call to an earlier top-level function,
    // or an allow-listed `Math.<name>(...)`, is. NOTE: `Math.abs(a)` moved OUT of
    // this test — it is now an allow-listed builtin that lowers+verifies (covered
    // by the Math positive tests below).
    match refusal("function k(a){return obj.f(a)}") {
        Refusal::UnsupportedConstruct { construct } => {
            assert!(construct.contains("call expression"), "got {construct}");
        }
        other => panic!("expected UnsupportedConstruct(call), got {other:?}"),
    }
}

#[test]
fn negative_member() {
    match refusal("function m(a){return a.b}") {
        Refusal::UnsupportedConstruct { construct } => {
            assert!(construct.contains("member access"), "got {construct}");
        }
        other => panic!("expected UnsupportedConstruct(member), got {other:?}"),
    }
}

#[test]
fn negative_statement_not_single_return() {
    // NOTE: the pre-extension example here (`let y=a;return y`) is now a VALID
    // binding lowering (covered by the binding positive tests below). A body that
    // still refuses as "not `<binding>* return`" is a bare NON-declaration
    // statement before the return — here a bare expression statement `a+1;`.
    match refusal("function t(a){a+1;return a}") {
        Refusal::UnsupportedStatement { .. } => {}
        other => panic!("expected UnsupportedStatement for a bare stmt, got {other:?}"),
    }
    // A body that does not end in a `return <expr>;` still refuses too.
    match refusal("function t2(a){const x=a;}") {
        Refusal::NotSingleArithReturn { .. } => {}
        other => panic!("expected NotSingleArithReturn for a missing return, got {other:?}"),
    }
}

#[test]
fn positive_two_independent_functions() {
    // NOTE: pre-composition this REFUSED as `NotSingleFunction`. The composition
    // increment (below) makes MULTIPLE top-level functions a valid module: the
    // LAST-declared (`two2`) is the ENTRY, earlier ones (`two`) are helpers. With
    // no calls between them this is just two free `fn`s; the entry `two2()`
    // returns 2. It lowers and verifies bit-for-bit against the oracle.
    let v = verified("function two(){return 1}function two2(){return 2}");
    assert_eq!(v.functions.len(), 2);
    assert_eq!(v.entry, 1);
    assert_eq!(v.functions[1].name, "two2");
    assert_eq!(v.functions[1].arity, 0);
    assert_eq!(v.ir, ArithIr::Lit(2.0));
    assert!(v.ledger.all_equal);
    assert_eq!(eval_module(&v.functions, v.entry, &[]), 2.0);
    // The rendered module carries BOTH free functions (helper first, entry last).
    assert_eq!(v.rust_source, "fn two() -> f64 { 1.0 }\nfn two2() -> f64 { 2.0 }");
}

#[test]
fn negative_bigint() {
    match refusal("function bi(a){return a+1n}") {
        Refusal::UnsupportedConstruct { construct } => {
            assert!(construct.contains("BigInt literal"), "got {construct}");
        }
        other => panic!("expected UnsupportedConstruct(BigInt), got {other:?}"),
    }
}

#[test]
fn negative_more_out_of_fragment() {
    // A grab-bag confirming fail-closed. NOTE: `x>0 ? 1 : 2` moved OUT of this
    // list — the conditional is now IN the extended fragment (covered by the
    // positive tests below); and `x | y` moved OUT — JS bitwise ops are now IN the
    // fragment (increment 8, covered by the bitwise positive tests below). These
    // all still refuse:
    //   - `x && y` on numeric params: `&&` needs boolean operands; we do NOT
    //     model ToBoolean of a number, so it is a type error, not a coercion.
    for js in [
        "function a(x,y){return x && y}", // Num operands to `&&` => TypeError
        "function a(x,y){return x ** y}", // exponent operator
        "function a(x){return `${x}`}",   // template
        "function a(x){return x + q}",    // free identifier `q`
        "function a(x){return (x=1)}",    // assignment
        "function a(x){return NaN}",      // NaN is an identifier, not a literal
        "const a = (x) => x;",            // arrow, not a function declaration
    ] {
        assert!(lower_and_verify(js).is_err(), "expected refusal for {js:?}");
    }
}

// ---------------------------------------------------------------------------
// (3) The delta ledger CATCHES a wrong lowering (fidelity divergence), and the
//     wrong artifact is emitted NOWHERE.
// ---------------------------------------------------------------------------

#[test]
fn fidelity_divergence_is_caught() {
    // The JS says `a + b`; feed a deliberately WRONG IR (`a - b`). The oracle
    // and eval_ir must disagree, so the check refuses.
    let wrong = ArithIr::Sub(Box::new(ArithIr::Param(0)), Box::new(ArithIr::Param(1)));
    match check_fidelity("function d(a,b){return a+b}", "d", &[], &wrong, 2) {
        Err(Refusal::FidelityDivergence { input, js, rust }) => {
            assert_eq!(input.len(), 2);
            assert_ne!(js, rust, "a caught divergence must report differing values");
        }
        other => panic!("expected FidelityDivergence, got {other:?}"),
    }
}

#[test]
fn fidelity_catches_wrong_constant() {
    // JS `a * 2`, wrong IR `a * 3` — caught on the first non-zero sample.
    let wrong = ArithIr::Mul(Box::new(ArithIr::Param(0)), Box::new(ArithIr::Lit(3.0)));
    assert!(matches!(
        check_fidelity("function d(a){return a*2}", "d", &[], &wrong, 1),
        Err(Refusal::FidelityDivergence { .. })
    ));
}

// ---------------------------------------------------------------------------
// Rendering / sampling spot checks.
// ---------------------------------------------------------------------------

#[test]
fn render_negative_zero_and_specials_roundtrip() {
    // -0.0 distinguished from 0.0 in the oracle round-trip.
    assert_eq!(parse_projected_num("-0").map(f64::to_bits), Some((-0.0f64).to_bits()));
    assert_eq!(parse_projected_num("0").map(f64::to_bits), Some(0.0f64.to_bits()));
    assert!(parse_projected_num("NaN").unwrap().is_nan());
    assert_eq!(parse_projected_num("Infinity"), Some(f64::INFINITY));
    assert_eq!(parse_projected_num("-Infinity"), Some(f64::NEG_INFINITY));
    // A function that produces -0.0 on a -0.0 input still verifies (the oracle
    // and eval_ir agree that the result is -0.0, not +0.0).
    let v = verified("function z(a,b){return a+b*2}");
    let bits = eval_ir(&v.ir, &[-0.0, -0.0]).to_bits();
    assert_eq!(bits, (-0.0f64).to_bits());
}

#[test]
fn sample_corpus_is_bounded_and_deterministic() {
    assert_eq!(build_samples(0), vec![Vec::<f64>::new()]);
    assert_eq!(build_samples(1).len(), 18);
    assert_eq!(build_samples(2).len(), 324);
    assert!(build_samples(3).len() <= crate::fidelity::pin().max_samples());
    assert!(build_samples(5).len() <= crate::fidelity::pin().max_samples());
    // Determinism: identical across calls (compare by bit pattern, since the
    // corpus contains NaN and `NaN != NaN` under `f64: PartialEq`).
    let bits = |ss: Vec<Vec<f64>>| -> Vec<Vec<u64>> {
        ss.iter().map(|t| t.iter().map(|v| v.to_bits()).collect()).collect()
    };
    assert_eq!(bits(build_samples(3)), bits(build_samples(3)));
}

// ===========================================================================
// EXTENDED FRAGMENT (M4 floor increment 2): comparisons, boolean logic, and the
// conditional operator. Each positive lowers AND verifies bit-for-bit against
// the interp oracle over the corpus. Every negative refuses, emitting nothing.
// ===========================================================================

// ---- Positive: piecewise-numeric functions lower and verify ---------------

#[test]
fn positive_max_ternary_ir_and_render() {
    let v = verified("function mx(a,b){return a>b?a:b}");
    // The task's target artifact, byte-for-byte.
    assert_eq!(v.rust_source, "fn mx(p0: f64, p1: f64) -> f64 { if p0 > p1 { p0 } else { p1 } }");
    assert_eq!(
        v.ir,
        ArithIr::Cond {
            test: Box::new(BoolIr::Cmp {
                op: CmpOp::Gt,
                left: Box::new(ArithIr::Param(0)),
                right: Box::new(ArithIr::Param(1)),
            }),
            cons: Box::new(ArithIr::Param(0)),
            alt: Box::new(ArithIr::Param(1)),
        }
    );
    assert!(v.ledger.all_equal && v.ledger.first_divergence.is_none());
    assert_eq!(eval_ir(&v.ir, &[3.0, 2.0]), 3.0);
    assert_eq!(eval_ir(&v.ir, &[2.0, 3.0]), 3.0);
    // NaN > 5 is false => returns b (5). (Not "the larger", NaN is unordered.)
    assert_eq!(eval_ir(&v.ir, &[f64::NAN, 5.0]), 5.0);
}

#[test]
fn positive_min_ternary() {
    let v = verified("function mn(a,b){return a<b?a:b}");
    assert_eq!(v.rust_source, "fn mn(p0: f64, p1: f64) -> f64 { if p0 < p1 { p0 } else { p1 } }");
    assert!(v.ledger.all_equal);
}

#[test]
fn positive_abs_ternary_nan_and_neg_zero_agree() {
    let src = "function ab(a){return a<0?-a:a}";
    let v = verified(src);
    assert_eq!(v.rust_source, "fn ab(p0: f64) -> f64 { if p0 < 0.0 { -p0 } else { p0 } }");
    assert!(v.ledger.all_equal);
    assert_eq!(eval_ir(&v.ir, &[-3.0]), 3.0);

    // The WHOLE corpus already proved bit-equality; re-confirm the two subtle
    // corners explicitly (this ternary is NOT Math.abs: it branches on `a<0`).
    // NaN: `NaN<0` is false => returns `a` = NaN (both oracle and eval_ir).
    let jn = oracle_eval(src, "ab", &[f64::NAN]).expect("oracle number");
    let rn = eval_ir(&v.ir, &[f64::NAN]);
    assert!(jn.is_nan() && rn.is_nan(), "ab(NaN): js={jn} rust={rn}");
    assert!(same_js_number(jn, rn));
    assert_eq!(projection_number_repr(jn), "NaN");
    assert_eq!(projection_number_repr(rn), "NaN");

    // -0.0: `-0<0` is false => returns `a` = -0.0 (NOT +0 as Math.abs would).
    let jz = oracle_eval(src, "ab", &[-0.0]).expect("oracle number");
    let rz = eval_ir(&v.ir, &[-0.0]);
    assert_eq!(jz.to_bits(), (-0.0f64).to_bits(), "oracle ab(-0) must be -0");
    assert_eq!(rz.to_bits(), (-0.0f64).to_bits(), "eval ab(-0) must be -0");
    assert!(same_js_number(jz, rz));
    assert_eq!(projection_number_repr(jz), "-0");
    assert_eq!(projection_number_repr(rz), "-0");
}

#[test]
fn positive_sign_nested_ternary_nan_and_neg_zero() {
    let src = "function sgn(a){return a>0?1:(a<0?-1:0)}";
    let v = verified(src);
    assert_eq!(
        v.rust_source,
        "fn sgn(p0: f64) -> f64 { if p0 > 0.0 { 1.0 } else { if p0 < 0.0 { -1.0 } else { 0.0 } } }"
    );
    assert!(v.ledger.all_equal);
    assert_eq!(eval_ir(&v.ir, &[5.0]), 1.0);
    assert_eq!(eval_ir(&v.ir, &[-5.0]), -1.0);

    // sign(NaN): NaN>0 false, NaN<0 false => the `0` literal (+0.0), not NaN.
    let jn = oracle_eval(src, "sgn", &[f64::NAN]).expect("oracle number");
    let rn = eval_ir(&v.ir, &[f64::NAN]);
    assert!(same_js_number(jn, rn), "sgn(NaN): js={jn} rust={rn}");
    assert_eq!(projection_number_repr(jn), "0");
    assert_eq!(projection_number_repr(rn), "0");

    // sign(-0): -0>0 false, -0<0 false => the `0` literal (+0.0). Result is +0,
    // even though the input was -0 — both oracle and eval_ir agree.
    let jz = oracle_eval(src, "sgn", &[-0.0]).expect("oracle number");
    let rz = eval_ir(&v.ir, &[-0.0]);
    assert!(same_js_number(jz, rz), "sgn(-0): js={jz} rust={rz}");
    assert_eq!(projection_number_repr(jz), "0");
    assert_eq!(projection_number_repr(rz), "0");
}

#[test]
fn positive_clamp_nested() {
    let v = verified("function clamp(x,lo,hi){return x<lo?lo:(x>hi?hi:x)}");
    assert_eq!(
        v.rust_source,
        "fn clamp(p0: f64, p1: f64, p2: f64) -> f64 \
         { if p0 < p1 { p1 } else { if p0 > p2 { p2 } else { p0 } } }"
    );
    assert!(v.ledger.all_equal);
    assert_eq!(eval_ir(&v.ir, &[5.0, 0.0, 10.0]), 5.0);
    assert_eq!(eval_ir(&v.ir, &[-1.0, 0.0, 10.0]), 0.0);
    assert_eq!(eval_ir(&v.ir, &[99.0, 0.0, 10.0]), 10.0);
}

#[test]
fn positive_compound_and_condition() {
    let v = verified("function both(a,b){return a>0&&b>0?1:0}");
    assert_eq!(
        v.rust_source,
        "fn both(p0: f64, p1: f64) -> f64 { if p0 > 0.0 && p1 > 0.0 { 1.0 } else { 0.0 } }"
    );
    assert!(v.ledger.all_equal);
    assert_eq!(eval_ir(&v.ir, &[1.0, 1.0]), 1.0);
    assert_eq!(eval_ir(&v.ir, &[1.0, -1.0]), 0.0);
    assert_eq!(eval_ir(&v.ir, &[-1.0, 1.0]), 0.0);
}

#[test]
fn positive_or_not_and_booleq_conditions_verify() {
    // `||` in the condition.
    let a = verified("function either(a,b){return a>0||b>0?1:0}");
    assert_eq!(
        a.rust_source,
        "fn either(p0: f64, p1: f64) -> f64 { if p0 > 0.0 || p1 > 0.0 { 1.0 } else { 0.0 } }"
    );
    // `!` in the condition (parenthesizes its comparison operand).
    let b = verified("function sel(a,b){return !(a>b)?a:b}");
    assert_eq!(
        b.rust_source,
        "fn sel(p0: f64, p1: f64) -> f64 { if !(p0 > p1) { p0 } else { p1 } }"
    );
    // Bool === Bool: same-type strict equality, no coercion => Rust `bool ==`.
    let c = verified("function xnor(a,b){return (a>0)===(b>0)?1:0}");
    assert_eq!(
        c.rust_source,
        "fn xnor(p0: f64, p1: f64) -> f64 { if (p0 > 0.0) == (p1 > 0.0) { 1.0 } else { 0.0 } }"
    );
    for v in [&a, &b, &c] {
        assert!(v.ledger.all_equal, "expected a bit-equal ledger");
    }
}

#[test]
fn positive_numeric_equality_conditions() {
    // `===`/`!==` on two numbers map to f64 `==`/`!=` — proven per sample.
    let a = verified("function iseq(a,b){return a===b?1:0}");
    assert_eq!(
        a.rust_source,
        "fn iseq(p0: f64, p1: f64) -> f64 { if p0 == p1 { 1.0 } else { 0.0 } }"
    );
    let b = verified("function isne(a,b){return a!==b?1:0}");
    assert_eq!(
        b.rust_source,
        "fn isne(p0: f64, p1: f64) -> f64 { if p0 != p1 { 1.0 } else { 0.0 } }"
    );
    assert!(a.ledger.all_equal && b.ledger.all_equal);
    // NaN === NaN is false (the ledger proved it); -0 === +0 is true.
    assert_eq!(eval_ir(&a.ir, &[f64::NAN, f64::NAN]), 0.0);
    assert_eq!(eval_ir(&a.ir, &[-0.0, 0.0]), 1.0);
}

#[test]
fn positive_le_ge_conditions() {
    let a = verified("function le(a,b){return a<=b?1:0}");
    assert_eq!(
        a.rust_source,
        "fn le(p0: f64, p1: f64) -> f64 { if p0 <= p1 { 1.0 } else { 0.0 } }"
    );
    let b = verified("function ge(a,b){return a>=b?1:0}");
    assert_eq!(
        b.rust_source,
        "fn ge(p0: f64, p1: f64) -> f64 { if p0 >= p1 { 1.0 } else { 0.0 } }"
    );
    assert!(a.ledger.all_equal && b.ledger.all_equal);
}

// ---- Negative: type errors and non-numeric results refuse -----------------

#[test]
fn negative_bare_boolean_returns() {
    // A function whose whole return types to Bool is out of the numeric-result
    // fragment: refuse, emit nothing (comparison and logical-compound forms).
    for js in [
        "function p(a,b){return a<b}",
        "function q(a,b){return a>0 && b>0}",
        "function n(a){return !(a>0)}",
    ] {
        match lower_and_verify(js) {
            Err(Refusal::NonNumericResult { .. }) => {}
            other => panic!("expected NonNumericResult for {js:?}, got {other:?}"),
        }
    }
}

#[test]
fn negative_type_error_bool_plus_num() {
    // `(a>0)+1` is Bool + Num. JS would coerce (`true+1==2`); we REFUSE, never
    // coerce — a wrong lowering is never emitted.
    match refusal("function bad(a){return (a>0)+1}") {
        Refusal::TypeError { .. } => {}
        other => panic!("expected TypeError for Bool+Num, got {other:?}"),
    }
}

#[test]
fn negative_nonboolean_condition() {
    // `a ? a : b` with numeric `a`: we do NOT model ToBoolean of a number, so the
    // non-boolean condition is a type error (refuse), not a truthiness coercion.
    match refusal("function mix(a,b){return a?a:b}") {
        Refusal::TypeError { .. } => {}
        other => panic!("expected TypeError for a non-boolean condition, got {other:?}"),
    }
}

#[test]
fn negative_mismatched_conditional_branches() {
    // `c ? (a>0) : b` — then is Bool, else is Num: branches disagree => refuse.
    match refusal("function mm(a,b){return a>0 ? (a>0) : b}") {
        Refusal::TypeError { .. } => {}
        other => panic!("expected TypeError for mismatched branch types, got {other:?}"),
    }
}

#[test]
fn negative_mixed_equality_num_and_bool() {
    // `(a>0) === 1` — Bool === Num: mixed strict equality. Refuse (no coercion).
    match refusal("function me(a){return (a>0) === 1 ? 1 : 0}") {
        Refusal::TypeError { .. } => {}
        other => panic!("expected TypeError for Bool===Num, got {other:?}"),
    }
}

// ---- Ledger: a deliberately wrong conditional lowering is CAUGHT ----------

#[test]
fn fidelity_catches_swapped_conditional() {
    // JS is `a>b?a:b` (max). Feed a WRONG IR that swaps the branches (making it
    // min): on any sample with a>b the oracle (max) and eval_ir (min) disagree,
    // so the fidelity check refuses and NOTHING is emitted.
    let wrong = ArithIr::Cond {
        test: Box::new(BoolIr::Cmp {
            op: CmpOp::Gt,
            left: Box::new(ArithIr::Param(0)),
            right: Box::new(ArithIr::Param(1)),
        }),
        cons: Box::new(ArithIr::Param(1)), // swapped (max's `then` should be p0)
        alt: Box::new(ArithIr::Param(0)),  // swapped (max's `else` should be p1)
    };
    match check_fidelity("function mx(a,b){return a>b?a:b}", "mx", &[], &wrong, 2) {
        Err(Refusal::FidelityDivergence { input, js, rust }) => {
            assert_eq!(input.len(), 2);
            assert_ne!(js, rust, "a caught divergence must report differing values");
        }
        other => panic!("expected FidelityDivergence for a swapped conditional, got {other:?}"),
    }
}

// ===========================================================================
// EXTENDED FRAGMENT (M4 floor increment 3): local `const`/`let` bindings.
// Straight-line, SSA-only (each name bound once, never reassigned), numeric
// result. Each positive lowers a `<binding>* return <expr>` function AND verifies
// bit-for-bit against the interp oracle over the corpus (the oracle runs the
// ORIGINAL source, bindings and all, so bindings are covered for free). Every
// negative refuses, emitting nothing.
// ===========================================================================

// ---- Positive: straight-line binding functions lower and verify -----------

#[test]
fn positive_binding_single_num_local() {
    // A numeric local feeding the return: `t = a*b`, then `t + 1`.
    let v = verified("function f(a,b){ const t = a*b; return t + 1; }");
    assert_eq!(v.rust_source, "fn f(p0: f64, p1: f64) -> f64 { let l2: f64 = p0 * p1; l2 + 1.0 }");
    assert_eq!(
        v.bindings,
        vec![Binding {
            slot: 2,
            init: TypedIr::Num(ArithIr::Mul(
                Box::new(ArithIr::Param(0)),
                Box::new(ArithIr::Param(1)),
            )),
        }]
    );
    assert_eq!(v.ir, ArithIr::Add(Box::new(ArithIr::Local(2)), Box::new(ArithIr::Lit(1.0))));
    assert!(v.ledger.all_equal && v.ledger.first_divergence.is_none());
    assert_eq!(eval_func(&v.bindings, &v.ir, &[3.0, 4.0]), 13.0);
}

#[test]
fn positive_binding_difference_of_squares() {
    // Two numeric locals: `s = a+b`, `d = a-b`, `return s*d` == a² - b².
    let v = verified("function g(a,b){ const s = a+b; const d = a-b; return s*d; }");
    assert_eq!(
        v.rust_source,
        "fn g(p0: f64, p1: f64) -> f64 { let l2: f64 = p0 + p1; let l3: f64 = p0 - p1; l2 * l3 }"
    );
    assert!(v.ledger.all_equal && v.ledger.first_divergence.is_none());
    // (a+b)(a-b) = a² - b².
    assert_eq!(eval_func(&v.bindings, &v.ir, &[3.0, 2.0]), 5.0);
    assert_eq!(eval_func(&v.bindings, &v.ir, &[5.0, 3.0]), 16.0);
}

#[test]
fn positive_binding_square_of_square() {
    let v = verified("function h(a){ const sq = a*a; return sq*sq; }");
    assert_eq!(v.rust_source, "fn h(p0: f64) -> f64 { let l1: f64 = p0 * p0; l1 * l1 }");
    assert!(v.ledger.all_equal);
    assert_eq!(eval_func(&v.bindings, &v.ir, &[2.0]), 16.0);
}

#[test]
fn positive_binding_boolean_local_feeds_ternary() {
    // A BOOLEAN local (`big = a > b`) feeds a conditional's test. It renders as a
    // typed `let l2: bool = …;`, and its reference is `BoolIr::Local`.
    let v = verified("function p(a,b){ const big = a > b; return big ? a : b; }");
    assert_eq!(
        v.rust_source,
        "fn p(p0: f64, p1: f64) -> f64 { let l2: bool = p0 > p1; if l2 { p0 } else { p1 } }"
    );
    assert_eq!(
        v.bindings,
        vec![Binding {
            slot: 2,
            init: TypedIr::Bool(BoolIr::Cmp {
                op: CmpOp::Gt,
                left: Box::new(ArithIr::Param(0)),
                right: Box::new(ArithIr::Param(1)),
            }),
        }]
    );
    assert_eq!(
        v.ir,
        ArithIr::Cond {
            test: Box::new(BoolIr::Local(2)),
            cons: Box::new(ArithIr::Param(0)),
            alt: Box::new(ArithIr::Param(1)),
        }
    );
    assert!(v.ledger.all_equal);
    assert_eq!(eval_func(&v.bindings, &v.ir, &[3.0, 2.0]), 3.0);
    assert_eq!(eval_func(&v.bindings, &v.ir, &[2.0, 3.0]), 3.0);
    // NaN > 5 is false => returns b (5), exactly as the oracle proved.
    assert_eq!(eval_func(&v.bindings, &v.ir, &[f64::NAN, 5.0]), 5.0);
}

#[test]
fn positive_binding_dependency_chain() {
    // A chain of locals, each referencing the previous (lexical order).
    let v = verified("function c(a){ const x = a+1; const y = x+1; const z = y+1; return z; }");
    assert_eq!(
        v.rust_source,
        "fn c(p0: f64) -> f64 { let l1: f64 = p0 + 1.0; let l2: f64 = l1 + 1.0; \
         let l3: f64 = l2 + 1.0; l3 }"
    );
    assert!(v.ledger.all_equal);
    assert_eq!(eval_func(&v.bindings, &v.ir, &[10.0]), 13.0);
}

#[test]
fn positive_let_keyword_binds_like_const() {
    // `let` with a single initializer lowers identically to `const` (both are SSA
    // here — the Rust artifact always emits an immutable `let`).
    let v = verified("function fl(a){ let t = a*a; return t; }");
    assert_eq!(v.rust_source, "fn fl(p0: f64) -> f64 { let l1: f64 = p0 * p0; l1 }");
    assert!(v.ledger.all_equal);
    assert_eq!(eval_func(&v.bindings, &v.ir, &[3.0]), 9.0);
}

// ---- Negative: out-of-fragment statements / bindings refuse ---------------

#[test]
fn negative_binding_reassignment() {
    // SSA-only: a reassignment of a local is a non-declaration statement => refuse.
    match refusal("function r(a){ let x = a; x = x+1; return x; }") {
        Refusal::UnsupportedStatement { .. } => {}
        other => panic!("expected UnsupportedStatement for a reassignment, got {other:?}"),
    }
}

#[test]
fn negative_binding_use_before_decl() {
    // `const y = z` references `z` before it is declared (lexical order): `z` is
    // not yet in scope, so it refuses as a free/undeclared identifier.
    match refusal("function u(a){ const y = z; const z = a; return y; }") {
        Refusal::UnsupportedConstruct { construct } => {
            assert!(construct.contains("free identifier"), "got {construct}");
        }
        other => panic!("expected UnsupportedConstruct for use-before-decl, got {other:?}"),
    }
}

#[test]
fn negative_binding_free_variable() {
    // A free variable in the return (`q` is neither param nor local) => refuse.
    match refusal("function fv(a){ return a + q; }") {
        Refusal::UnsupportedConstruct { construct } => {
            assert!(construct.contains("free identifier"), "got {construct}");
        }
        other => panic!("expected UnsupportedConstruct for a free variable, got {other:?}"),
    }
}

#[test]
fn negative_binding_var() {
    // `var` has function-scope hoisting subtlety — out of the SSA fragment.
    match refusal("function v(a){ var x = a; return x; }") {
        Refusal::UnsupportedBinding { .. } => {}
        other => panic!("expected UnsupportedBinding for `var`, got {other:?}"),
    }
}

#[test]
fn negative_binding_boolean_result() {
    // `const b = a > 0; return b;` — the return types to Bool => refuse (only
    // numeric-result functions are in the fragment).
    match refusal("function nb(a){ const b = a > 0; return b; }") {
        Refusal::NonNumericResult { .. } => {}
        other => panic!("expected NonNumericResult for a bare-boolean local return, got {other:?}"),
    }
}

#[test]
fn negative_binding_multiple_declarators() {
    // `const x=1, y=2` — multiple declarators in one declaration => refuse.
    match refusal("function md(a){ const x=1, y=2; return a+x+y; }") {
        Refusal::UnsupportedBinding { .. } => {}
        other => panic!("expected UnsupportedBinding for multiple declarators, got {other:?}"),
    }
}

#[test]
fn negative_binding_if_statement() {
    // An `if` statement before the return is not a supported binding => refuse.
    match refusal("function iff(a){ if (a>0) return 1; return 0; }") {
        Refusal::UnsupportedStatement { .. } => {}
        other => panic!("expected UnsupportedStatement for an `if`, got {other:?}"),
    }
}

#[test]
fn negative_binding_missing_initializer() {
    // `let x;` (no initializer) — only the single-initializer form is supported.
    match refusal("function mi(a){ let x; return a; }") {
        Refusal::UnsupportedBinding { .. } => {}
        other => panic!("expected UnsupportedBinding for a missing initializer, got {other:?}"),
    }
}

#[test]
fn negative_binding_destructuring() {
    // A destructuring binding pattern is out of the fragment => refuse.
    match refusal("function ds(a){ const [x] = a; return x; }") {
        Refusal::UnsupportedBinding { .. } => {}
        other => panic!("expected UnsupportedBinding for destructuring, got {other:?}"),
    }
}

#[test]
fn negative_binding_redeclaration_and_shadowing() {
    // Redeclaring a local or shadowing a parameter refuses (nothing emitted). In
    // practice the parser rejects a duplicate lexical declaration first as an
    // early error; either way the outcome is a sound refusal. We only assert that
    // it REFUSES (never a lowering) — the honesty invariant.
    for js in [
        "function rd(a){ const x = 1; const x = 2; return x; }", // redeclare local
        "function sh(a){ const a = 1; return a; }",              // shadow param
    ] {
        assert!(lower_and_verify(js).is_err(), "expected a refusal for {js:?}");
    }
}

// ---- Ledger: a deliberately wrong binding lowering (slot swap) is CAUGHT ---

#[test]
fn fidelity_catches_swapped_binding_slot() {
    // JS `k(a,b)` = (a+b) - (a-b) = 2b. Correct bindings are s=a+b (slot 2) and
    // d=a-b (slot 3), with return Sub(Local(2), Local(3)). Feed a WRONG return
    // that SWAPS the two local slots — Sub(Local(3), Local(2)) = (a-b)-(a+b) = -2b
    // — which diverges from the oracle on any sample with b != 0, so the fidelity
    // check refuses and NOTHING is emitted.
    let js = "function k(a,b){ const s = a+b; const d = a-b; return s-d; }";
    let bindings = vec![
        Binding {
            slot: 2,
            init: TypedIr::Num(ArithIr::Add(
                Box::new(ArithIr::Param(0)),
                Box::new(ArithIr::Param(1)),
            )),
        },
        Binding {
            slot: 3,
            init: TypedIr::Num(ArithIr::Sub(
                Box::new(ArithIr::Param(0)),
                Box::new(ArithIr::Param(1)),
            )),
        },
    ];
    let wrong_ret = ArithIr::Sub(Box::new(ArithIr::Local(3)), Box::new(ArithIr::Local(2)));
    match check_fidelity(js, "k", &bindings, &wrong_ret, 2) {
        Err(Refusal::FidelityDivergence { input, js: j, rust }) => {
            assert_eq!(input.len(), 2);
            assert_ne!(j, rust, "a caught divergence must report differing values");
        }
        other => panic!("expected FidelityDivergence for a swapped binding slot, got {other:?}"),
    }

    // Sanity anchor: with the CORRECT return the same bindings verify, so the
    // divergence above is due to the swap, not a spurious check failure.
    let right_ret = ArithIr::Sub(Box::new(ArithIr::Local(2)), Box::new(ArithIr::Local(3)));
    let led = check_fidelity(js, "k", &bindings, &right_ret, 2)
        .expect("the correct binding lowering must verify bit-for-bit");
    assert!(led.all_equal && led.first_divergence.is_none());
}

// ===========================================================================
// EXTENDED FRAGMENT (M4 floor increment 4): MULTIPLE top-level functions +
// non-recursive CALLS between them — the COMPOSITION capability. The source is
// ONLY top-level `function` declarations, each already in the straight-line-SSA
// single-function fragment; the LAST-declared function is the ENTRY (arity = its
// params), earlier functions are helpers. An expression (in any function's
// initializers / return) may CALL a STRICTLY-EARLIER top-level function
// `g(e0, e1, ...)` — arg count == g's arity, each arg Num, result Num. The call
// graph is ACYCLIC by declaration order ⇒ non-recursive and trivially
// terminating. Same oracle-checked delta ledger, same honesty discipline: the
// oracle runs the ORIGINAL source (all functions hoisted) with a call to the
// entry appended, so the SAME per-sample bit-for-bit check covers calls for free;
// any divergence ⇒ Refusal, emitted nowhere.
// ===========================================================================

// ---- Positive: composed multi-function modules lower and verify -----------

#[test]
fn positive_call_sum_of_squares() {
    // A helper `sq` used twice in the entry: `sq(a) + sq(b)` == a² + b².
    let v = verified("function sq(x){return x*x} function f(a,b){return sq(a)+sq(b)}");
    assert_eq!(
        v.rust_source,
        "fn sq(p0: f64) -> f64 { p0 * p0 }\n\
         fn f(p0: f64, p1: f64) -> f64 { sq(p0) + sq(p1) }"
    );
    // The function table: helper `sq` (index 0), entry `f` (index 1).
    assert_eq!(v.functions.len(), 2);
    assert_eq!(v.entry, 1);
    assert_eq!(v.functions[0].name, "sq");
    assert_eq!(v.functions[0].arity, 1);
    assert_eq!(v.functions[1].name, "f");
    assert_eq!(v.functions[1].arity, 2);
    // The entry IR: Add of two calls to the helper (index 0) on p0 and p1.
    assert_eq!(
        v.ir,
        ArithIr::Add(
            Box::new(ArithIr::Call { callee: 0, args: vec![ArithIr::Param(0)] }),
            Box::new(ArithIr::Call { callee: 0, args: vec![ArithIr::Param(1)] }),
        )
    );
    assert!(v.ledger.all_equal && v.ledger.first_divergence.is_none());
    // 3² + 4² = 25; via eval_module, which resolves the helper calls.
    assert_eq!(eval_module(&v.functions, v.entry, &[3.0, 4.0]), 25.0);
    assert_eq!(eval_module(&v.functions, v.entry, &[0.0, 0.0]), 0.0);
}

#[test]
fn positive_call_feeds_binding_chained() {
    // A call feeding a `const` binding, then a chained call on that local:
    // `y = inc(a); return inc(y);` == a + 2.
    let v = verified("function inc(x){return x+1} function g(a){const y=inc(a);return inc(y);}");
    assert_eq!(
        v.rust_source,
        "fn inc(p0: f64) -> f64 { p0 + 1.0 }\n\
         fn g(p0: f64) -> f64 { let l1: f64 = inc(p0); inc(l1) }"
    );
    // The entry `g` binds a numeric local (slot 1) to a call, and returns a call
    // that consumes it.
    assert_eq!(
        v.bindings,
        vec![Binding {
            slot: 1,
            init: TypedIr::Num(ArithIr::Call { callee: 0, args: vec![ArithIr::Param(0)] })
        }]
    );
    assert_eq!(v.ir, ArithIr::Call { callee: 0, args: vec![ArithIr::Local(1)] });
    assert!(v.ledger.all_equal);
    assert_eq!(eval_module(&v.functions, v.entry, &[5.0]), 7.0);
    assert_eq!(eval_module(&v.functions, v.entry, &[-1.0]), 1.0);
}

#[test]
fn positive_call_nested_max_of_three() {
    // Nested calls: max-of-3 via a 2-argument max helper — `mx(mx(a,b),c)`.
    let v = verified("function mx(a,b){return a>b?a:b} function m3(a,b,c){return mx(mx(a,b),c);}");
    assert_eq!(
        v.rust_source,
        "fn mx(p0: f64, p1: f64) -> f64 { if p0 > p1 { p0 } else { p1 } }\n\
         fn m3(p0: f64, p1: f64, p2: f64) -> f64 { mx(mx(p0, p1), p2) }"
    );
    // The entry IR nests a call inside a call's argument.
    assert_eq!(
        v.ir,
        ArithIr::Call {
            callee: 0,
            args: vec![
                ArithIr::Call { callee: 0, args: vec![ArithIr::Param(0), ArithIr::Param(1)] },
                ArithIr::Param(2),
            ],
        }
    );
    assert!(v.ledger.all_equal);
    assert_eq!(eval_module(&v.functions, v.entry, &[1.0, 2.0, 3.0]), 3.0);
    assert_eq!(eval_module(&v.functions, v.entry, &[5.0, 1.0, 2.0]), 5.0);
    assert_eq!(eval_module(&v.functions, v.entry, &[2.0, 9.0, 4.0]), 9.0);
}

#[test]
fn positive_call_helper_in_condition() {
    // A helper used in a numeric context after a conditional: `pos(a) + pos(b)`
    // counts how many of a, b are > 0.
    let v = verified("function pos(x){return x>0?1:0} function h(a,b){return pos(a)+pos(b);}");
    assert_eq!(
        v.rust_source,
        "fn pos(p0: f64) -> f64 { if p0 > 0.0 { 1.0 } else { 0.0 } }\n\
         fn h(p0: f64, p1: f64) -> f64 { pos(p0) + pos(p1) }"
    );
    assert!(v.ledger.all_equal);
    assert_eq!(eval_module(&v.functions, v.entry, &[1.0, -1.0]), 1.0);
    assert_eq!(eval_module(&v.functions, v.entry, &[1.0, 1.0]), 2.0);
    assert_eq!(eval_module(&v.functions, v.entry, &[-1.0, -1.0]), 0.0);
    // pos(NaN): NaN>0 is false ⇒ 0; the oracle proved this bit-for-bit.
    assert_eq!(eval_module(&v.functions, v.entry, &[f64::NAN, 5.0]), 1.0);
}

// ---- Negative: recursion, bad calls, and bad modules refuse ---------------

#[test]
fn negative_call_direct_recursion() {
    // A call to the CURRENT function itself: `r` is not a strictly-earlier
    // top-level function (it is the one being lowered), so the call cannot
    // resolve ⇒ refuse. Recursion is impossible.
    match refusal("function r(n){return r(n)}") {
        Refusal::UnknownCallee { name } => assert_eq!(name, "r"),
        other => panic!("expected UnknownCallee for direct recursion, got {other:?}"),
    }
}

#[test]
fn negative_call_forward_later() {
    // `a` calls `b`, but `b` is declared LATER: when lowering `a`, `b` is not yet
    // in the earlier-functions table ⇒ refuse (only backward calls are legal).
    match refusal("function a(x){return b(x)} function b(x){return x}") {
        Refusal::UnknownCallee { name } => assert_eq!(name, "b"),
        other => panic!("expected UnknownCallee for a forward call, got {other:?}"),
    }
}

#[test]
fn negative_call_mutual_recursion() {
    // `e` calls `o` and `o` calls `e`: lowering `e` (declared first) cannot see
    // `o` (declared later) ⇒ refuse. A cycle can never be constructed.
    match refusal("function e(n){return o(n)} function o(n){return e(n)}") {
        Refusal::UnknownCallee { name } => assert_eq!(name, "o"),
        other => panic!("expected UnknownCallee for mutual recursion, got {other:?}"),
    }
}

#[test]
fn negative_call_arity_mismatch() {
    // `one` has arity 1; `c` calls it with two arguments ⇒ refuse.
    match refusal("function one(x){return x} function c(a){return one(a,a)}") {
        Refusal::CallArityMismatch { name, expected, found } => {
            assert_eq!(name, "one");
            assert_eq!(expected, 1);
            assert_eq!(found, 2);
        }
        other => panic!("expected CallArityMismatch, got {other:?}"),
    }
}

#[test]
fn negative_call_undeclared() {
    // `z` is neither an earlier top-level function nor anything else ⇒ refuse.
    match refusal("function u(a){return z(a)}") {
        Refusal::UnknownCallee { name } => assert_eq!(name, "z"),
        other => panic!("expected UnknownCallee for an undeclared callee, got {other:?}"),
    }
}

#[test]
fn negative_call_non_num_argument() {
    // A call argument must be Num: `id(a>0)` passes a boolean ⇒ TypeError (never
    // coerce). Only top-level earlier functions are callable, and only on numbers.
    match refusal("function id(x){return x} function f(a){return id(a>0)}") {
        Refusal::TypeError { .. } => {}
        other => panic!("expected TypeError for a non-Num call argument, got {other:?}"),
    }
}

#[test]
fn negative_call_to_param_or_local() {
    // A name bound as a PARAMETER is not callable (only earlier top-level
    // functions are) — even though `g` is in scope, `g(1)` refuses.
    match refusal("function f(g){return g(1)}") {
        Refusal::UnknownCallee { name } => assert_eq!(name, "g"),
        other => panic!("expected UnknownCallee for calling a parameter, got {other:?}"),
    }
    // Likewise a call to a LOCAL binding is refused.
    match refusal("function f(a){const t=a; return t(a);}") {
        Refusal::UnknownCallee { name } => assert_eq!(name, "t"),
        other => panic!("expected UnknownCallee for calling a local, got {other:?}"),
    }
}

#[test]
fn negative_module_non_function_top_level() {
    // A non-function top-level statement (`const K=1;`) refuses the WHOLE module —
    // the fragment has no top-level bindings, and `K` is not callable/bound in it.
    match refusal("const K=1; function f(a){return a+K}") {
        Refusal::NotSingleFunction { .. } => {}
        other => panic!("expected NotSingleFunction for a non-function top-level, got {other:?}"),
    }
}

#[test]
fn negative_module_helper_out_of_fragment() {
    // If ANY function in the module is outside the single-function fragment, the
    // WHOLE module refuses. Here `bad` uses reassignment (`y=y+1`), which is
    // SSA-forbidden ⇒ refuse — even though the entry `f` itself is in-fragment.
    match refusal("function bad(x){let y=x;y=y+1;return y} function f(a){return bad(a)}") {
        Refusal::UnsupportedStatement { .. } => {}
        other => {
            panic!("expected UnsupportedStatement from the out-of-fragment helper, got {other:?}")
        }
    }
}

#[test]
fn negative_module_duplicate_function_name() {
    // Two top-level functions with the same name make a call name ambiguous ⇒
    // refuse the whole module (fail-closed; the script parser does not reject a
    // duplicate top-level function declaration for us).
    match refusal("function d(x){return x} function d(a){return a+1}") {
        Refusal::Redeclaration { name } => assert_eq!(name, "d"),
        other => panic!("expected Redeclaration for a duplicate function name, got {other:?}"),
    }
}

// ---- Ledger: a deliberately wrong CALL lowering is CAUGHT ------------------

#[test]
fn fidelity_catches_wrong_callee_index() {
    // Module `inc`, `sq`, `f`, where `f(a)` should return `sq(a)` == a². Feed a
    // WRONG entry that calls the WRONG helper index (`inc`, index 0, == a+1). On
    // any sample with a² != a+1 (e.g. a=3: 9 vs 4) the oracle (sq) and eval_module
    // (inc) disagree, so the fidelity check refuses and NOTHING is emitted.
    let js = "function inc(x){return x+1} function sq(x){return x*x} function f(a){return sq(a)}";
    let functions = vec![
        LoweredFn {
            name: "inc".to_string(),
            arity: 1,
            bindings: vec![],
            ret_ir: ArithIr::Add(Box::new(ArithIr::Param(0)), Box::new(ArithIr::Lit(1.0))),
        },
        LoweredFn {
            name: "sq".to_string(),
            arity: 1,
            bindings: vec![],
            ret_ir: ArithIr::Mul(Box::new(ArithIr::Param(0)), Box::new(ArithIr::Param(0))),
        },
        LoweredFn {
            name: "f".to_string(),
            arity: 1,
            bindings: vec![],
            // WRONG: calls index 0 (`inc`) instead of index 1 (`sq`).
            ret_ir: ArithIr::Call { callee: 0, args: vec![ArithIr::Param(0)] },
        },
    ];
    match check_fidelity_module(js, &functions, 2) {
        Err(Refusal::FidelityDivergence { input, js: j, rust }) => {
            assert_eq!(input.len(), 1);
            assert_ne!(j, rust, "a caught divergence must report differing values");
        }
        other => panic!("expected FidelityDivergence for a wrong callee index, got {other:?}"),
    }

    // Sanity anchor: with the CORRECT callee (index 1, `sq`) the same module
    // verifies bit-for-bit — so the divergence above is due to the wrong index,
    // not a spurious failure.
    let mut right = functions;
    right[2].ret_ir = ArithIr::Call { callee: 1, args: vec![ArithIr::Param(0)] };
    let led = check_fidelity_module(js, &right, 2)
        .expect("the correct callee lowering must verify bit-for-bit");
    assert!(led.all_equal && led.first_divergence.is_none());
}

#[test]
fn fidelity_catches_dropped_call_argument() {
    // Same module shape, but the wrong entry DROPS an argument: `sq()` with zero
    // args instead of `sq(a)`. eval seeds sq with no params ⇒ its `p0` reads NaN
    // ⇒ result NaN, while the oracle returns a number ⇒ divergence, caught.
    let js = "function sq(x){return x*x} function f(a){return sq(a)}";
    let functions = vec![
        LoweredFn {
            name: "sq".to_string(),
            arity: 1,
            bindings: vec![],
            ret_ir: ArithIr::Mul(Box::new(ArithIr::Param(0)), Box::new(ArithIr::Param(0))),
        },
        LoweredFn {
            name: "f".to_string(),
            arity: 1,
            bindings: vec![],
            ret_ir: ArithIr::Call { callee: 0, args: vec![] }, // WRONG: dropped arg
        },
    ];
    match check_fidelity_module(js, &functions, 1) {
        Err(Refusal::FidelityDivergence { .. }) => {}
        other => panic!("expected FidelityDivergence for a dropped call argument, got {other:?}"),
    }
}

// ===========================================================================
// EXTENDED FRAGMENT (M4 floor increment 5): `Math.*` builtin calls, via the
// PROPOSE -> VALIDATE -> REFUSE discipline. Each supported builtin EMITS a
// proposed Rust lowering (a direct `f64` method for abs/floor/ceil/trunc/sqrt, a
// JS-semantics `__js_math_*` helper for the traps sign/round/min/max); the
// SAME oracle-checked delta ledger then VALIDATES it bit-for-bit — the oracle
// runs the ORIGINAL `Math.*` source, so a divergent proposal on ANY corpus sample
// is a Refusal, emitted nowhere. The proposal is untrusted; the ledger is the
// authority. Everything Math.* off the allow-list (Math.random, Math.hypot,
// Math.PI, wrong arity, aliased `Math`) refuses. Still deterministic strict-mode,
// numeric-result, corpus-bounded — NOT the LLM autoformalizer.
// ===========================================================================

// ---- Positive: allow-listed Math builtins lower and verify bit-exact ------

#[test]
fn positive_math_direct_unary_ops_lower_and_verify() {
    // The direct-map unary ops render as a plain `f64` method call and are
    // bit-identical to the oracle BY CONSTRUCTION (the interp computes the SAME
    // `n.abs()`/`floor()`/`ceil()`/`trunc()`/`sqrt()`). The ledger CONFIRMS it on
    // every corpus sample (incl. -0 / NaN / ±Inf), and no helper is prepended.
    let cases: &[(&str, &str, MathOp)] = &[
        ("function f(a){return Math.abs(a)}", "fn f(p0: f64) -> f64 { p0.abs() }", MathOp::Abs),
        (
            "function f(a){return Math.floor(a)}",
            "fn f(p0: f64) -> f64 { p0.floor() }",
            MathOp::Floor,
        ),
        ("function f(a){return Math.ceil(a)}", "fn f(p0: f64) -> f64 { p0.ceil() }", MathOp::Ceil),
        (
            "function f(a){return Math.trunc(a)}",
            "fn f(p0: f64) -> f64 { p0.trunc() }",
            MathOp::Trunc,
        ),
        ("function f(a){return Math.sqrt(a)}", "fn f(p0: f64) -> f64 { p0.sqrt() }", MathOp::Sqrt),
    ];
    for (js, expected, op) in cases {
        let v = verified(js);
        assert_eq!(&v.rust_source, expected, "render mismatch for {js:?}");
        assert_eq!(v.ir, ArithIr::MathCall { op: *op, args: vec![ArithIr::Param(0)] });
        assert!(
            v.ledger.all_equal && v.ledger.first_divergence.is_none(),
            "ledger must confirm bit-equality vs the oracle for {js:?}"
        );
        assert!(!v.rust_source.contains("__js_math_"), "direct-map op emits no helper: {js:?}");
    }
    // Re-check a few subtle corners the ledger already proved: abs(-0)=+0,
    // sqrt(-0)=-0, sqrt(-1)=NaN, ceil(-0.5)=-0 (the smallest int >= -0.5 is -0).
    let abs = verified("function f(a){return Math.abs(a)}");
    assert_eq!(eval_module(&abs.functions, abs.entry, &[-0.0]).to_bits(), 0.0f64.to_bits());
    let sqrt = verified("function f(a){return Math.sqrt(a)}");
    assert_eq!(eval_module(&sqrt.functions, sqrt.entry, &[-0.0]).to_bits(), (-0.0f64).to_bits());
    assert!(eval_module(&sqrt.functions, sqrt.entry, &[-1.0]).is_nan());
    let ceil = verified("function f(a){return Math.ceil(a)}");
    let jz = oracle_eval("function f(a){return Math.ceil(a)}", "f", &[-0.5]).expect("oracle");
    let rz = eval_module(&ceil.functions, ceil.entry, &[-0.5]);
    assert_eq!(jz.to_bits(), (-0.0f64).to_bits(), "oracle Math.ceil(-0.5) must be -0");
    assert_eq!(rz.to_bits(), (-0.0f64).to_bits(), "eval Math.ceil(-0.5) must be -0");
}

#[test]
fn positive_math_sign_signed_zero_and_nan() {
    let src = "function s(a){return Math.sign(a)}";
    let v = verified(src);
    // The proposed lowering prepends the JS-semantics helper (Math.sign is NOT
    // f64::signum, which returns ±1 on ±0).
    assert_eq!(
        v.rust_source,
        format!("{HELPER_SIGN}\nfn s(p0: f64) -> f64 {{ __js_math_sign(p0) }}")
    );
    assert_eq!(v.ir, ArithIr::MathCall { op: MathOp::Sign, args: vec![ArithIr::Param(0)] });
    assert!(v.ledger.all_equal && v.ledger.first_divergence.is_none());
    // The ledger CONFIRMED bit-equality vs the oracle on the ±0 and NaN samples;
    // re-check the corners explicitly: +0->+0, -0->-0, NaN->NaN, else ±1.
    for (input, proj) in &[(0.0, "0"), (-0.0, "-0"), (5.0, "1"), (-5.0, "-1")] {
        let js = oracle_eval(src, "s", &[*input]).expect("oracle number");
        let ours = eval_module(&v.functions, v.entry, &[*input]);
        assert!(same_js_number(js, ours), "Math.sign({input}): js={js} ours={ours}");
        assert_eq!(projection_number_repr(js), *proj);
        assert_eq!(projection_number_repr(ours), *proj);
    }
    let jn = oracle_eval(src, "s", &[f64::NAN]).expect("oracle number");
    let rn = eval_module(&v.functions, v.entry, &[f64::NAN]);
    assert!(jn.is_nan() && rn.is_nan() && same_js_number(jn, rn));
    assert_eq!(projection_number_repr(jn), "NaN");
}

#[test]
fn positive_math_round_half_toward_plus_infinity() {
    let src = "function r(a){return Math.round(a)}";
    let v = verified(src);
    assert_eq!(
        v.rust_source,
        format!("{HELPER_ROUND}\nfn r(p0: f64) -> f64 {{ __js_math_round(p0) }}")
    );
    assert_eq!(v.ir, ArithIr::MathCall { op: MathOp::Round, args: vec![ArithIr::Param(0)] });
    assert!(v.ledger.all_equal && v.ledger.first_divergence.is_none());
    // Half rounds toward +Inf (NOT f64::round's ties-away-from-zero): 0.5->1,
    // 2.5->3, -2.5->-2, -1.5->-1; -0.5->-0 and -0.4->-0 (sign preserved). The
    // corpus covered 0.5/-0.5/±0/±Inf/NaN; also check the away-from-zero contrast
    // values 2.5/-2.5/-1.5 (not in the corpus) — where naive .round() would give
    // 3/-3/-2 — and the -0 preservation the ledger confirmed on -0.5.
    for (input, proj) in &[
        (0.5, "1"),
        (2.5, "3"),
        (-2.5, "-2"),
        (1.5, "2"),
        (-1.5, "-1"),
        (-0.5, "-0"),
        (-0.4, "-0"),
        (0.4, "0"),
        (-0.0, "-0"),
        (0.0, "0"),
    ] {
        let js = oracle_eval(src, "r", &[*input]).expect("oracle number");
        let ours = eval_module(&v.functions, v.entry, &[*input]);
        assert!(same_js_number(js, ours), "Math.round({input}): js={js} ours={ours}");
        assert_eq!(projection_number_repr(js), *proj, "oracle Math.round({input})");
        assert_eq!(projection_number_repr(ours), *proj, "eval Math.round({input})");
    }
    assert_eq!(eval_module(&v.functions, v.entry, &[f64::INFINITY]), f64::INFINITY);
    assert_eq!(eval_module(&v.functions, v.entry, &[f64::NEG_INFINITY]), f64::NEG_INFINITY);
    assert!(eval_module(&v.functions, v.entry, &[f64::NAN]).is_nan());
}

#[test]
fn positive_math_min_nan_and_signed_zero() {
    let src = "function mn(a,b){return Math.min(a,b)}";
    let v = verified(src);
    // The task's target artifact for Math.min, byte-for-byte.
    assert_eq!(
        v.rust_source,
        format!("{HELPER_MIN}\nfn mn(p0: f64, p1: f64) -> f64 {{ __js_math_min(p0, p1) }}")
    );
    assert_eq!(
        v.ir,
        ArithIr::MathCall { op: MathOp::Min, args: vec![ArithIr::Param(0), ArithIr::Param(1)] }
    );
    assert!(v.ledger.all_equal && v.ledger.first_divergence.is_none());
    // NaN-propagating (NOT Rust f64::min, which is NaN-ignoring). The ledger
    // CONFIRMED bit-equality vs the oracle on the NaN samples; re-check.
    for input in [[f64::NAN, 5.0], [5.0, f64::NAN]] {
        let js = oracle_eval(src, "mn", &input).expect("oracle number");
        let ours = eval_module(&v.functions, v.entry, &input);
        assert!(
            js.is_nan() && ours.is_nan() && same_js_number(js, ours),
            "Math.min NaN sample {input:?}: js={js} ours={ours}"
        );
    }
    // Signed zero: Math.min(-0,+0) = -0 and Math.min(+0,-0) = -0 (min prefers -0).
    // The ledger CONFIRMED it on the ±0 samples; re-check both orders.
    for input in [[-0.0, 0.0], [0.0, -0.0]] {
        let js = oracle_eval(src, "mn", &input).expect("oracle number");
        let ours = eval_module(&v.functions, v.entry, &input);
        assert_eq!(js.to_bits(), (-0.0f64).to_bits(), "oracle Math.min{input:?} must be -0");
        assert_eq!(ours.to_bits(), (-0.0f64).to_bits(), "eval Math.min{input:?} must be -0");
        assert_eq!(projection_number_repr(js), "-0");
    }
}

#[test]
fn positive_math_max_nan_and_signed_zero() {
    let src = "function mx(a,b){return Math.max(a,b)}";
    let v = verified(src);
    assert_eq!(
        v.rust_source,
        format!("{HELPER_MAX}\nfn mx(p0: f64, p1: f64) -> f64 {{ __js_math_max(p0, p1) }}")
    );
    assert!(v.ledger.all_equal && v.ledger.first_divergence.is_none());
    // NaN-propagating. Ledger confirmed on the NaN samples; re-check.
    for input in [[f64::NAN, 5.0], [5.0, f64::NAN]] {
        let js = oracle_eval(src, "mx", &input).expect("oracle number");
        let ours = eval_module(&v.functions, v.entry, &input);
        assert!(js.is_nan() && ours.is_nan() && same_js_number(js, ours));
    }
    // Signed zero: Math.max(-0,+0) = +0 and Math.max(+0,-0) = +0 (max prefers +0);
    // Math.max(-0,-0) = -0. Ledger confirmed on the ±0 samples; re-check.
    for input in [[-0.0, 0.0], [0.0, -0.0]] {
        let js = oracle_eval(src, "mx", &input).expect("oracle number");
        let ours = eval_module(&v.functions, v.entry, &input);
        assert_eq!(js.to_bits(), 0.0f64.to_bits(), "oracle Math.max{input:?} must be +0");
        assert_eq!(ours.to_bits(), 0.0f64.to_bits(), "eval Math.max{input:?} must be +0");
        assert_eq!(projection_number_repr(js), "0");
    }
    let jz = oracle_eval(src, "mx", &[-0.0, -0.0]).expect("oracle number");
    let rz = eval_module(&v.functions, v.entry, &[-0.0, -0.0]);
    assert_eq!(jz.to_bits(), (-0.0f64).to_bits());
    assert_eq!(rz.to_bits(), (-0.0f64).to_bits());
}

#[test]
fn positive_math_clamp_composed() {
    // A composed builtin expression: Math.min(Math.max(x,lo),hi). Both helpers are
    // prepended (min before max, canonical order), and the ledger validates the
    // whole composition bit-for-bit against the oracle.
    let src = "function clamp(x,lo,hi){return Math.min(Math.max(x,lo),hi)}";
    let v = verified(src);
    assert_eq!(
        v.rust_source,
        format!(
            "{HELPER_MIN}\n{HELPER_MAX}\n\
             fn clamp(p0: f64, p1: f64, p2: f64) -> f64 \
             {{ __js_math_min(__js_math_max(p0, p1), p2) }}"
        )
    );
    assert!(v.ledger.all_equal && v.ledger.first_divergence.is_none());
    assert_eq!(eval_module(&v.functions, v.entry, &[5.0, 0.0, 10.0]), 5.0);
    assert_eq!(eval_module(&v.functions, v.entry, &[-1.0, 0.0, 10.0]), 0.0);
    assert_eq!(eval_module(&v.functions, v.entry, &[99.0, 0.0, 10.0]), 10.0);
}

#[test]
fn negative_math_pow_refused_transcendental() {
    // Math.pow is REFUSED, not shipped — the honesty fix an adversarial audit
    // forced. Math.pow is a TRANSCENDENTAL: IEEE-754 does NOT mandate a correctly-
    // rounded `pow`, so `f64::powf` (platform libm) is not bit-identical to JS
    // Math.pow (V8) in general — e.g. Math.pow(1.0038291389817462, 2) is
    // 1.0076729402688338 in node/V8 but 1.0076729402688340 via f64::powf (a 1-ULP
    // divergence). And the corpus fidelity check could NEVER catch that: the interp
    // oracle computes Math.pow with the SAME `f64::powf`, so eval_math == oracle is
    // a TAUTOLOGY (`powf == powf`) that provides ZERO independent validation. A
    // shipped Math.pow lowering would therefore CLAIM "bit-equal to JS" but not be.
    // (Note `p*p` — the same value in JS — lowers to exact Rust `*` and IS correct;
    // only the Math.pow route is unsound.) So Math.pow falls back to the faithful
    // tier: it REFUSES, and NOTHING is emitted.
    let src = "function f(a,b){return Math.pow(a,b)}";
    match refusal(src) {
        Refusal::UnsupportedConstruct { construct } => {
            assert!(
                construct.contains("Math.pow") && construct.contains("transcendental"),
                "got {construct}"
            );
        }
        other => panic!("expected UnsupportedConstruct(Math.pow transcendental), got {other:?}"),
    }
    // Emits nothing: it is a refusal, full stop — no lowering to inspect.
    assert!(lower_and_verify(src).is_err(), "Math.pow must not produce a lowering");
}

// ---- Negative: off-allow-list / misused Math refuses, emitting nothing ----

#[test]
fn negative_math_random_refuses() {
    // Math.random is nondeterministic — MUST refuse (off the allow-list). The
    // interp oracle also has no coverage for it, so even reaching the ledger would
    // refuse; we refuse earlier, at lowering.
    match refusal("function rnd(){return Math.random()}") {
        Refusal::UnsupportedConstruct { construct } => {
            assert!(construct.contains("Math.random"), "got {construct}");
        }
        other => panic!("expected UnsupportedConstruct(Math.random), got {other:?}"),
    }
}

#[test]
fn negative_math_unsupported_builtin_hypot() {
    match refusal("function hy(a,b){return Math.hypot(a,b)}") {
        Refusal::UnsupportedConstruct { construct } => {
            assert!(construct.contains("Math.hypot"), "got {construct}");
        }
        other => panic!("expected UnsupportedConstruct(Math.hypot), got {other:?}"),
    }
}

#[test]
fn negative_math_pi_member() {
    // `Math.PI` is a member access (not a call) — out of the fragment => refuse.
    match refusal("function p(){return Math.PI}") {
        Refusal::UnsupportedConstruct { construct } => {
            assert!(construct.contains("member access"), "got {construct}");
        }
        other => panic!("expected UnsupportedConstruct(member access) for Math.PI, got {other:?}"),
    }
}

#[test]
fn negative_math_min_wrong_arity() {
    // Math.min/max are restricted to EXACTLY 2 args (JS is variadic; !=2 refuses,
    // to stay simple and sound).
    for js in [
        "function m1(a){return Math.min(a)}",         // 1 arg
        "function m3(a,b,c){return Math.min(a,b,c)}", // 3 args
    ] {
        match lower_and_verify(js) {
            Err(Refusal::UnsupportedConstruct { construct }) => {
                assert!(
                    construct.contains("Math.min expects exactly 2"),
                    "got {construct} for {js:?}"
                );
            }
            other => panic!("expected UnsupportedConstruct(arity) for {js:?}, got {other:?}"),
        }
    }
}

#[test]
fn negative_math_used_as_value() {
    // `Math` used other than as `Math.<name>(...)`: aliasing it to a local makes
    // `Math` a free identifier in the initializer => refuse (never reaches `.abs`).
    match refusal("function mv(){const m=Math;return m.abs(1)}") {
        Refusal::UnsupportedConstruct { construct } => {
            assert!(construct.contains("free identifier `Math`"), "got {construct}");
        }
        other => panic!("expected UnsupportedConstruct(free Math) for aliasing, got {other:?}"),
    }
}

// ---- Ledger: a deliberately wrong Math proposal is CAUGHT ------------------

#[test]
fn fidelity_would_catch_naive_min_on_nan() {
    // A NAIVE Math.min lowering to Rust's f64::min would be WRONG: f64::min is
    // NaN-IGNORING (min(NaN,x)=x), whereas JS Math.min is NaN-PROPAGATING
    // (Math.min(NaN,x)=NaN). Demonstrate the ledger's oracle would catch it: on
    // the NaN sample the oracle and the naive `a.min(b)` proposal disagree, while
    // OUR (correct) lowering agrees with the oracle bit-for-bit.
    let src = "function mn(a,b){return Math.min(a,b)}";
    let v = verified(src);
    assert!(v.ledger.all_equal);
    let js = oracle_eval(src, "mn", &[f64::NAN, 5.0]).expect("oracle number");
    assert!(js.is_nan(), "JS Math.min(NaN,5) must be NaN");
    let naive = (f64::NAN).min(5.0); // Rust f64::min: NaN-ignoring => 5.0
    assert_eq!(naive, 5.0);
    assert!(!same_js_number(js, naive), "the naive f64::min proposal must diverge from the oracle");
    let ours = eval_module(&v.functions, v.entry, &[f64::NAN, 5.0]);
    assert!(ours.is_nan() && same_js_number(js, ours));
}

#[test]
fn fidelity_catches_swapped_math_op() {
    // JS is Math.max; feed a WRONG IR using Math.min. On any sample with a<b the
    // oracle (max) and eval (min) disagree => the ledger refuses, emitting nothing.
    let src = "function mx(a,b){return Math.max(a,b)}";
    let wrong =
        ArithIr::MathCall { op: MathOp::Min, args: vec![ArithIr::Param(0), ArithIr::Param(1)] };
    match check_fidelity(src, "mx", &[], &wrong, 2) {
        Err(Refusal::FidelityDivergence { input, js, rust }) => {
            assert_eq!(input.len(), 2);
            assert_ne!(js, rust, "a caught divergence must report differing values");
        }
        other => panic!("expected FidelityDivergence for a swapped Math op, got {other:?}"),
    }
    // Sanity anchor: the CORRECT op verifies, so the divergence is due to the swap.
    let right =
        ArithIr::MathCall { op: MathOp::Max, args: vec![ArithIr::Param(0), ArithIr::Param(1)] };
    let led = check_fidelity(src, "mx", &[], &right, 2)
        .expect("the correct Math.max lowering must verify bit-for-bit");
    assert!(led.all_equal && led.first_divergence.is_none());
}

// ===========================================================================
// EXTENDED FRAGMENT (M4 floor increment 6): a single numeric ARRAY-FOLD via a
// for-of reduction — the real-numeric-program shape (sum / product / dot-product
// / max-of-array). ONE function form takes a number-array first parameter and
// reduces it: `function f(ARR, s0, …) { <binding>* let ACC = <init>;
// for (const X of ARR) { ACC = <step>; } return <ret>; }`. Each positive lowers
// AND verifies bit-for-bit against the interp oracle over the (array × scalar)
// corpus — the oracle runs the REAL JS for-of, so JS reduction semantics
// (left-to-right, NaN propagation, signed zero) are the authority. Every negative
// refuses, emitting nothing. Still deterministic strict-mode, numeric-result,
// corpus-bounded, terminating on finite arrays — NOT the LLM autoformalizer.
// ===========================================================================

/// A verified fold: the module must have lowered into a fold entry (`v.fold`).
fn verified_fold(js: &str) -> (VerifiedLowering, FoldFn) {
    let v = verified(js);
    let fold = v.fold.clone().unwrap_or_else(|| {
        panic!("expected an array-fold lowering for {js:?}, got a scalar module")
    });
    (v, fold)
}

// ---- Positive: array-fold functions lower and verify bit-equal to the oracle ---

#[test]
fn positive_fold_sum_ir_and_render() {
    // The task's flagship shape. The array is `arr: &[f64]`; the accumulator is a
    // `let mut` local (slot 1), the loop var a local (slot 2).
    let (v, fold) =
        verified_fold("function sum(arr){ let s=0; for(const x of arr){ s=s+x; } return s; }");
    assert_eq!(
        v.rust_source,
        "fn sum(arr: &[f64]) -> f64 { let mut l1: f64 = 0.0; for &l2 in arr { l1 = l1 + l2; } l1 }"
    );
    assert_eq!(fold.name, "sum");
    assert_eq!(fold.scalar_arity, 0);
    assert!(fold.pre_bindings.is_empty());
    assert_eq!(fold.acc_slot, 1);
    assert_eq!(fold.loop_var_slot, 2);
    assert_eq!(fold.acc_init, ArithIr::Lit(0.0));
    // step: s + x == Local(1) + Local(2); return: Local(1).
    assert_eq!(fold.step, ArithIr::Add(Box::new(ArithIr::Local(1)), Box::new(ArithIr::Local(2))));
    assert_eq!(fold.ret, ArithIr::Local(1));
    assert!(v.ledger.all_equal && v.ledger.first_divergence.is_none());
    assert!(v.ledger.samples_checked > 0);
    // Direct eval spot checks (helpers table is empty).
    assert_eq!(eval_fold(&fold, &[], &[1.0, 2.0, 3.0], &[]), 6.0);
    assert_eq!(eval_fold(&fold, &[], &[], &[]), 0.0); // empty array => the seed
    assert_eq!(eval_fold(&fold, &[], &[0.1, 0.2, 0.3], &[]), 0.1 + 0.2 + 0.3);
}

#[test]
fn positive_fold_product() {
    let (v, fold) =
        verified_fold("function prod(arr){ let p=1; for(const x of arr){ p = p*x; } return p; }");
    assert_eq!(
        v.rust_source,
        "fn prod(arr: &[f64]) -> f64 { let mut l1: f64 = 1.0; for &l2 in arr { l1 = l1 * l2; } l1 }"
    );
    assert_eq!(fold.acc_init, ArithIr::Lit(1.0));
    assert!(v.ledger.all_equal && v.ledger.first_divergence.is_none());
    assert_eq!(eval_fold(&fold, &[], &[2.0, 3.0, 4.0], &[]), 24.0);
    assert_eq!(eval_fold(&fold, &[], &[], &[]), 1.0); // empty product => 1
}

#[test]
fn positive_fold_sum_of_squares() {
    let (v, fold) = verified_fold(
        "function sumsq(arr){ let s=0; for(const x of arr){ s = s + x*x; } return s; }",
    );
    assert_eq!(
        v.rust_source,
        "fn sumsq(arr: &[f64]) -> f64 { let mut l1: f64 = 0.0; for &l2 in arr { l1 = l1 + l2 * l2; } l1 }"
    );
    assert!(v.ledger.all_equal && v.ledger.first_divergence.is_none());
    assert_eq!(eval_fold(&fold, &[], &[1.0, 2.0, 3.0], &[]), 14.0);
}

#[test]
fn positive_fold_axpy_uses_scalar_param() {
    // A scalar param `k` in the step: the array is slot 0, `k` is p1 (slot 1), the
    // accumulator slot 2, the loop var slot 3.
    let (v, fold) = verified_fold(
        "function axpy(arr,k){ let s=0; for(const x of arr){ s = s + k*x; } return s; }",
    );
    assert_eq!(
        v.rust_source,
        "fn axpy(arr: &[f64], p1: f64) -> f64 { let mut l2: f64 = 0.0; for &l3 in arr { l2 = l2 + p1 * l3; } l2 }"
    );
    assert_eq!(fold.scalar_arity, 1);
    assert_eq!(fold.acc_slot, 2);
    assert_eq!(fold.loop_var_slot, 3);
    // step: s + k*x == Local(2) + Param(1)*Local(3).
    assert_eq!(
        fold.step,
        ArithIr::Add(
            Box::new(ArithIr::Local(2)),
            Box::new(ArithIr::Mul(Box::new(ArithIr::Param(1)), Box::new(ArithIr::Local(3)))),
        )
    );
    assert!(v.ledger.all_equal && v.ledger.first_divergence.is_none());
    // k=2 over [1,2,3] => 2*(1+2+3) = 12.
    assert_eq!(eval_fold(&fold, &[], &[1.0, 2.0, 3.0], &[2.0]), 12.0);
}

#[test]
fn positive_fold_maxabs_step_calls_math() {
    // The step calls Math.max / Math.abs (trap ops): the __js_math_max helper is
    // prepended, and Math.abs renders as `l2.abs()`. NaN-propagating Math.max means
    // an array containing NaN folds to NaN — the oracle proves it bit-for-bit.
    let (v, fold) = verified_fold(
        "function maxabs(arr){ let m=0; for(const x of arr){ m = Math.max(m, Math.abs(x)); } return m; }",
    );
    assert_eq!(
        v.rust_source,
        format!(
            "{HELPER_MAX}\n\
             fn maxabs(arr: &[f64]) -> f64 {{ let mut l1: f64 = 0.0; for &l2 in arr {{ l1 = __js_math_max(l1, l2.abs()); }} l1 }}"
        )
    );
    assert_eq!(
        fold.step,
        ArithIr::MathCall {
            op: MathOp::Max,
            args: vec![
                ArithIr::Local(1),
                ArithIr::MathCall { op: MathOp::Abs, args: vec![ArithIr::Local(2)] },
            ],
        }
    );
    assert!(v.ledger.all_equal && v.ledger.first_divergence.is_none());
    assert_eq!(eval_fold(&fold, &[], &[-3.0, 1.0, -2.0], &[]), 3.0);
    // NaN propagates through Math.max => NaN.
    assert!(eval_fold(&fold, &[], &[1.0, f64::NAN, 2.0], &[]).is_nan());
}

#[test]
fn positive_fold_mean_times2_return_over_acc_and_scalar() {
    // A non-trivial return expression over the accumulator and a scalar param:
    // `return s/n*2` == (sum/n)*2.
    let (v, fold) = verified_fold(
        "function mean_times2(arr,n){ let s=0; for(const x of arr){ s = s+x; } return s/n*2; }",
    );
    assert_eq!(
        v.rust_source,
        "fn mean_times2(arr: &[f64], p1: f64) -> f64 { let mut l2: f64 = 0.0; for &l3 in arr { l2 = l2 + l3; } l2 / p1 * 2.0 }"
    );
    // return: (s / n) * 2 == Mul(Div(Local(2), Param(1)), Lit(2.0)).
    assert_eq!(
        fold.ret,
        ArithIr::Mul(
            Box::new(ArithIr::Div(Box::new(ArithIr::Local(2)), Box::new(ArithIr::Param(1)))),
            Box::new(ArithIr::Lit(2.0)),
        )
    );
    assert!(v.ledger.all_equal && v.ledger.first_divergence.is_none());
    // (1+2+3)/3*2 == 4.
    assert_eq!(eval_fold(&fold, &[], &[1.0, 2.0, 3.0], &[3.0]), 4.0);
}

#[test]
fn positive_fold_with_pre_binding_in_acc_init() {
    // A pre-binding before the accumulator, whose value seeds the accumulator init:
    // `const base = 10; let s = base; ...`. base is slot 1, the accumulator slot 2.
    let (v, fold) = verified_fold(
        "function pb(arr){ const base = 10; let s = base; for(const x of arr){ s = s + x; } return s; }",
    );
    assert_eq!(
        v.rust_source,
        "fn pb(arr: &[f64]) -> f64 { let l1: f64 = 10.0; let mut l2: f64 = l1; for &l3 in arr { l2 = l2 + l3; } l2 }"
    );
    assert_eq!(fold.pre_bindings.len(), 1);
    assert_eq!(fold.pre_bindings[0].slot, 1);
    assert_eq!(fold.acc_init, ArithIr::Local(1)); // seeded from the pre-binding
    assert!(v.ledger.all_equal && v.ledger.first_divergence.is_none());
    // 10 + (1+2+3) == 16.
    assert_eq!(eval_fold(&fold, &[], &[1.0, 2.0, 3.0], &[]), 16.0);
}

// ---- Positive: fidelity holds on the crucial edge arrays (explicit) ---------

#[test]
fn positive_fold_fidelity_on_edge_arrays_empty_nan_signed_zero_inf() {
    // The whole (array × scalar) corpus already proved bit-equality; re-confirm the
    // crucial edge arrays EXPLICITLY against the oracle, bit-for-bit: the empty
    // array, a NaN-containing array, a ±0-containing array, and a ±Inf-containing
    // array. Sum and product exercise + and *; both propagate NaN and are
    // signed-zero-aware exactly as JS is.
    let cases: &[(&str, &str)] = &[
        ("function sum(arr){ let s=0; for(const x of arr){ s=s+x; } return s; }", "sum"),
        ("function prod(arr){ let p=1; for(const x of arr){ p = p*x; } return p; }", "prod"),
    ];
    let edge_arrays: &[Vec<f64>] = &[
        vec![],                                      // empty
        vec![1.0, f64::NAN, 2.0],                    // NaN-containing
        vec![0.0, -0.0, 1.0],                        // ±0-containing
        vec![f64::INFINITY, f64::NEG_INFINITY, 1.0], // ±Inf-containing
        vec![-0.0, -0.0],                            // all -0
    ];
    for (js, name) in cases {
        let (_, fold) = verified_fold(js);
        for arr in edge_arrays {
            let ours = eval_fold(&fold, &[], arr, &[]);
            let arglist = js_array_literal(arr);
            let js_val = oracle_eval_call(js, name, &arglist).unwrap_or_else(|e| {
                panic!("oracle must return a number for {name}({arglist}): {e}")
            });
            assert!(
                same_js_number(js_val, ours),
                "{name}({arglist}): oracle={} eval_fold={}",
                projection_number_repr(js_val),
                projection_number_repr(ours)
            );
        }
    }
    // Pin the exact bit-level outcomes of the subtle corners, each matching the
    // oracle (checked above). SUM (seed +0): empty => +0; NaN propagates; ±Inf =>
    // NaN (Inf + -Inf).
    let (_, sum) =
        verified_fold("function sum(arr){ let s=0; for(const x of arr){ s=s+x; } return s; }");
    assert_eq!(eval_fold(&sum, &[], &[], &[]).to_bits(), 0.0f64.to_bits()); // empty => +0 seed
    assert!(eval_fold(&sum, &[], &[1.0, f64::NAN, 2.0], &[]).is_nan()); // NaN propagates
    assert!(eval_fold(&sum, &[], &[f64::INFINITY, f64::NEG_INFINITY, 1.0], &[]).is_nan()); // Inf+-Inf
    // PRODUCT is signed-zero-aware: prod([0, -0, 1]) == -0 (1*0=+0, +0*-0=-0,
    // -0*1=-0), a genuine -0 result matching the oracle bit-for-bit.
    let prod_js = "function prod(arr){ let p=1; for(const x of arr){ p = p*x; } return p; }";
    let (_, prod) = verified_fold(prod_js);
    assert_eq!(eval_fold(&prod, &[], &[0.0, -0.0, 1.0], &[]).to_bits(), (-0.0f64).to_bits());
    let jz = oracle_eval_call(prod_js, "prod", "[0, (-0), 1]").expect("oracle number");
    assert_eq!(jz.to_bits(), (-0.0f64).to_bits(), "oracle prod([0,-0,1]) must be -0");
    assert!(eval_fold(&prod, &[], &[], &[]) == 1.0); // empty product => the seed 1
}

// ---- Positive: the array corpus is deterministic and bounded ----------------

#[test]
fn fold_corpus_is_bounded_and_deterministic() {
    let arrays = build_array_corpus();
    // 1 empty + 18 singletons + 3 all-same + 2 ascending + 1 NaN + 1 ±0 + 1 ±Inf
    // + 1 mixed + 2 everyday == 30 arrays; includes the empty array.
    assert_eq!(arrays.len(), 30);
    assert!(arrays.iter().any(std::vec::Vec::is_empty), "corpus must include the empty array");
    assert!(arrays.iter().any(|a| a.iter().any(|v| v.is_nan())), "a NaN-containing array");
    assert!(
        arrays.iter().any(|a| a.iter().any(|v| v.to_bits() == (-0.0f64).to_bits())),
        "a -0-containing array"
    );
    assert!(arrays.iter().any(|a| a.iter().any(|v| v.is_infinite())), "an Inf-containing array");
    assert!(arrays.iter().any(|a| a.len() >= 8), "a longer (>=8) array");
    // Total corpus bounded for scalar_arity 0 and 1.
    assert_eq!(build_fold_corpus(0).len(), 30); // 30 arrays * 1 empty scalar tuple
    assert_eq!(build_fold_corpus(1).len(), 30 * 18); // 30 arrays * 18 scalar tuples
    assert!(build_fold_corpus(2).len() <= crate::fidelity::pin().fold_max_samples());
    // Determinism (compare by bit pattern, since the corpus contains NaN).
    let bits = |ss: Vec<Vec<f64>>| -> Vec<Vec<u64>> {
        ss.iter().map(|t| t.iter().map(|v| v.to_bits()).collect()).collect()
    };
    assert_eq!(bits(build_array_corpus()), bits(build_array_corpus()));
}

// ---- Negative: everything outside the exact fold shape refuses, emit nothing --

#[test]
fn negative_fold_while_loop() {
    // A `while` loop is not the single `for (const X of ARR)` fold => refuse.
    assert!(
        lower_and_verify("function w(arr){ let s=0; while(s<10){ s=s+1; } return s; }").is_err()
    );
}

#[test]
fn negative_fold_c_style_for_with_index_length() {
    // A C-style `for(let i=0;i<arr.length;i++)` is not a for-of fold; and it uses
    // `arr.length` / indexing. It refuses (no for-of => scalar path refuses the
    // `for` statement).
    assert!(
        lower_and_verify(
            "function cf(arr){ let s=0; for(let i=0;i<arr.length;i=i+1){ s=s+arr[i]; } return s; }"
        )
        .is_err()
    );
}

#[test]
fn negative_fold_index_and_length_no_loop() {
    // Indexing / `.length` with no loop: `arr` is a scalar param on the scalar path,
    // and `arr[0]` / `arr.length` are member access => refuse.
    match refusal("function il(arr){ return arr[0]+arr.length; }") {
        Refusal::UnsupportedConstruct { construct } => {
            assert!(construct.contains("member access"), "got {construct}");
        }
        other => panic!("expected UnsupportedConstruct(member access), got {other:?}"),
    }
}

#[test]
fn negative_fold_break_in_body() {
    // A `break` in the loop body: the body is a block with two statements (an `if`
    // and the assignment), not a single `ACC = <expr>` => refuse.
    match refusal(
        "function br(arr){ let s=0; for(const x of arr){ if(x<0) break; s=s+x; } return s; }",
    ) {
        Refusal::UnsupportedStatement { .. } => {}
        other => {
            panic!("expected UnsupportedStatement for a break in the loop body, got {other:?}")
        }
    }
}

#[test]
fn negative_fold_loop_body_binds_local() {
    // A local binding inside the loop body: the body has two statements => refuse.
    match refusal(
        "function lb(arr){ let s=0; for(const x of arr){ const y=x*2; s=s+y; } return s; }",
    ) {
        Refusal::UnsupportedStatement { .. } => {}
        other => {
            panic!("expected UnsupportedStatement for a binding in the loop body, got {other:?}")
        }
    }
}

#[test]
fn negative_fold_const_accumulator() {
    // A `const` accumulator cannot be reassigned in the loop => refuse (either the
    // parser rejects the const assignment, or our fold gate refuses the const decl).
    assert!(
        lower_and_verify("function ca(arr){ const s=0; for(const x of arr){ s=s+x; } return s; }")
            .is_err()
    );
}

#[test]
fn negative_fold_array_literal_iterable() {
    // for-of over an ARRAY LITERAL (not the array parameter): ARR is not a param
    // used as the iterable => refuse. (Also there is no array parameter at all.)
    assert!(
        lower_and_verify("function al(){ let s=0; for(const x of [1,2,3]){ s=s+x; } return s; }")
            .is_err()
    );
}

#[test]
fn negative_fold_iterates_over_scalar_or_nonfirst() {
    // for-of over a SCALAR param (not the first/array param): refuse. Here the
    // first param `arr` is unused as an iterable; the loop iterates `k`.
    match refusal("function fs(arr,k){ let s=0; for(const x of k){ s=s+x; } return s; }") {
        Refusal::UnsupportedStatement { .. } => {}
        other => panic!("expected UnsupportedStatement for a for-of over a scalar, got {other:?}"),
    }
}

#[test]
fn negative_fold_destructured_head() {
    // A destructuring for-of head `for (const [a,b] of arr)` => refuse.
    match refusal("function dh(arr){ let s=0; for(const [a,b] of arr){ s=s+a; } return s; }") {
        Refusal::UnsupportedStatement { .. } => {}
        other => {
            panic!("expected UnsupportedStatement for a destructured for-of head, got {other:?}")
        }
    }
}

#[test]
fn negative_fold_let_loop_var() {
    // A `let` loop variable (not `const X`) => refuse.
    match refusal("function lv(arr){ let s=0; for(let x of arr){ s=s+x; } return s; }") {
        Refusal::UnsupportedStatement { .. } => {}
        other => panic!("expected UnsupportedStatement for a `let` loop variable, got {other:?}"),
    }
}

#[test]
fn negative_fold_nested_loop() {
    // A nested for-of inside the loop body: the body is not a single assignment
    // (it is another for-of) => refuse.
    match refusal(
        "function nl(arr){ let s=0; for(const x of arr){ for(const y of arr){ s=s+y; } } return s; }",
    ) {
        Refusal::UnsupportedStatement { .. } => {}
        other => panic!("expected UnsupportedStatement for a nested loop, got {other:?}"),
    }
}

#[test]
fn negative_fold_boolean_step() {
    // A boolean fold: the accumulator is numeric but the step types to Bool
    // (`s > 0` compared) => a type error at `lower_num(step)`. (We do not model a
    // boolean accumulator.)
    match refusal("function bf(arr){ let s=0; for(const x of arr){ s = s > x; } return s; }") {
        Refusal::TypeError { .. } => {}
        other => panic!("expected TypeError for a boolean fold step, got {other:?}"),
    }
}

#[test]
fn negative_fold_return_uses_loop_var_out_of_scope() {
    // The return references the loop variable `x`, which is out of scope after the
    // loop => refuse as a free identifier.
    match refusal("function rx(arr){ let s=0; for(const x of arr){ s=s+x; } return x; }") {
        Refusal::UnsupportedConstruct { construct } => {
            assert!(construct.contains("free identifier"), "got {construct}");
        }
        other => panic!(
            "expected UnsupportedConstruct(free identifier) for out-of-scope loop var, got {other:?}"
        ),
    }
}

#[test]
fn negative_fold_array_param_used_as_number() {
    // The array parameter used as a numeric value (`arr + 1` in the return) refuses:
    // ARR is not a value expression, only the for-of iterable.
    match refusal("function au(arr){ let s=0; for(const x of arr){ s=s+x; } return arr + 1; }") {
        Refusal::UnsupportedConstruct { construct } => {
            assert!(construct.contains("free identifier"), "got {construct}");
        }
        other => panic!(
            "expected UnsupportedConstruct(free identifier) for array-as-number, got {other:?}"
        ),
    }
}

#[test]
fn negative_fold_helper_may_not_contain_loop() {
    // A for-of function that is NOT the last-declared (the fold must be the entry):
    // the helper `h` contains a loop => refuse.
    assert!(
        lower_and_verify(
            "function h(arr){ let s=0; for(const x of arr){ s=s+x; } return s; } function f(a){ return a+1; }"
        )
        .is_err()
    );
}

// ---- Positive: a fold as the entry, calling an earlier SCALAR helper ---------

#[test]
fn positive_fold_step_calls_scalar_helper() {
    // The fold entry calls a strictly-earlier scalar helper `dbl(x)=2x` in the
    // step: `s = s + dbl(x)` == 2 * sum. The helper is rendered as a free `fn`
    // before the fold, and the call resolves through the helper table.
    let v = verified(
        "function dbl(x){return x*2} function f(arr){ let s=0; for(const x of arr){ s = s + dbl(x); } return s; }",
    );
    let fold = v.fold.clone().expect("a fold entry");
    assert_eq!(v.functions.len(), 1); // one scalar helper
    assert_eq!(v.functions[0].name, "dbl");
    assert_eq!(
        v.rust_source,
        "fn dbl(p0: f64) -> f64 { p0 * 2.0 }\n\
         fn f(arr: &[f64]) -> f64 { let mut l1: f64 = 0.0; for &l2 in arr { l1 = l1 + dbl(l2); } l1 }"
    );
    // step: s + dbl(x) == Local(1) + Call{callee:0, [Local(2)]}.
    assert_eq!(
        fold.step,
        ArithIr::Add(
            Box::new(ArithIr::Local(1)),
            Box::new(ArithIr::Call { callee: 0, args: vec![ArithIr::Local(2)] }),
        )
    );
    assert!(v.ledger.all_equal && v.ledger.first_divergence.is_none());
    // 2*(1+2+3) == 12; via eval_fold with the helper table.
    assert_eq!(eval_fold(&fold, &v.functions, &[1.0, 2.0, 3.0], &[]), 12.0);
}

// ---- Ledger: a deliberately wrong fold lowering is CAUGHT --------------------

#[test]
fn fidelity_catches_wrong_fold_step() {
    // JS is `s = s + x` (sum). Feed a WRONG step `s - x` while eval keeps the source
    // as the oracle: on any array with a non-zero element the oracle (sum) and
    // eval_fold (with the wrong step) disagree, so the fidelity check refuses and
    // NOTHING is emitted.
    let js = "function sum(arr){ let s=0; for(const x of arr){ s=s+x; } return s; }";
    let (_, correct) = verified_fold(js);
    let mut wrong = correct.clone();
    wrong.step = ArithIr::Sub(Box::new(ArithIr::Local(1)), Box::new(ArithIr::Local(2)));
    match check_fidelity_fold(js, &[], &wrong) {
        Err(Refusal::FidelityDivergence { input, js: j, rust }) => {
            assert!(!input.is_empty());
            assert_ne!(j, rust, "a caught divergence must report differing values");
        }
        other => panic!("expected FidelityDivergence for a wrong fold step, got {other:?}"),
    }
    // Sanity anchor: the CORRECT step verifies, so the divergence is due to the swap.
    let led = check_fidelity_fold(js, &[], &correct)
        .expect("the correct fold step must verify bit-for-bit");
    assert!(led.all_equal && led.first_divergence.is_none());
}

#[test]
fn fidelity_catches_swapped_acc_and_loop_var() {
    // JS `axpy(arr,k){ s = s + k*x }`. Feed a WRONG step that swaps the accumulator
    // and loop-variable slots (`x + k*s` instead of `s + k*x`): on arrays/scalars
    // where these differ the oracle and eval_fold disagree => refuse.
    let js = "function axpy(arr,k){ let s=0; for(const x of arr){ s = s + k*x; } return s; }";
    let (_, correct) = verified_fold(js);
    let mut wrong = correct.clone();
    // acc is Local(2), loop var Local(3), k is Param(1). Swap acc<->loopvar.
    wrong.step = ArithIr::Add(
        Box::new(ArithIr::Local(3)),
        Box::new(ArithIr::Mul(Box::new(ArithIr::Param(1)), Box::new(ArithIr::Local(2)))),
    );
    match check_fidelity_fold(js, &[], &wrong) {
        Err(Refusal::FidelityDivergence { .. }) => {}
        other => panic!("expected FidelityDivergence for a swapped acc/loop-var, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// (7) ERASABLE-TYPESCRIPT front door — `lower_ts_and_verify` composes the
//     trust-ts-strip type-eraser with the existing JS lowering. Erasable TS
//     autoformalizes TRANSITIVELY: TS ≡ stripped-JS (the eraser's Node-
//     differential corpus gate) ∧ stripped-JS ≡ Rust (the delta ledger, over
//     the numeric corpus) — both hops bounded evidence, neither one proof. Type
//     annotations are ERASED and NEVER trusted as facts — the ledger judges the
//     stripped BEHAVIOR, not the TS types. Same bounded corpus honesty as the JS
//     path, one erasure hop earlier.
// ---------------------------------------------------------------------------

fn verified_ts(ts: &str) -> VerifiedLowering {
    match lower_ts_and_verify(ts) {
        Ok(v) => v,
        Err(e) => panic!("expected a verified TS lowering for {ts:?}, got refusal: {e:?}"),
    }
}

fn refusal_ts(ts: &str) -> Refusal {
    match lower_ts_and_verify(ts) {
        Ok(v) => panic!("expected a refusal for TS {ts:?}, got a lowering: {v:?}"),
        Err(e) => e,
    }
}

#[test]
fn ts_positive_add_types_erased_to_f64() {
    // The flagship: a typed TS `add` lowers to the SAME f64 Rust as untyped JS
    // `a+b` — the `: number` annotations are gone (erased, never trusted). The
    // ledger proves stripped-JS ≡ Rust bit-for-bit over the numeric corpus.
    let v = verified_ts("function add(a: number, b: number): number { return a + b; }");
    assert_eq!(v.rust_source, "fn add(p0: f64, p1: f64) -> f64 { p0 + p1 }");
    assert_eq!(v.ir, ArithIr::Add(Box::new(ArithIr::Param(0)), Box::new(ArithIr::Param(1))));
    assert!(v.ledger.all_equal && v.ledger.first_divergence.is_none());
    assert!(v.ledger.samples_checked > 0);
}

#[test]
fn ts_positive_square() {
    let v = verified_ts("function sq(x: number): number { return x * x; }");
    assert_eq!(v.rust_source, "fn sq(p0: f64) -> f64 { p0 * p0 }");
    assert!(v.ledger.all_equal && v.ledger.first_divergence.is_none());
}

#[test]
fn ts_positive_typed_local_binding() {
    // A typed local `const t: number = a*a;` — the `: number` on the binding is
    // erased; the SSA local lowers exactly as the untyped JS would.
    let v = verified_ts("function f(a: number): number { const t: number = a * a; return t + 1; }");
    assert_eq!(v.rust_source, "fn f(p0: f64) -> f64 { let l1: f64 = p0 * p0; l1 + 1.0 }");
    assert!(v.ledger.all_equal && v.ledger.first_divergence.is_none());
}

#[test]
fn ts_positive_multi_fn_module() {
    // A typed multi-function module composes exactly as the untyped JS module:
    // `sq` is a helper called twice by the entry `h`. Types erased throughout.
    let v = verified_ts(
        "function sq(x: number): number { return x*x; } \
         function h(a: number, b: number): number { return sq(a) + sq(b); }",
    );
    assert_eq!(
        v.rust_source,
        "fn sq(p0: f64) -> f64 { p0 * p0 }\n\
         fn h(p0: f64, p1: f64) -> f64 { sq(p0) + sq(p1) }"
    );
    assert_eq!(v.functions.len(), 2);
    assert!(v.ledger.all_equal && v.ledger.first_divergence.is_none());
}

#[test]
fn ts_positive_array_fold() {
    // A typed array-fold: `arr: number[]` (the `number[]` annotation erased —
    // the array is detected as the for-of iterable, exactly as untyped JS), and a
    // typed accumulator `let s: number = 0;`. Renders the same &[f64] fold.
    let v = verified_ts(
        "function sum(arr: number[]): number { let s: number = 0; for (const x of arr) { s = s + x; } return s; }",
    );
    assert_eq!(
        v.rust_source,
        "fn sum(arr: &[f64]) -> f64 { let mut l1: f64 = 0.0; for &l2 in arr { l1 = l1 + l2; } l1 }"
    );
    let fold = v.fold.clone().expect("a typed array-fold must lower to a FoldFn");
    assert_eq!(fold.name, "sum");
    assert!(v.ledger.all_equal && v.ledger.first_divergence.is_none());
    assert_eq!(eval_fold(&fold, &[], &[1.0, 2.0, 3.0], &[]), 6.0);
}

#[test]
fn ts_positive_math_abs() {
    // A typed function using an allow-listed Math.* builtin. `Math.abs` is a
    // direct-map op: renders `p0.abs()`, bit-identical to the oracle's `n.abs()`.
    let v = verified_ts("function n(a: number): number { return Math.abs(a); }");
    assert_eq!(v.rust_source, "fn n(p0: f64) -> f64 { p0.abs() }");
    assert!(v.ledger.all_equal && v.ledger.first_divergence.is_none());
}

#[test]
fn ts_negative_enum_is_non_erasable() {
    // An `enum` is NOT pure type-erasure (it has runtime semantics — a forward /
    // reverse-mapped object), so trust-ts-strip's erasable-strip REFUSES it. We
    // surface that as NonErasableTypeScript and emit nothing — we do NOT attempt
    // the non-erasable `transform` lowering (out of the M4-TS fragment).
    let r = refusal_ts("enum E { A, B } function f(a: number): number { return a; }");
    match r {
        Refusal::NonErasableTypeScript { reason } => {
            assert!(!reason.is_empty(), "the eraser must carry a fail-closed reason");
        }
        other => panic!("expected NonErasableTypeScript for an enum, got {other:?}"),
    }
}

#[test]
fn ts_negative_namespace_is_non_erasable() {
    // A `namespace` likewise has runtime semantics and is NOT pure erasure — the
    // erasable-strip refuses it, surfaced as NonErasableTypeScript.
    let r = refusal_ts(
        "namespace N { export const x = 1; } function f(a: number): number { return a; }",
    );
    match r {
        Refusal::NonErasableTypeScript { .. } => {}
        other => panic!("expected NonErasableTypeScript for a namespace, got {other:?}"),
    }
}

#[test]
fn ts_negative_stripped_behavior_out_of_fragment() {
    // Erasable TS whose STRIPPED behavior is out-of-fragment: the `: string`
    // return annotation is erased (never trusted), and the body strips to
    // `return a + "x";` — a string concatenation. The strip SUCCEEDS (this is
    // pure erasure), but the JS path then refuses the string literal as
    // UnsupportedConstruct. The ledger judges the stripped BEHAVIOR, not the
    // (erased) type annotation.
    let r = refusal_ts("function f(a: number): string { return a + \"x\"; }");
    assert!(
        !matches!(r, Refusal::NonErasableTypeScript { .. }),
        "the strip must SUCCEED (pure erasure); the JS path is what refuses"
    );
    match r {
        Refusal::UnsupportedConstruct { .. } => {}
        other => panic!("expected UnsupportedConstruct via the JS path, got {other:?}"),
    }
}

// ===========================================================================
// EXTENDED FRAGMENT (M4 floor increment 8): JS BITWISE operators `| & ^ ~ << >>
// >>>` over ToInt32 / ToUint32. Unlike Math.pow (a TRANSCENDENTAL that refuses —
// f64::powf != V8, and the same-primitive oracle-check is a tautology), the
// bitwise ops are built on ToInt32/ToUint32, which are EXACT integer functions —
// a precise modular definition EVERY correct implementation (V8, the interp, the
// rendered Rust) computes bit-identically. So even though the fidelity check
// compares eval against the interp oracle (which also does ToInt32), the check is
// SOUND (validation, not tautology), exactly as for +,-,*,/. Each positive lowers
// AND verifies bit-for-bit against the oracle over the corpus (NaN / ±Inf / ±0 /
// f64::MAX included). Every negative refuses, emitting nothing.
// ===========================================================================

// ---- Positive: bitwise functions lower and verify bit-equal to the oracle ---

#[test]
fn positive_bitwise_or_render_and_ledger() {
    let v = verified("function orr(a,b){return a|b}");
    assert_eq!(
        v.rust_source,
        format!(
            "{HELPER_TO_UINT32}\n{HELPER_TO_INT32}\n\
             fn orr(p0: f64, p1: f64) -> f64 {{ ((__js_to_int32(p0) | __js_to_int32(p1)) as f64) }}"
        )
    );
    assert_eq!(v.ir, ArithIr::BitOr(Box::new(ArithIr::Param(0)), Box::new(ArithIr::Param(1))));
    assert!(v.ledger.all_equal && v.ledger.first_divergence.is_none());
    assert!(v.ledger.samples_checked > 0);
    // 5 | 2 == 7; 6 | 1 == 7.
    assert_eq!(eval_module(&v.functions, v.entry, &[5.0, 2.0]), 7.0);
    assert_eq!(eval_module(&v.functions, v.entry, &[6.0, 1.0]), 7.0);
}

#[test]
fn positive_bitwise_truncise_idiom_x_or_zero() {
    // The `x | 0` truncate-to-int32 idiom — the task's flagship. Only __js_to_int32
    // (dragging in its __js_to_uint32 dependency) is prepended.
    let v = verified("function truncise(a){return a|0}");
    assert_eq!(
        v.rust_source,
        format!(
            "{HELPER_TO_UINT32}\n{HELPER_TO_INT32}\n\
             fn truncise(p0: f64) -> f64 {{ ((__js_to_int32(p0) | __js_to_int32(0.0)) as f64) }}"
        )
    );
    assert!(v.ledger.all_equal && v.ledger.first_divergence.is_none());
    // truncation toward zero: 3.9|0 == 3, -3.9|0 == -3.
    assert_eq!(eval_module(&v.functions, v.entry, &[3.9]), 3.0);
    assert_eq!(eval_module(&v.functions, v.entry, &[-3.9]), -3.0);
    // NaN|0 == 0, Infinity|0 == 0 (ToInt32 of NaN/Inf is 0).
    assert_eq!(eval_module(&v.functions, v.entry, &[f64::NAN]), 0.0);
    assert_eq!(eval_module(&v.functions, v.entry, &[f64::INFINITY]), 0.0);
    // boundary wrap: 2147483647|0 == itself; 2147483648|0 wraps to -2147483648;
    // 4294967296|0 (== 2^32) wraps to 0.
    assert_eq!(eval_module(&v.functions, v.entry, &[2_147_483_647.0]), 2_147_483_647.0);
    assert_eq!(eval_module(&v.functions, v.entry, &[2_147_483_648.0]), -2_147_483_648.0);
    assert_eq!(eval_module(&v.functions, v.entry, &[4_294_967_296.0]), 0.0);
}

#[test]
fn positive_bitwise_ushr_unsigned_result() {
    // `a >>> 0` is the canonical UNSIGNED coercion: -1 >>> 0 === 4294967295 (a u32,
    // NOT -1). Only __js_to_uint32 is prepended (>>> never needs the signed int32).
    let v = verified("function ushr(a){return a>>>0}");
    assert_eq!(
        v.rust_source,
        format!(
            "{HELPER_TO_UINT32}\n\
             fn ushr(p0: f64) -> f64 {{ ((__js_to_uint32(p0).wrapping_shr(__js_to_uint32(0.0) & 31)) as f64) }}"
        )
    );
    assert!(v.ledger.all_equal && v.ledger.first_divergence.is_none());
    // The signed-vs-unsigned trap: -1 >>> 0 == 4294967295 (unsigned), NOT -1.
    assert_eq!(eval_module(&v.functions, v.entry, &[-1.0]), 4_294_967_295.0);
    assert_eq!(eval_module(&v.functions, v.entry, &[0.0]), 0.0);
    // -2 >>> 0 == 4294967294.
    assert_eq!(eval_module(&v.functions, v.entry, &[-2.0]), 4_294_967_294.0);
}

#[test]
fn positive_bitwise_shl_shift_count_mod_32() {
    // The shift count is taken mod 32 (ToUint32(b) & 31): 1<<32 == 1, 1<<33 == 2,
    // 1<<0 == 1. `a<<b` needs both helpers (int32 for a, uint32 for the count).
    let v = verified("function shl(a,b){return a<<b}");
    assert_eq!(
        v.rust_source,
        format!(
            "{HELPER_TO_UINT32}\n{HELPER_TO_INT32}\n\
             fn shl(p0: f64, p1: f64) -> f64 {{ ((__js_to_int32(p0).wrapping_shl(__js_to_uint32(p1) & 31)) as f64) }}"
        )
    );
    assert!(v.ledger.all_equal && v.ledger.first_divergence.is_none());
    assert_eq!(eval_module(&v.functions, v.entry, &[1.0, 32.0]), 1.0);
    assert_eq!(eval_module(&v.functions, v.entry, &[1.0, 33.0]), 2.0);
    assert_eq!(eval_module(&v.functions, v.entry, &[1.0, 0.0]), 1.0);
    assert_eq!(eval_module(&v.functions, v.entry, &[1.0, 31.0]), -2_147_483_648.0); // 1<<31 wraps to i32::MIN
}

#[test]
fn positive_bitwise_not() {
    // `~a` == !ToInt32(a): ~0 == -1, ~5 == -6.
    let v = verified("function notb(a){return ~a}");
    assert_eq!(
        v.rust_source,
        format!(
            "{HELPER_TO_UINT32}\n{HELPER_TO_INT32}\n\
             fn notb(p0: f64) -> f64 {{ ((!__js_to_int32(p0)) as f64) }}"
        )
    );
    assert_eq!(v.ir, ArithIr::BitNot(Box::new(ArithIr::Param(0))));
    assert!(v.ledger.all_equal && v.ledger.first_divergence.is_none());
    assert_eq!(eval_module(&v.functions, v.entry, &[0.0]), -1.0);
    assert_eq!(eval_module(&v.functions, v.entry, &[5.0]), -6.0);
    // ~(-1) == 0, ~NaN == -1 (ToInt32(NaN)=0, !0=-1).
    assert_eq!(eval_module(&v.functions, v.entry, &[-1.0]), 0.0);
    assert_eq!(eval_module(&v.functions, v.entry, &[f64::NAN]), -1.0);
}

#[test]
fn positive_bitwise_and_xor_composed() {
    // A composed bitwise expression `(a&b)^c` — nested ToInt32 casts, validated by
    // the ledger bit-for-bit.
    let v = verified("function andxor(a,b,c){return (a&b)^c}");
    assert_eq!(
        v.ir,
        ArithIr::BitXor(
            Box::new(ArithIr::BitAnd(Box::new(ArithIr::Param(0)), Box::new(ArithIr::Param(1)))),
            Box::new(ArithIr::Param(2)),
        )
    );
    assert!(v.ledger.all_equal && v.ledger.first_divergence.is_none());
    // (6 & 3) ^ 5 == 2 ^ 5 == 7.
    assert_eq!(eval_module(&v.functions, v.entry, &[6.0, 3.0, 5.0]), 7.0);
    // (12 & 10) ^ 1 == 8 ^ 1 == 9.
    assert_eq!(eval_module(&v.functions, v.entry, &[12.0, 10.0, 1.0]), 9.0);
}

#[test]
fn positive_bitwise_signed_shift() {
    // `a >> 1` is an ARITHMETIC (sign-propagating) shift: -1 >> 0 == -1 (NOT the
    // unsigned 4294967295 that >>> gives); -8 >> 1 == -4.
    let v = verified("function signed_shift(a){return a>>1}");
    assert_eq!(
        v.rust_source,
        format!(
            "{HELPER_TO_UINT32}\n{HELPER_TO_INT32}\n\
             fn signed_shift(p0: f64) -> f64 {{ ((__js_to_int32(p0).wrapping_shr(__js_to_uint32(1.0) & 31)) as f64) }}"
        )
    );
    assert!(v.ledger.all_equal && v.ledger.first_divergence.is_none());
    assert_eq!(eval_module(&v.functions, v.entry, &[-8.0]), -4.0);
    assert_eq!(eval_module(&v.functions, v.entry, &[13.0]), 6.0);
    // -1 >> 1 == -1 (sign bit propagates).
    assert_eq!(eval_module(&v.functions, v.entry, &[-1.0]), -1.0);
}

#[test]
fn positive_bitwise_hashy_composed_with_binding() {
    // A realistic hash-ish mixer combining a shift, subtraction, addition, a local
    // binding, and the `| 0` int32-truncate idiom: `h = (a<<5) - a + b; return h|0`.
    let v = verified("function hashy(a,b){ const h = (a<<5) - a + b; return h | 0; }");
    assert!(v.rust_source.contains("let l2: f64 = ((__js_to_int32(p0).wrapping_shl(__js_to_uint32(5.0) & 31)) as f64) - p0 + p1;"));
    assert!(v.rust_source.contains("((__js_to_int32(l2) | __js_to_int32(0.0)) as f64)"));
    assert!(v.ledger.all_equal && v.ledger.first_divergence.is_none());
    // (5<<5) - 5 + 3 == 160 - 5 + 3 == 158; |0 == 158.
    assert_eq!(eval_module(&v.functions, v.entry, &[5.0, 3.0]), 158.0);
    // (1<<5) - 1 + 0 == 31.
    assert_eq!(eval_module(&v.functions, v.entry, &[1.0, 0.0]), 31.0);
}

// ---- Positive: every trap matches the oracle bit-for-bit (explicit) ---------

#[test]
fn positive_bitwise_traps_match_oracle_bit_for_bit() {
    // The task's trap list — each proven EQUAL between our eval and the interp
    // oracle AND equal to the ECMA-262 expected value, bit-for-bit. These pin the
    // exact-integer semantics that make the bitwise ops safe to ship (unlike the
    // transcendental Math.pow). Format: (source, name, inputs, expected f64).
    let traps: &[(&str, &str, &[f64], f64)] = &[
        // Unsigned vs signed shift.
        ("function u(a){return a>>>0}", "u", &[-1.0], 4_294_967_295.0), // -1>>>0 === 4294967295
        ("function s(a){return a>>0}", "s", &[-1.0], -1.0),             // -1>>0  === -1
        // Shift count mod 32.
        ("function f(a,b){return a<<b}", "f", &[1.0, 32.0], 1.0), // 1<<32 === 1
        ("function f(a,b){return a<<b}", "f", &[1.0, 33.0], 2.0), // 1<<33 === 2
        ("function f(a,b){return a<<b}", "f", &[1.0, 0.0], 1.0),  // 1<<0  === 1
        // ToInt32 of NaN / ±Infinity / ±0 is 0.
        ("function f(a){return a|0}", "f", &[f64::NAN], 0.0), // NaN|0 === 0
        ("function f(a){return a|0}", "f", &[f64::INFINITY], 0.0), // Infinity|0 === 0
        ("function f(a){return a|0}", "f", &[f64::NEG_INFINITY], 0.0), // -Infinity|0 === 0
        // Truncation toward zero.
        ("function f(a){return a|0}", "f", &[3.9], 3.0), // 3.9|0 === 3
        ("function f(a){return a|0}", "f", &[-3.9], -3.0), // -3.9|0 === -3
        // Boundary wrap.
        ("function f(a){return a|0}", "f", &[2_147_483_647.0], 2_147_483_647.0), // 2147483647|0 === 2147483647
        ("function f(a){return a|0}", "f", &[2_147_483_648.0], -2_147_483_648.0), // 2147483648|0 === -2147483648
        ("function f(a){return a|0}", "f", &[4_294_967_296.0], 0.0), // 4294967296|0 === 0
        // Large-magnitude finite (ToUint32 modular reduction is exact via fmod).
        ("function u(a){return a>>>0}", "u", &[4_294_967_297.0], 1.0), // (2^32+1)>>>0 === 1
        // Bitwise NOT.
        ("function n(a){return ~a}", "n", &[0.0], -1.0), // ~0 === -1
        ("function n(a){return ~a}", "n", &[5.0], -6.0), // ~5 === -6
    ];
    for (src, name, input, expected) in traps {
        let v = verified(src);
        let ours = eval_module(&v.functions, v.entry, input);
        let js = oracle_eval(src, name, input)
            .unwrap_or_else(|e| panic!("oracle must return a number for {name}({input:?}): {e}"));
        // eval == oracle (the honesty core), and both == the ECMA expected value.
        assert!(
            same_js_number(js, ours),
            "{src} on {input:?}: oracle={} eval={}",
            projection_number_repr(js),
            projection_number_repr(ours)
        );
        assert_eq!(
            ours.to_bits(),
            expected.to_bits(),
            "{src} on {input:?}: eval={} expected={}",
            projection_number_repr(ours),
            projection_number_repr(*expected)
        );
    }
}

// ---- Negative: a non-numeric or BigInt operand refuses ----------------------

#[test]
fn negative_bitwise_bool_operand() {
    // A boolean operand to a bitwise op is a type error (we do NOT coerce
    // ToInt32(bool) — the fragment never coerces). `(a<b)|1` is Bool | Num.
    match refusal("function bo(a,b){return (a<b)|1}") {
        Refusal::TypeError { .. } => {}
        other => panic!("expected TypeError for a Bool bitwise operand, got {other:?}"),
    }
}

#[test]
fn negative_bitwise_bigint_operand() {
    // A BigInt operand `1n` refuses at the operand as a BigInt literal (a bitwise op
    // over a BigInt is never lowered — it can never become a BigInt-coercing route).
    match refusal("function bi(a){return a|1n}") {
        Refusal::UnsupportedConstruct { construct } => {
            assert!(construct.contains("BigInt literal"), "got {construct}");
        }
        other => {
            panic!("expected UnsupportedConstruct(BigInt) for a BigInt operand, got {other:?}")
        }
    }
}

// ---- Ledger: a deliberately WRONG bitwise lowering is CAUGHT -----------------

#[test]
fn fidelity_catches_wrong_shift_kind() {
    // JS is `a >>> 0` (LOGICAL / unsigned shift). Feed a WRONG IR using `Shr` (the
    // ARITHMETIC / signed shift) instead: on a == -1 the oracle (>>> == 4294967295)
    // and eval (>> == -1) disagree, so the fidelity check refuses and NOTHING is
    // emitted. This is exactly the "render >> where source is >>>" defect the task
    // asks to catch, exercised on -1 >>> 0.
    let src = "function u(a){return a>>>0}";
    let wrong = ArithIr::Shr(Box::new(ArithIr::Param(0)), Box::new(ArithIr::Lit(0.0)));
    match check_fidelity(src, "u", &[], &wrong, 1) {
        Err(Refusal::FidelityDivergence { input, js, rust }) => {
            assert_eq!(input.len(), 1);
            assert_ne!(js, rust, "a caught divergence must report differing values");
        }
        other => panic!("expected FidelityDivergence for a wrong shift kind, got {other:?}"),
    }
    // Sanity anchor: the CORRECT UShr lowering verifies bit-for-bit, so the
    // divergence above is due to the wrong shift kind, not a spurious failure.
    let right = ArithIr::UShr(Box::new(ArithIr::Param(0)), Box::new(ArithIr::Lit(0.0)));
    let led = check_fidelity(src, "u", &[], &right, 1)
        .expect("the correct a>>>0 lowering must verify bit-for-bit");
    assert!(led.all_equal && led.first_divergence.is_none());
}

#[test]
fn fidelity_catches_dropped_toint32_via_naive_shift() {
    // A subtler wrong lowering that DROPS the unsigned semantics: JS `a >>> 0` on a
    // negative input must be unsigned (4294967295 for -1), but a lowering that used
    // the signed int32 for the receiver (Shr) yields -1. The oracle catches it — the
    // proof that ToInt32/ToUint32 must be implemented EXACTLY, or the lowering
    // refuses. (Companion to the above; asserts the -1 >>> 0 trap specifically.)
    let src = "function u(a){return a>>>0}";
    let v = verified(src);
    let ours = eval_module(&v.functions, v.entry, &[-1.0]);
    let js = oracle_eval(src, "u", &[-1.0]).expect("oracle number");
    assert_eq!(ours, 4_294_967_295.0, "our -1>>>0 must be the unsigned 4294967295");
    assert!(same_js_number(js, ours), "oracle and eval must agree on -1>>>0");
    // The naive "signed" answer (what dropping ToUint32 would give) is -1 — proven
    // to DIVERGE from the oracle, so such a lowering could never verify.
    let naive_signed = -1.0_f64;
    assert!(!same_js_number(js, naive_signed), "the naive signed -1 must diverge from the oracle");
}
