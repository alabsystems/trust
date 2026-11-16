//! TINV step 0(b) PROBE (docs/design/2026-10-04-type-invariant-tinv.md §6): which of the
//! obligation shapes a type-invariant mint would ask the Clean kernel for does `certify_vc`
//! certify today? Each VC is a VIOLATION (satisfiable iff the property fails); a certificate
//! means the kernel accepted its refutation. The weakened twins drop one premise and must
//! never certify (they are satisfiable).
//!
//! MEASURED 2026-10-04: only (a) certified. 2026-10-05: (c) certifies since the Farkas lane
//! tightens a strict atom to `a + 1 ≤ b` instead of weakening it; (b) (product congruence)
//! and (d) (nonlinear) do not. The design doc's §9 records what that means for TINV. This test asserts only the soundness half (the weakened
//! twins); the positive outcomes are printed, so a new recognizer turns nothing red.
use trust_certify::certify_vc;
use trust_types::{Formula as F, Sort, SourceSpan, VcKind, VerificationCondition};

fn iv(n: &str) -> F {
    F::Var(n.to_string(), Sort::Int)
}
fn b(f: F) -> Box<F> {
    Box::new(f)
}
fn vc(name: &str, formula: F) -> VerificationCondition {
    VerificationCondition {
        kind: VcKind::Postcondition,
        function: format!("tinv_probe::{name}").into(),
        location: SourceSpan::default(),
        formula,
        contract_metadata: None,
        obligation: None,
    }
}
fn eq(a: F, c: F) -> F {
    F::Eq(b(a), b(c))
}
fn mul(a: F, c: F) -> F {
    F::Mul(b(a), b(c))
}
fn nonneg(n: &str) -> F {
    F::Ge(b(iv(n)), b(F::Int(0)))
}

/// (a) establish at a constructor: `len = c * r` makes `len == c * r`.
fn establish() -> F {
    F::And(vec![
        eq(iv("len"), mul(iv("c"), iv("r"))),
        F::Not(b(eq(iv("len"), mul(iv("c"), iv("r"))))),
    ])
}
/// (b) preserve through a mutator that keeps the three fields: `len1 = len0`, `c1 = c0`, `r1 = r0`.
fn preserve_product(keep_rows: bool) -> F {
    let mut v = vec![
        eq(iv("len0"), mul(iv("c0"), iv("r0"))),
        eq(iv("len1"), iv("len0")),
        eq(iv("c1"), iv("c0")),
    ];
    if keep_rows {
        v.push(eq(iv("r1"), iv("r0")));
    }
    v.push(F::Not(b(eq(iv("len1"), mul(iv("c1"), iv("r1"))))));
    F::And(v)
}
/// (c) json `Parser`: `i0 <= n`, the guard `i0 < n`, `i1 = i0 + 1` keep `i1 <= n`.
fn preserve_le(guarded: bool) -> F {
    let mut v =
        vec![F::Le(b(iv("i0")), b(iv("n"))), eq(iv("i1"), F::Add(b(iv("i0")), b(F::Int(1))))];
    if guarded {
        v.push(F::Lt(b(iv("i0")), b(iv("n"))));
    }
    v.push(F::Not(b(F::Le(b(iv("i1")), b(iv("n"))))));
    F::And(v)
}
/// (d) the nonlinear USE: `len == c*r`, `x < c`, `y < r` give `y*c + x < len`.
fn use_index(bounded_y: bool) -> F {
    let mut v = vec![
        eq(iv("len"), mul(iv("c"), iv("r"))),
        nonneg("x"),
        nonneg("y"),
        nonneg("c"),
        nonneg("r"),
        F::Lt(b(iv("x")), b(iv("c"))),
    ];
    if bounded_y {
        v.push(F::Lt(b(iv("y")), b(iv("r"))));
    }
    v.push(F::Ge(b(F::Add(b(mul(iv("y"), iv("c"))), b(iv("x")))), b(iv("len"))));
    F::And(v)
}

fn report(name: &str, f: F) -> bool {
    let certified = certify_vc(&vc(name, f)).is_some();
    eprintln!("TINV-0b {name}: {}", if certified { "CERTIFIED" } else { "not certified" });
    certified
}

#[test]
fn probe() {
    let results = [
        ("a_establish", report("a_establish", establish())),
        ("b_preserve_product", report("b_preserve_product", preserve_product(true))),
        ("c_preserve_le", report("c_preserve_le", preserve_le(true))),
        ("d_use_index", report("d_use_index", use_index(true))),
    ];
    // The weakened twins are satisfiable: no certificate may exist for them.
    assert!(!report("b_weak", preserve_product(false)));
    assert!(!report("c_weak", preserve_le(false)));
    assert!(!report("d_weak", use_index(false)));
    eprintln!("TINV-0b summary: {results:?}");
}
