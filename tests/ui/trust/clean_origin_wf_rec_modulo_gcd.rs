//@ needs-trust-verify
//@ run-pass
//@ compile-flags: -Z trust-verify=off
//@ dont-check-compiler-stderr
//! **§R8 ACCEPTANCE — the TEXTBOOK MODULO `gcd` RUNS FROM RUST.**
//!
//! ```text
//! def gcd (a b : Nat) : Nat := if h : 0 < b then gcd b (a % b) else a
//! termination_by b + a * 0
//! ```
//!
//! This is the design doc's ratified acceptance example in the spelling the doc
//! actually names — Euclid's algorithm, one guard, one self-call, the remainder
//! in the recursive argument — emitted, gate-verified and called from Rust
//! below.
//!
//! # What is different from `clean_origin_wf_rec_gcd.rs`
//!
//! **There is no fuel wrapper.** R3b's fixture gate-verifies a THREE-argument
//! fuelled loop `gcdF` and reaches a two-argument surface through an ordinary
//! Rust function that supplies `a + 2b` — so the two-argument `gcd` there
//! carries no proof claim. Here the gate-verified object IS the two-argument
//! `gcd`, and `main` calls it directly. The recursion also terminates in
//! Euclid's number of steps rather than running `a + 2b` frames to a fixed
//! point, which is why the rows below can afford much larger inputs.
//!
//! # The refusal this fixture's predecessor cites is NOT the one that moved
//!
//! `clean_origin_wf_rec_gcd.rs` records that the modulo form was refused
//! because a SYMBOLIC divisor is refused on purpose: Clean's `.mod` is TOTAL
//! where Rust's `%` PANICS, and the faithfulness gate is blind to that
//! divergence because the panic lives in MIR the kernel never sees
//! (`fa788aab89`). **That reasoning is correct and unchanged AT A MACHINE
//! WIDTH**, where the emitted operation is an `Rvalue::BinaryOp(Rem)` carrying
//! rustc's zero-divisor `Assert`. `control_21` (h) pins that refusal still
//! firing, and `r8_nat_mod_probes` q6 re-measures the divergence itself.
//!
//! It was over-general in one precise way: it generalised a `UInt{N}` finding
//! to `Nat`. At the bignum carrier the emitted operation is not the `%`
//! primitive at all — it is `Call(trust_bignum::Nat::rem, [&a, &b])`,
//! `TemplateTerminator` has no `Assert` variant, and `Nat::rem` returns the
//! DIVIDEND at a zero divisor (Lean's `Nat.mod_zero`). There is no emitted
//! panic path here to make unreachable.
//!
//! # WHAT CARRIES THE CLAIM — read this before citing the fixture
//!
//! **Not panic-freedom, because there is no panic.** The claim that replaces it
//! is TOTALITY AGREEMENT of the carrier, and it is *not* a kernel judgment
//! about the emitted code: the identification `a % b ≡ Nat.mod a b` is
//! discriminating about the VALUE (`r8_nat_mod_probes` q1 refuses the
//! `Nat.div` sibling, the swapped operands and the sub/add/mul twins) but it is
//! VACUOUS at an open dividend — `∀ a, a % 0 = a` by `rfl` is REFUSED, q2. The
//! zero case is carried by `trust-bignum`'s kernel-differential test, which
//! reduces `Nat.mod` in the REAL Clean `TypeChecker` at a zero divisor and
//! asserts the runtime agrees, plus the `PrimitiveCallee` TCB row. This is no
//! NEW kind of trust: `nat.sub` already rests on exactly it, and that row is
//! what makes the older `gcd` fixture run.
//!
//! **The obligation the compiler DOES discharge is the DECREASE.** `a % b < b`
//! needs `0 < b`; the textbook `dite` binds exactly that as `h`, and
//! `Nat.mod_lt … h` is visibly in the elaborated term (q4). Its undischarged
//! cases are refused: a guard on the WRONG value, a guard that does NOT
//! DOMINATE the division, and no guard at all (`control_21` (f), and q5).
//!
//! One consequence to state rather than inherit silently: because the decrease
//! proof is BORROWED from side A, this binary's TERMINATION now depends on
//! `Nat::rem` genuinely satisfying `a % b < b` at runtime — not merely on its
//! value being right. The value half is the differential test; the bound half
//! is `checked_div_rem`'s pinned `r < other` postcondition. The `nat.mod` row
//! says so.
//!
//! `Nat.gcd` is ABSENT from the prelude (`gcd_final_probes` n1), so there is no
//! prelude gcd to state agreement with — which is why `main` checks the
//! DEFINING PROPERTY in ordinary Rust rather than only comparing literals.

extern crate trust_bignum;

clean {
    def gcd (a b : Nat) : Nat := if h : 0 < b then gcd b (a % b) else a
    termination_by b + a * 0
}

fn nat(value: u64) -> trust_bignum::Nat {
    trust_bignum::Nat::from_u64(value)
}

/// The verified object itself, at `u64` for convenience. **No fuel, no
/// wrapper arithmetic** — this forwards to the emitted two-argument recursion
/// and nothing else.
fn g(a: u64, b: u64) -> u64 {
    gcd(nat(a), nat(b)).to_u64().expect("a gcd of two u64 fits in u64")
}

/// The reference Euclid, in ordinary Rust. Used only to CHECK the emitted
/// answer on inputs no literal table mentions.
fn reference(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        let r = a % b;
        a = b;
        b = r;
    }
    a
}

fn main() {
    // ── THE NAMED ROWS, each also a kernel decision (r8_nat_mod_probes q4,
    //    where the same values are reduced by the kernel with refuting twins).
    for (a, b, expected) in
        [(12u64, 18u64, 6u64), (18, 12, 6), (270, 192, 6), (7, 13, 1), (0, 5, 5), (5, 0, 5)]
    {
        assert_eq!(
            g(a, b),
            expected,
            "gcd({a}, {b}) must compute {expected} through the EMITTED well-founded \
             recursion over the total `Nat` remainder"
        );
    }

    // ── THE ZERO DIVISOR, REACHED FOR REAL AND NOT ONLY REASONED ABOUT.
    //
    // This is the row the whole landing turns on, so it is executed rather than
    // argued. `gcd(a, 0)` takes the ELSE arm and returns `a` without dividing,
    // which is the guard doing its job. But the emitted `Nat::rem` is total
    // anyway, and `b == 0` is exactly the input that would panic if this lane
    // had emitted Rust's `%` on a machine word. Nothing here panics.
    for a in [0u64, 1, 5, 42, 1_000_000_007] {
        assert_eq!(g(a, 0), a, "gcd({a}, 0) must return {a} through the guard's else arm");
    }
    // And the divisor reaching zero MID-RECURSION, which is how every one of
    // these terminates: the last step before the else arm has `a % b == 0`, so
    // the next frame is called with a zero second argument.
    assert_eq!(g(6, 6), 6, "equal inputs step to (6, 0) and then take the else arm");
    assert_eq!(g(0, 0), 0, "the doubly-degenerate pair must terminate, not divide by zero");

    // ── THE INDEPENDENT CHECK, so the rows above are a DECISION and not a
    //    restatement of literals typed here. A body that returned an argument,
    //    or A common divisor rather than the GREATEST, is caught on inputs the
    //    tables never mention.
    for (a, b) in [
        (12u64, 18u64),
        (270, 192),
        (7, 13),
        (48, 18),
        (99, 33),
        (17, 5),
        (1, 1),
        (13, 13),
        (1071, 462),
        (123_456, 7_890),
        (4_294_967_296, 65_536),
    ] {
        let got = g(a, b);
        assert_eq!(
            got,
            reference(a, b),
            "gcd({a}, {b}) must agree with the reference Euclid"
        );
        if got != 0 {
            assert_eq!(a % got, 0, "gcd({a}, {b}) = {got} must DIVIDE {a}");
            assert_eq!(b % got, 0, "gcd({a}, {b}) = {got} must DIVIDE {b}");
        }
        // …and it must be the GREATEST. The half a body returning `1`, or any
        // smaller common divisor, fails. Bounded so the fixture stays cheap.
        let cap = if a == 0 {
            b
        } else if b == 0 {
            a
        } else {
            a.min(b)
        };
        if cap <= 4096 {
            for d in (got + 1)..=cap {
                assert!(
                    a % d != 0 || b % d != 0,
                    "gcd({}, {}) returned {}, but {} divides both — the emitted body is \
                     computing A common divisor rather than the GREATEST one",
                    a,
                    b,
                    got,
                    d
                );
            }
        }
    }

    // ── THE ORDER ROW. `gcd` is symmetric in VALUE, so symmetry alone proves
    //    nothing — but the emitted body is NOT symmetric in shape: the zero
    //    test decides `b`, the zero arm returns `a`, and `a % b` sits at fixed
    //    operand positions of one call. Agreement here is the runtime half of
    //    `control_21` (b)'s swapped-operand refutation, and disagreement would
    //    mean a transposition somewhere between the elaborated term, the
    //    reflected functional, the emitted call and the MIR locals.
    for (a, b) in [(12u64, 18u64), (270, 192), (7, 13), (48, 18), (1071, 462)] {
        assert_eq!(
            g(a, b),
            g(b, a),
            "gcd({a}, {b}) and gcd({b}, {a}) must agree"
        );
    }

    // ── THE ZERO ARM, ON ITS OWN. With `b == 0` the body returns `a` — its
    //    FIRST parameter, not the guarded one and not a constant. This is where
    //    a body that returned the wrong parameter would show up, and it is the
    //    arm `control_21` (e)'s mutation moves.
    assert_eq!(gcd(nat(42), nat(0)).to_u64(), Some(42), "the zero arm returns `a`");
    assert_eq!(gcd(nat(0), nat(0)).to_u64(), Some(0), "…including when `a` is 0");

    // ── ONE STEP, ISOLATED. `gcd 12 18` must descend to `gcd 18 (12 % 18)` =
    //    `gcd 18 12`, i.e. the first step SWAPS when a < b rather than
    //    stalling. A body that computed `b % a` instead would loop or return a
    //    different value; this pins the direction of the very first descent.
    assert_eq!(g(12, 18), g(18, 12), "the first step of gcd(12,18) is gcd(18,12)");
    assert_eq!(reference(12, 18), 6);
}
