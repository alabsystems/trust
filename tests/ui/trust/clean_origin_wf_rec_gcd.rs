//@ needs-trust-verify
//@ run-pass
//@ compile-flags: -Z trust-verify=off
//@ dont-check-compiler-stderr
//! **§R3b ACCEPTANCE — `gcd` RUNS FROM RUST.**
//!
//! A genuinely recursive, genuinely gcd-computing Clean definition is emitted,
//! gate-verified, and called from Rust below. This is the design doc's ratified
//! acceptance example reached at last — by a route the doc did not name, and the
//! difference is stated in full under "WHAT THIS DOES NOT CLAIM".
//!
//! # The shape, and why it is this shape
//!
//! ```text
//! def gcdF (f a b : Nat) : Nat :=
//!   if h : 0 < f then gcdF (f - 1) ((a - b) + (b - a)) (a - (a - b)) else a
//! termination_by f
//! ```
//!
//! The step map is `T(a, b) = (|a - b|, min a b)`, written in truncated `-` and
//! `+` alone: on ℕ, `|a - b|` is `(a-b) + (b-a)` and `min a b` is `a - (a - b)`,
//! because truncated subtraction makes the "wrong" half of each pair `0`. It is
//! subtractive Euclid with the BRANCH removed — one guard, one self-call, no
//! comparison — so it fits a fragment whose emitted contract is a single zero
//! test. It preserves `gcd`, its only fixed points are `(g, 0)`, and `a + 2b`
//! strictly decreases by `b` on every non-fixed step.
//!
//! The recursion therefore terminates on `f` alone, decreasing by exactly one,
//! and any `f >= a + 2b` returns `gcd a b` with the extra fuel inert. The
//! two-argument `gcd` below is an ordinary Rust wrapper that supplies `a + 2b`.
//!
//! # Why not the ratified `gcd b (a % b)`, and why not `a + b`
//!
//! Both were refused when this fixture was written. **The modulo one no longer
//! is — see the correction below, and `clean_origin_wf_rec_modulo_gcd.rs`,
//! which is that form running.** The fuel form is still the right shape for
//! THIS fixture (it exercises general truncated `-` and a three-argument
//! recursion, which the modulo form does not), so nothing here was rewritten to
//! chase it.
//!
//!   * **The modulo form** — `if h : 0 < b then gcd b (a % b) else a` — has a
//!     SYMBOLIC divisor in its self-call argument, which commit `fa788aab89`
//!     refuses on purpose: Clean's `.mod` is TOTAL where Rust's `%` PANICS, and
//!     the faithfulness gate is BLIND to that divergence because the panic
//!     lives in MIR the kernel never sees. That refusal IS the safety —
//!     **AT A MACHINE WIDTH, which is where it was measured and where it still
//!     fires** (`control_21` (h) pins it; `r8_nat_mod_probes` q6 re-measures the
//!     divergence itself). The paragraph as originally written generalised that
//!     `UInt{N}` finding to `Nat`, and §R8 (2026-08-28) measured that the two
//!     lanes differ: at the bignum carrier the emitted operation is
//!     `Call(trust_bignum::Nat::rem, ..)`, not an `Rvalue::BinaryOp` — there is
//!     no `Assert`, no panic edge, and `Nat::rem` returns the dividend at a
//!     zero divisor. What replaces panic-freedom there is carrier totality
//!     (trust-bignum's kernel-differential test), and the obligation actually
//!     discharged is the DECREASE. The refusal above is UNMOVED; only the claim
//!     that it covered `Nat` was too strong.
//!   * **The two-call subtractive form** decreases in `a + b`, a TWO-PARAMETER
//!     measure, which the elaborator refuses by name at this pin ("a measure
//!     over more than one parameter … is not lowered yet"). It also needs a
//!     second self-call, and the gate's decrease-slot borrow pairs side B's
//!     call sites with side A's ONE at a time.
//!
//! Ranked against those, the fuel form needed no pin move, no `compiler/**`
//! edit, and no new gate pairing — two additions inside `crates/` (a general
//! truncated `Sub` node, and making the duplication rule MOVE-aware).
//!
//! # The kernel probe ran BEFORE the producer was written
//!
//! The one new identification is `a - b ≡ Nat.sub a b`.
//! `gcd_route_probes` m1 measured it and, critically, measured its wrong twins:
//! `a - b = Nat.add a b` REFUSED, `a - b = Nat.sub b a` REFUSED (subtraction is
//! not commutative, unlike `+` and `*` — which is what makes
//! `control_17`'s swapped-operand rows genuine refutations rather than
//! delicate ones), `5 - 3 = 3` REFUSED, `1 - 3 = 1` REFUSED. Truncation is the
//! kernel's decision too: `1 - 3 = 0` ADMITS, which is exactly
//! `trust_bignum`'s `checked_sub(..).unwrap_or(ZERO)`.
//!
//! # WHAT THIS DOES NOT CLAIM
//!
//! **`gcd` is not proved correct here.** The gate-verified object is `gcdF`, a
//! three-argument fuelled loop; the two-argument surface is an unverified Rust
//! wrapper that supplies the fuel. The fuel-sufficiency fact is true and is
//! measured at both ends (`gcd_final_probes` n3, at exactly `a + 2b` and at
//! `a + 2b + 1`), but it is not proved. And `Nat.gcd` is ABSENT from the
//! prelude — `gcd_final_probes` n1 asserts that absence — so there is no
//! prelude gcd to state agreement with; the rows below are literals, exactly as
//! the shipped `addAcc`/`dbl`/`fact` fixtures use, and each one is a kernel
//! DECISION with a refuting control (`gcd_final_probes` n4).
//!
//! What this fixture does claim is the whole of what it does: the emitted
//! binary, produced from the Clean island by the verified lowering, computes
//! these values.
//!
//! SMALL-ISH INPUTS ON PURPOSE, same as the siblings: the emitted recursion
//! always runs the FULL fuel — it does not stop at the fixed point — and each
//! frame allocates bignums. `gcd(270, 192)` is 654 frames, and it is here
//! because a shallow row cannot tell a working recursion from one that returns
//! its argument.

extern crate trust_bignum;

clean {
    def gcdF (f a b : Nat) : Nat := if h : 0 < f then gcdF (f - 1) ((a - b) + (b - a)) (a - (a - b)) else a
    termination_by f
}

fn nat(value: u64) -> trust_bignum::Nat {
    trust_bignum::Nat::from_u64(value)
}

/// The two-argument surface. **This wrapper is ordinary Rust and carries no
/// proof claim** — it exists only to supply a fuel bound large enough that the
/// loop has reached its fixed point, and `a + 2b` is that bound.
fn gcd(a: u64, b: u64) -> u64 {
    gcdF(nat(a + 2 * b), nat(a), nat(b))
        .to_u64()
        .expect("gcd of two u64 fits in u64")
}

fn main() {
    // ── THE ROWS THE TASK NAMES, every one a kernel decision (n4) ──
    for (a, b, expected) in
        [(12u64, 18u64, 6u64), (270, 192, 6), (7, 13, 1), (0, 5, 5), (5, 0, 5)]
    {
        assert_eq!(
            gcd(a, b),
            expected,
            "gcd({a}, {b}) must compute {expected} through the EMITTED well-founded \
             recursion over general truncated subtraction"
        );
    }

    // ── THE INDEPENDENT CHECK, so the rows above are a DECISION and not a
    //    restatement of literals I typed.
    //
    // Asserting `gcd(12, 18) != 3` right after asserting it IS 6 measures
    // nothing. What measures something is checking the emitted answer against
    // the DEFINING PROPERTY, computed here in ordinary Rust: `g` divides both,
    // and nothing larger does. A body that returned a common divisor rather
    // than the greatest one, or that returned an argument, or that returned the
    // fuel, is caught by this on inputs the literal table never mentions.
    for (a, b) in [(12u64, 18u64), (270, 192), (7, 13), (0, 5), (5, 0), (48, 18), (99, 33), (17, 5)]
    {
        let g = gcd(a, b);
        // NOTE: these `assert!` messages pass their values POSITIONALLY.
        // `assert!`'s message reaches `panic!` as a plain literal at this
        // fixture's edition, so inline `{a}` capture is not formatted and
        // `non_fmt_panics` fires — which compiletest reports as an unexpected
        // diagnostic. `assert_eq!` (used above) always goes through
        // `format_args!` and is unaffected, which is why only these two forms
        // need it.
        assert!(
            (a == 0 || g != 0) && (b == 0 || g != 0),
            "gcd({}, {}) = 0 with a non-zero input is not a common divisor",
            a,
            b
        );
        if g != 0 {
            assert_eq!(a % g, 0, "gcd({a}, {b}) = {g} must DIVIDE {a}");
            assert_eq!(b % g, 0, "gcd({a}, {b}) = {g} must DIVIDE {b}");
        }
        // …and it must be the GREATEST. This is the half that a body returning
        // `1`, or any smaller common divisor, fails.
        let cap = if a == 0 { b } else if b == 0 { a } else { a.min(b) };
        for d in (g + 1)..=cap {
            assert!(
                a % d != 0 || b % d != 0,
                "gcd({}, {}) returned {}, but {} divides both — the emitted body is \
                 computing A common divisor rather than the GREATEST one",
                a,
                b,
                g,
                d
            );
        }
    }

    // ── THE ORDER ROW. `gcd` is symmetric in VALUE, so symmetry alone proves
    //    nothing about the emission — but the emitted body is NOT symmetric in
    //    shape: `a - b` and `b - a` sit at different operand positions of
    //    different calls, and the zero arm returns `a`. Agreement here is the
    //    runtime half of `control_17`'s swapped-operand refutations.
    for (a, b) in [(12u64, 18u64), (270, 192), (7, 13), (48, 18)] {
        assert_eq!(
            gcd(a, b),
            gcd(b, a),
            "gcd({a}, {b}) and gcd({b}, {a}) must agree; if they do not, an operand order \
             is transposed somewhere between the elaborated term, the reflected functional, \
             the emitted self-call and the MIR locals"
        );
    }

    // ── THE ZERO ARM, on its own: with no fuel the body returns `a`, its
    //    SECOND parameter — not the measure, not a constant. This is the arm
    //    the emitted zero test selects, and it is where a body that returned
    //    the fuel would show up.
    assert_eq!(gcdF(nat(0), nat(42), nat(7)).to_u64(), Some(42), "the zero arm returns `a`");
    assert_eq!(gcdF(nat(0), nat(0), nat(9)).to_u64(), Some(0), "…including when `a` is 0");

    // ── EXTRA FUEL IS INERT. The recursion runs every unit of fuel it is
    //    given, so this also demonstrates that the step map's fixed point is
    //    genuinely fixed rather than the loop merely stopping in time.
    for extra in [0u64, 1, 5, 40] {
        assert_eq!(
            gcdF(nat(12 + 2 * 18 + extra), nat(12), nat(18)).to_u64(),
            Some(6),
            "fuel beyond the bound must not change the answer (extra = {extra})"
        );
    }

    // ── A DEGENERATE PAIR the fixed-point argument has to cover.
    assert_eq!(gcd(0, 0), 0, "gcd(0, 0) = 0, and the loop must terminate at zero fuel");
    assert_eq!(gcd(6, 6), 6, "equal inputs reach (0, 6) in one step and then hold");
}
