//@ needs-trust-verify
//@ run-pass
//@ compile-flags: -Z trust-verify=off
//@ dont-check-compiler-stderr
//! **§R3d ACCEPTANCE — the TWO-ARGUMENT `gcd` RUNS FROM RUST, WITH NO FUEL.**
//!
//! ```text
//! def gcdB (a b : Nat) : Nat :=
//!   if h : 0 < b then gcdB ((a-b)+(b-a)) (a-(a-b)) else a
//! termination_by a + 2*b
//! ```
//!
//! `gcdB(a, b)` below is a DIRECT call to that Clean definition. There is no
//! wrapper, no fuel parameter, and nothing between the Rust call site and the
//! gate-verified body.
//!
//! # What changed from the sibling fixture, and why it matters
//!
//! `clean_origin_wf_rec_gcd.rs` runs `gcdF f a b` — a three-argument fuelled
//! loop — behind an ordinary Rust wrapper `gcd(a, b) = gcdF(a + 2*b, a, b)`.
//! Its header says so plainly: *"the two-argument surface is an unverified Rust
//! wrapper that supplies the fuel"*, so the proof claim covered `gcdF` and the
//! sufficiency of `a + 2b` was true, measured at both ends, and NOT proved.
//!
//! Here the two-argument surface **is** the recursion. `a + 2*b` is the
//! `termination_by` MEASURE, discharged inside `first-party/clean` by its own
//! cascade — axiom-free, foundational closure only — instead of being handed to
//! the loop as a countdown. Nothing about the call carries an unproved
//! sufficiency assumption, because there is no fuel to be sufficient.
//!
//! # How it reaches the compiler
//!
//! The measure names BOTH parameters, so `first-party/clean` lowers it as a
//! course-of-values recursion on the measure's VALUE — WF "phase 3", its
//! `wf_recursion::sum_measure`. That is a different `WellFounded.fix` spine from
//! the one every earlier fixture here uses: an `n`-dependent Pi motive, a spine
//! seeded `(Nat.succ m) p⃗ (Nat.le.refl (Nat.succ m))`, one extra hypothesis
//! binder, and a five-argument `rec` whose decrease proof is LAST. The emitted
//! MIR is nevertheless byte-identical in shape to phase 2's — one bignum zero
//! test on a parameter, two arm regions, one self-call with one operand per
//! parameter:
//!
//! ```text
//! bb0: _3 = &_2; is_zero(move _3) -> _4      -- the guard, on `b`
//! bb2: _0 = move _1                          -- the zero arm, `a`
//! bb3..bb7: (a-b), (b-a), their sum; (a-b), a-(a-b)
//! bb8: gcdB(move _13, move _19) -> _0
//! ```
//!
//! # WHAT THIS DOES AND DOES NOT CLAIM
//!
//! **It does not claim `gcd` is proved correct.** `Nat.gcd` is ABSENT from the
//! prelude (`gcd_final_probes` n1 asserts that absence), so there is no prelude
//! `gcd` to state agreement with and no correctness theorem is available to
//! state at all. The rows below are hand-computed literals — and every one of
//! them is a KERNEL DECISION with a refuting sibling: `gcd_phase3_probes` p7
//! puts each `gcdB a b = v` to the kernel and requires the wrong `v` to be
//! REFUSED, so this fixture compares the emitted binary against decisions rather
//! than against two copies of the same guess.
//!
//! What it DOES claim is the whole of what it does: the binary emitted from the
//! Clean island by the verified lowering — planned by
//! `emit::recognise_wf_sum_measure_rec`, materialized by the shared zero-test
//! skeleton, read back by `trust_types::recognize_wf_sum_measure_rec`, reflected
//! by `reflect_wf::reflect_wf_functional` at the phase-3 telescope, and admitted
//! by `gate::check_faithful_wf_functional` against side A's own functional with
//! its measure plumbing and decrease proof BORROWED — computes these values.
//!
//! The refuting siblings of that admit are
//! `control_18_wf_sum_measure_emitter_mutation`: swapped self-call operands, the
//! guard on the wrong parameter, a wrong threaded index, the `|a-b|` / `min a b`
//! legs' operands transposed, and a wrong bignum callee are all REFUSED.
//!
//! # Why the inputs are small
//!
//! For the same reason as the siblings — each frame allocates bignums — but this
//! form is far cheaper than the fuelled one: it stops at its fixed point instead
//! of always running the full `a + 2b` steps. `gcd(270, 192)` is about a dozen
//! frames here where the fuel form is 654, and it is still included because a
//! shallow row cannot tell a working recursion from one that returns its
//! argument.

extern crate trust_bignum;

clean {
    def gcdB (a b : Nat) : Nat := if h : 0 < b then gcdB ((a-b)+(b-a)) (a-(a-b)) else a
    termination_by a + 2*b
}

fn nat(value: u64) -> trust_bignum::Nat {
    trust_bignum::Nat::from_u64(value)
}

/// The DIRECT call. No wrapper computes anything: `gcdB` is the Clean
/// definition, called with the two arguments it declares.
fn gcd(a: u64, b: u64) -> u64 {
    gcdB(nat(a), nat(b)).to_u64().expect("gcd of two u64 fits in u64")
}

fn main() {
    // ── THE ROWS THE TASK NAMES, every one a kernel decision (p7) ──
    for (a, b, expected) in
        [(12u64, 18u64, 6u64), (270, 192, 6), (7, 13, 1), (0, 5, 5), (5, 0, 5)]
    {
        assert_eq!(
            gcd(a, b),
            expected,
            "gcd({a}, {b}) must compute {expected} through the EMITTED sum-measure \
             well-founded recursion, called with TWO arguments and no fuel"
        );
    }

    // ── THE INDEPENDENT CHECK, so the rows above are a DECISION and not a
    //    restatement of literals I typed.
    //
    // Asserting `gcd(12, 18) != 3` right after asserting it IS 6 measures
    // nothing. What measures something is checking the emitted answer against
    // the DEFINING PROPERTY, computed here in ordinary Rust: `g` divides both,
    // and nothing larger does. A body that returned a common divisor rather
    // than the greatest one, or that returned one of its arguments, is caught
    // by this on inputs the literal table never mentions.
    for (a, b) in [
        (12u64, 18u64),
        (270, 192),
        (7, 13),
        (0, 5),
        (5, 0),
        (48, 18),
        (99, 33),
        (17, 5),
        (1, 1),
        (100, 75),
    ] {
        let g = gcd(a, b);
        // NOTE: these `assert!` messages pass their values POSITIONALLY.
        // `assert!`'s message reaches `panic!` as a plain literal at this
        // fixture's edition, so inline `{a}` capture is not formatted and
        // `non_fmt_panics` fires — which compiletest reports as an unexpected
        // diagnostic. `assert_eq!` (used above) always goes through
        // `format_args!` and is unaffected, which is why only these two forms
        // need it.
        assert!(
            (a == 0 && b == 0) || g != 0,
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
    //    shape: the guard is on `b` alone, the zero arm returns `a`, and
    //    `a - b` and `b - a` sit at different operand positions of different
    //    calls. Agreement here is the runtime half of `control_18`'s
    //    swapped-operand and wrong-guard refutations.
    for (a, b) in [(12u64, 18u64), (270, 192), (7, 13), (48, 18), (99, 33)] {
        assert_eq!(
            gcd(a, b),
            gcd(b, a),
            "gcd({a}, {b}) and gcd({b}, {a}) must agree; if they do not, an operand order \
             is transposed somewhere between the elaborated term, the reflected functional, \
             the emitted self-call and the MIR locals"
        );
    }

    // ── THE ZERO ARM, on its own. The guard is `0 < b`, so `b = 0` returns `a`
    //    UNCHANGED — not `b`, not a constant, not the measure. This is the arm
    //    the emitted zero test selects, and the row that a body guarding the
    //    WRONG parameter fails immediately.
    assert_eq!(gcd(42, 0), 42, "the zero arm returns `a` verbatim");
    assert_eq!(gcd(0, 0), 0, "…including when `a` is 0");
    assert_eq!(gcd(1, 0), 1);

    // ── ONE STEP, isolated. `gcd(0, 5)` takes exactly one recursive step —
    //    `(|0-5|, min 0 5) = (5, 0)` — so it exercises the self-call's TWO
    //    operands at their simplest, where the truncated `-` does all the work.
    assert_eq!(gcd(0, 5), 5, "one step: (0, 5) -> (5, 0) -> 5");
    assert_eq!(gcd(0, 1), 1);

    // ── A DEGENERATE PAIR the fixed-point argument has to cover.
    assert_eq!(gcd(6, 6), 6, "equal inputs reach (0, 6), then (6, 0), and hold");
}
