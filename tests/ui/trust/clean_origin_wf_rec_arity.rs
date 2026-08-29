//@ needs-trust-verify
//@ run-pass
//@ compile-flags: -Z trust-verify=off
//@ dont-check-compiler-stderr
//! **§R3a ACCEPTANCE — A MULTI-PARAMETER WELL-FOUNDED RECURSION IS EMITTABLE
//! AND CALLABLE.**
//!
//! The sibling fixtures run single-parameter well-founded recursions:
//! `clean_origin_wf_rec.rs` runs `countdownSum`, `clean_origin_wf_rec_mul.rs`
//! runs `fact`. Both descend on their SOLE parameter. These two descend on one
//! parameter while THREADING a second through the recursion, which is the whole
//! of what the compiler grew.
//!
//! # What moved, and what did not
//!
//! The measure is still a SINGLE parameter decreasing by exactly one, still
//! guarded by `if h : 0 < a`, still with exactly one self-call. What the lane
//! gained is arity: the fix spine now carries `5 + N` arguments under `N`
//! binders, the motive is an ARROW tower (`fun _ => Nat -> Nat`) rather than
//! `fun _ => Nat`, the functional binds `N + 1` binders rather than two, and
//! the recursive slot is applied to `N + 1` arguments rather than two. Side B's
//! de Bruijn layout is computed from `N` in one place (`reflect::RecCall`)
//! instead of being three literals.
//!
//! **It needed no pin move and no `compiler/**` edit.** `first-party/clean`
//! already lowers a two-parameter well-founded recursion with a one-parameter
//! measure at the pinned commit — `r7_arity_widening_probes` q1 reads the
//! lowering out of the elaborator — and the compiler-side materializer was
//! already generic in `template.arg_count` and `TemplateTy::Param { index }`.
//! The arity limit was `trust-clean-origin`'s alone. Per ruling v7/D2 a
//! measured fragment boundary is a statement of where we are, never a design.
//!
//! # The kernel probe ran BEFORE the producer was written
//!
//! The widening's one new identification is POSITIONAL: side B renders source
//! parameter `i` at the index the functional's binder telescope puts it at, and
//! that is only sound if the kernel DECIDES parameter order.
//! `r7_arity_widening_probes` q3 measured it — `sel a b = b := rfl` ADMITS and
//! the same-shaped `sel a b = a := rfl` is REFUSED — the `nat.mul` discipline
//! (`r6` q7) applied to a selection.
//!
//! # `dbl` and not just `addAcc`
//!
//! `addAcc a b = a + b` is SYMMETRIC in its two parameters, so on it alone
//! every operand-order control and every value assertion would pass whether or
//! not the compiler had the parameters the right way round. `dbl a b = b * 2^a`
//! is not: `dbl 3 1 = 8` and `dbl 1 3 = 6`. Both run here, and `control_16`'s
//! mutation battery is taken on `dbl` for the same reason.
//!
//! # DELIBERATELY NOT HERE
//!
//!   * **`gcd`.** Still not callable, and — measured 2026-08-26 — arity is no
//!     longer the reason. The modulo `gcd`'s measure-slot argument is `a % b`
//!     with a SYMBOLIC divisor, which commit `fa788aab89` refuses on purpose:
//!     Clean's `Nat.mod` is TOTAL where Rust's `%` PANICS, and the
//!     faithfulness gate is BLIND to that divergence because the panic lives
//!     in MIR the kernel never sees. That refusal IS the safety. A SUBTRACTIVE
//!     `gcd` does not route around it either: it decreases only in `a + b`, a
//!     two-parameter MEASURE, which is refused island-side by name.
//!   * **A parameter used twice in one branch.** `def scale (a b : Nat) := if
//!     h : 0 < a then b + scale (a - 1) b else 0` names `b` once in its value
//!     and once as the threaded argument. The emitted body moves the non-Copy
//!     bignum parameters and the emitter has no clone, so the plan refuses it
//!     by name (`r7_arity_widening_probes` q2 pins the refusal).
//!
//! SMALL INPUTS ON PURPOSE, same as the siblings: the emitted self-call form
//! recurses O(value) deep and each frame allocates a bignum.
//!
//! THE VALUES BELOW ARE PROBE-PINNED, not invented: `r7_arity_widening_probes`
//! q4 closes every row by `rfl` at the real kernel, with `addAcc 3 4 = 8`,
//! `dbl 3 1 = 6` and `dbl 1 3 = 8` as the refuting controls — the last two
//! being exactly the parameter-order confusions this fixture exists to rule
//! out. What runs here is the EMITTED binary computing them.

extern crate trust_bignum;

clean {
    def addAcc (a b : Nat) : Nat := if h : 0 < a then addAcc (a - 1) (b + 1) else b
    termination_by a

    def dbl (a b : Nat) : Nat := if h : 0 < a then dbl (a - 1) (b * 2) else b
    termination_by a
}

fn nat(value: u64) -> trust_bignum::Nat {
    trust_bignum::Nat::from_u64(value)
}

fn main() {
    // `addAcc a b = a + b` — the threaded parameter is genuinely CHANGED at
    // each step (`b + 1`), so a compiler that dropped the threading would
    // return `b` unchanged and every row but the first would fail.
    for (a, b, expected) in [(0u64, 0u64, 0u64), (0, 7, 7), (3, 4, 7), (9, 1, 10), (6, 6, 12)] {
        let out = addAcc(nat(a), nat(b));
        assert_eq!(
            out.to_u64(),
            Some(expected),
            "addAcc({a}, {b}) must compute {expected} through the emitted two-parameter \
             well-founded recursion"
        );
    }

    // `dbl a b = b * 2^a` — ASYMMETRIC, so these rows fail if the two
    // parameters are swapped anywhere between the fix spine, the functional's
    // binder telescope, the emitted self-call's operands and the MIR locals.
    for (a, b, expected) in [(0u64, 5u64, 5u64), (3, 1, 8), (1, 3, 6), (5, 2, 64), (4, 3, 48)] {
        let out = dbl(nat(a), nat(b));
        assert_eq!(
            out.to_u64(),
            Some(expected),
            "dbl({a}, {b}) must compute {expected} through the emitted two-parameter \
             well-founded recursion"
        );
    }

    // THE ORDER ROW, on its own. `dbl 3 1` and `dbl 1 3` are the same two
    // numerals in the other order, and they must not agree — this is the
    // runtime half of `r7_arity_widening_probes` q3's kernel measurement that
    // parameter order is DECIDED.
    let forward = dbl(nat(3), nat(1)).to_u64();
    let reversed = dbl(nat(1), nat(3)).to_u64();
    assert_eq!(forward, Some(8), "dbl(3, 1) = 1 * 2^3");
    assert_eq!(reversed, Some(6), "dbl(1, 3) = 3 * 2^1");
    assert_ne!(
        forward, reversed,
        "the emitted body must distinguish its two parameters; if these agree, the measure \
         and the threaded argument have been confused somewhere in the layout"
    );

    // The ZERO arm of the emitted zero test, on its own: it returns the
    // THREADED parameter, not the measure and not a constant. A body that
    // returned `a` would give 0 here, and one that returned a numeral would
    // ignore `b` entirely.
    assert_eq!(addAcc(nat(0), nat(42)).to_u64(), Some(42), "addAcc(0, 42) takes the zero arm");
    assert_eq!(dbl(nat(0), nat(42)).to_u64(), Some(42), "dbl(0, 42) takes the zero arm");
}
