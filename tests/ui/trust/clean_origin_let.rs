//@ needs-trust-verify
//@ run-pass
//@ compile-flags: -Z trust-verify=off
//@ dont-check-compiler-stderr
//! **THE `let`-BINDING SHAPE RUNS** (2026-09-13, W5 widening).
//!
//! A Rust `main` calls kernel-checked Clean `def`s whose bodies contain
//! `let`-bindings, through the minted `DefId`s. A `let y := v; b` is
//! definitionally `b[y := v]` — the kernel's own zeta step — so the emitter
//! reduces every `let` away before recognition (`emit::zeta_normalize`) and the
//! body flows into the SAME shape recognisers, materializer and faithfulness
//! gate as its `let`-free equivalent. The gate verifies the emitted body
//! against the island's `let` term (zeta) before anything links, and the binary
//! computes the reduced value.
//!
//! Every value asserted distinguishes the emitted semantics from a plausible
//! mistranslation, so a green run pins the reduction and not merely that a call
//! linked:
//!
//! * `id_let` — the trivial `let y := x; y`, which must reduce to the
//!   parameter projection, not to `0` or a fresh temp read before it is
//!   written;
//! * `sq_let(3) == 16` — `let y := x+1; y*y` USES the binding twice, so it
//!   reduces to `(x+1)*(x+1)`; `y+y` (a plausible mis-read) would give `8`,
//!   and `y*x` would give `12`;
//! * `shadow_let(10) == 11` — `let x := x+1; x` REBINDS the parameter name and
//!   the innermost binding must win: returning the outer parameter would give
//!   `10`;
//! * `nested_let(5) == 6` and `letval_let(4) == 10` — chained and
//!   bound-value-is-itself-a-`let` compositions.
//!
//! `-Z trust-verify=off` is the point, not a convenience: the faithfulness
//! gate is a compilation-correctness check, deliberately NOT behind any
//! verification switch, and this fixture would be worthless if the flag could
//! disable the machinery it measures.

mod m {
    clean {
        def id_let (x : UInt64) : UInt64 := let y := x; y
        def sq_let (x : UInt64) : UInt64 := let y := x + 1; y * y
        def shadow_let (x : UInt64) : UInt64 := let x := x + 1; x
        def nested_let (x : UInt64) : UInt64 := let y := x; let z := y + 1; z
        def letval_let (x : UInt64) : UInt64 := let y := (let w := x; w + 1); y * 2
    }
}

fn main() {
    // Identity binding: the binding is the parameter, verbatim.
    assert_eq!(crate::m::id_let(7), 7, "let y := x; y must be the identity");
    assert_eq!(crate::m::id_let(0), 0);
    assert_eq!(crate::m::id_let(u64::MAX), u64::MAX);

    // Reused binding: (x+1)*(x+1). `y+y` would give 8, `y*x` would give 12.
    assert_eq!(crate::m::sq_let(3), 16, "let y := x+1; y*y == (3+1)*(3+1)");
    assert_eq!(crate::m::sq_let(0), 1, "(0+1)*(0+1)");
    assert_eq!(crate::m::sq_let(u64::MAX), 0, "(u64::MAX + 1) wraps to 0, and 0*0 == 0");

    // Shadowing: the inner `x` (param+1) wins; returning the outer would be 10.
    assert_eq!(crate::m::shadow_let(10), 11, "let x := x+1; x must return the SHADOW, 11");
    assert_eq!(crate::m::shadow_let(0), 1);

    // Nested lets: let y := x; let z := y+1; z == x+1.
    assert_eq!(crate::m::nested_let(5), 6, "nested let chain computes x+1");

    // Bound value is itself a let: (x+1)*2.
    assert_eq!(crate::m::letval_let(4), 10, "let y := (let w := x; w+1); y*2 == (4+1)*2");
    assert_eq!(crate::m::letval_let(0), 2);
}
