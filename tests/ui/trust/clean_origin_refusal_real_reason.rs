//@ needs-trust-verify
//@ check-fail
//@ compile-flags: -Z trust-verify=off
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! **The `E0425` note for a refused island `def` states the reason it was
//! ACTUALLY refused for (ruling v7/D3).**
//!
//! Measured 2026-09-16 (probe-call 04a): `sfst` below is accepted by the
//! crate's Clean batch — the same build reports it "kernel-checked" when it is
//! not called — yet its call site was told that `sfst` is "a `parsed` symbol"
//! and advised to "remove any `sorry`/`trusted`". There is no `sorry`. The mint
//! site had mapped every certified-admission error onto a fabricated
//! `KernelStatus::Parsed` (`Err(_) => KernelStatus::Parsed`), so none of the
//! options offered could fix the situation.
//!
//! The refusal is unchanged — nothing is minted, fail-closed — and now carries
//! the admitter's own reason verbatim, plus the carrier lane's refusal of the
//! same signature when it has one, plus the LIKELY CAUSE when the kernel type
//! begins with a type-variable binder. That last part is this repro's real
//! story (measured 2026-09-17 in control 28): the Clean prelude declares no
//! `Int64`, so Lean's auto-bound-implicit rule made the NAME a type variable
//! and `sfst` was kernel-checked as a projection polymorphic over an arbitrary
//! type — kernel type `Sort -> #0 -> #1 -> #2`. The exact reason text belongs to the
//! admitter and is pinned in the `crates/` lane
//! (`trust-clean-origin/tests/control_28_refusal_states_the_real_reason.rs`,
//! which also pins that the `parsed`/`sorry` story is GONE — an absence this
//! file cannot express). Here: the note is attached, names the real lane, and
//! carries options.

mod m {
    clean {
        def sfst (a : Int64) (b : Int64) : Int64 := a
        def ufst (a : UInt64) (b : UInt64) : UInt64 := a
    }
}

fn main() {
    let _ = m::sfst(-5i64, 9i64);
    //~^ ERROR cannot find function `sfst` in module `m`
    //~| NOTE the certified re-admission of THIS declaration

    // CLOSE NEGATIVE TWIN: the same shape at a width that carries still mints —
    // the new refusal arm is not a second way to refuse a good declaration. An
    // `E0425` here would be an unannotated error and fail the test.
    let _ = m::ufst(5u64, 9u64);
}
