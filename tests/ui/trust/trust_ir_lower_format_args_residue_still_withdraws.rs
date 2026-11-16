//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ compile-flags: -Ztrust-ir-lower=strict -Ztrust-verify=on -Ztrust-policy=advisory
//@ needs-trust-verify
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//! RE-ENABLED 2026-09-19, and the gap it was alarming about is CLOSED.
//!
//! History, kept because it is the point of the file. `54ea2954cd` made the
//! producer refuse the BODY that mints an unsignable Rust-ABI call edge instead
//! of failing the whole crate. That was the right change, but it moved the
//! refusal LATER — into the crate-assembly re-splice fixpoint — while
//! `-Ztrust-ir-lower=strict`'s only per-body arm reads the `mir_built`-time
//! report. So `show` was refused (`lowered: false, spliced: false`, an
//! `UnsignableRustAbiDeclaration(std::io::_print)` row on the sidecar) and strict
//! exited 0 with no diagnostic at all — against the flag's own help text, "a body
//! the producer cannot fully lower [is] a compile error instead of a
//! coverage-only skip". On 2026-09-17 this file was NOT re-blessed to
//! `check-pass`: that would have pinned a live contract violation as expected
//! behaviour and pointed the tripwire backwards, so it became `ignore-test` with
//! a capability alarm and the property moved to the run-make twin.
//!
//! The producer now carries a `RefusedBody` channel on `FinalizeSummary` — the
//! same shape as the existing `seam` verdicts, because both are verdicts that
//! cannot be known until the whole crate is assembled — and the compiler raises
//! each one at that body's own span under strict. The diagnostic therefore has a
//! SPAN now, which is why the annotation moved from the file-level (spanless)
//! form onto `show` itself. NOTE, learned the hard way: do not write that
//! spanless marker literally in prose here even inside backticks -- compiletest
//! scans the whole file for annotations and parsed this very sentence as one,
//! failing the test with "UNKNOWN: ` form".
//!
//! Measured 2026-09-19 on a stage1 at `c46762ee889` + that change, subject and
//! two controls: this file under strict exits 1 with exactly one "REFUSED at
//! crate assembly" error; the SAME file WITHOUT strict exits 0 with none; and a
//! body with no unsignable edge under strict exits 0 with none. So the error is
//! scoped to strict and to refused bodies, and is not a blanket refusal.
//!
//! THE RUN-MAKE TWIN STAYS. `tests/run-make/trust-ir-fndef-declaration-signatures`
//! compiles THIS FILE and asserts the refusal on the producer's own sidecar via
//! `assert_body_refused`. That pin observes the PRODUCER's ledger; this one
//! observes what strict REPORTS. They are different claims and the file must keep
//! its shape for both.
//!
//! Trust (2026-09-16, rvalue-snapshot admission — negative control (vi): a
//! still-unlowerable `format_args!` operand keeps the `std::io::_print`
//! refusal, by name). The admission lowers the expansion's tuple when the
//! element's BORROW is minted by wave-SB and the element is an rvalue rustc
//! provably cannot promote. It does nothing for an element whose borrow the
//! mint refuses BY TYPE: here `d` is a `&dyn Display` parameter, its snapshot
//! pointee is `FatPtr(TraitObject)`, and the named-local borrow arm's
//! allow-list (wave-AR2: Slice / Str / ContainerLen only) declines it before
//! emitting anything. The tuple therefore still fails, the IR watermark (H2)
//! is unmoved, wave-FA lowers the element `d` for its (absent) effect and
//! DROPS the `Arguments` construction into the unit sink, the drop withdraws
//! `_print`'s signature, and finalization refuses the declaration by name —
//! exactly as it did for every call-bearing `println!` before this landing.
//!
//! SHAPE CHOSEN BY READING, NOT BY MEASUREMENT: the plan of record asks for
//! a shape from the driver-side residue census (M1). Until that census runs,
//! this is the shape the borrow arm's allow-list refuses on its face. If the
//! driver shows `show` lowering instead, re-point this file at a measured
//! residue shape; keep the pin, which is "a dropped `Arguments` argument still
//! refuses `_print` by name". The finalization diagnostic is SPANLESS, hence
//! the file-level annotation form; `main`'s own unsize coercion may or may not
//! lower and is not this file's question (`dont-require-annotations`).

pub fn show(d: &dyn std::fmt::Display) {
    //~^ ERROR -Ztrust-ir-lower=strict: this body was REFUSED at crate assembly
    println!("{}", d);
}

fn main() {
    show(&5);
}


