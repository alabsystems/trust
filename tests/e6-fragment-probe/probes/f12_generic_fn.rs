//@ probe-shape: none
//@ probe-expect: ice
//@ probe-note: REGRESSION, 2026-07-25: this now ICEs the compiler. It used to report
//@ probe-note: clause-outside-fragment (generics are outside the domain map — the W16
//@ probe-note: extraction-timing wall reaches this lane too). It is NOT an E6 problem:
//@ probe-note: `pub fn idg<T>(x: T) -> T { x }` alone panics under -Ztrust-verify=on,
//@ probe-note: with no island and no clause. -Ztrust-ir-flip=no avoids it.
//@ probe-note:   crates/trust-thir-lower/src/flip.rs:127 — attempted to read from
//@ probe-note:   stolen value: rustc_middle::thir::Thir
//@ probe-note: Program 1 owns that file; see docs/exec/2026-07-25-note-flip-ice-on-generics.md
clean { def ident_isl (x : UInt64) : UInt64 := x }
pub fn idg<T>(x: T) -> T { x }
pub fn use_it(x: u64) -> u64
    ensures result == ident_isl(x)
{ idg(x) }
