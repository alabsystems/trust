//@ probe-shape: none
//@ probe-expect: clause-outside-fragment
//@ probe-note: The ICE recorded on 2026-07-25 is FIXED as of 2026-07-26; this is a
//@ probe-note: fragment boundary again, not a crash. Kept because it was the probe that
//@ probe-note: caught the crash. Formerly:
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
