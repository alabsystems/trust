//@ check-pass
//@ compile-flags: -Z trust-ir-lower -Z trust-verify=off

// Trust (vtable slice 7 — the paired promoted-global value model): chain item (1) of the
// vtable campaign. A body held at the interpretation differential's tail gate ONLY because a
// reachable `GlobalAddr` of a paired `__trust_promoted_*` global materializes module-global
// state is now admitted for a real verdict, IFF the pairing and audit prove the observation
// is modeled:
//   * the global is immutable, initializer-BEARING, data-only, with BIT-EXACT equal content
//     on BOTH sides (post-slice-6 the oracle's once-stored escaping slot respells itself as
//     the producer's own mint, so both sides carry the same named global);
//   * every value derived from the address is a pure pass-through (shared Borrow / Copy), a
//     non-volatile Load-through, or a Return operand — a Store through it, an escape into a
//     call, a GEP, or any unanticipated operand position refuses fail-closed;
//   * at most ONE distinct admitted global per side (the slice-4 bound), and the entry's
//     reachable closure is call-free.
//
// Every lane below is one body of the measured 13-body flip population (postbuild-vtable7:
// Agreed 2541 -> 2554, all other scorecard cells byte-identical to postbuild-vtable6). Each
// must keep COMPILING — a lowering decline is a coverage decision, never an error — and each
// pins one arm of the admission.

// ADDRESS-RETURNING, scalar content (const-address-of::A/B/C, references::BOO,
// ptr_is_null::FOO, dealloc_intrinsic::Z, issue-6991::x): raw `Ptr` agreement is meaningful
// because on an admitted body the returned pointer can only BE the single paired global's
// address at offset 0.
const A: *const i32 = &raw const *&2;
const BOO: &i32 = &42;
static X: &'static usize = &1;

// ADDRESS-RETURNING, empty-aggregate content (issue-53708::main::C, non-scalar-cast::FOO):
// the pairing's content equality compares `Aggregate([])` bit-exactly.
#[derive(PartialEq, Eq)]
struct S;
const C: &S = &S;

// ADDRESS-RETURNING behind an opaque never-read receiver (lint-no-err::Repro::get).
struct Repro;
impl Repro {
    fn get(&self) -> &i32 {
        &3
    }
}

// UNIT-RETURNING with the global touched on both sides (sugar-ambiguity::pin::foo,
// late-bound-in-body's closure): agreement is over the unit value; the admitted GlobalAddr
// and the oracle's kept Borrows are the only module-global observations.
fn unit_touch() {
    let _x: &bool = &true;
}

// STILL HELD, deliberately (the fail-closed side of the same slice — these must also keep
// compiling): the address ESCAPES INTO A CALL (regions-reassign-let-bound-pointer::main —
// call-bearing closure disables admission outright), and a multi-promoted body whose oracle
// side carries an UNPAIRED extra respelled slot (sugar-ambiguity::main) stays on its
// coverage-only note.
fn takes(_r: &isize) {}
fn escapes_into_call() {
    takes(&1);
}

fn main() {
    let _ = (A, BOO, X, C, Repro.get());
    unit_touch();
    escapes_into_call();
}
