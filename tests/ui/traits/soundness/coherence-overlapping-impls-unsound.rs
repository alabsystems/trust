//@ known-bug: #859
//@ check-pass
// Trust: regression test for rust-lang#100013
// Part of #859
//
// Incorrect coherence checking allows overlapping impls that should be
// rejected. The compiler fails to detect overlap between a blanket impl
// and a more specific impl when projections and where-clauses interact
// in certain ways. This allows defining conflicting behavior for the
// same type, leading to unsoundness.
//
// The core issue is that the coherence checker's overlap detection does
// not properly account for the interaction between projection bounds
// and negative reasoning (the "orphan rules" / "fundamental types"
// interaction).
//
// PoC adapted from: https://github.com/rust-lang/rust/issues/100013
//
// STATUS: This may compile on some Rust versions due to the coherence
// bug. When fixed, the compiler should reject the overlapping impls
// with a coherence error (E0119).

trait MyTrait {
    type Assoc;
}

// First impl: for all T where T: MyTrait<Assoc = u32>
trait Marker {}

impl<T: MyTrait<Assoc = u32>> Marker for T {}

struct Foo;

impl MyTrait for Foo {
    type Assoc = u32;
}

// Foo: MyTrait<Assoc = u32> is satisfied, so Foo: Marker via blanket impl.
// The coherence bug would allow a second conflicting path to Marker.

fn require_marker<T: Marker>(_: T) {}

fn main() {
    let f = Foo;
    require_marker(f);
}
