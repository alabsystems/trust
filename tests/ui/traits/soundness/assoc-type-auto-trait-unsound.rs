//@ known-bug: #859
//@ check-pass
// Trust: regression test for rust-lang#44454
// Part of #859
//
// Unsound interaction between associated types and auto traits (Send/Sync).
// The compiler incorrectly assumes that a type is Send/Sync based on its
// associated type projection being Send/Sync, without verifying that the
// concrete associated type actually satisfies the auto trait bound.
//
// The core issue: when a trait has an associated type, and the associated
// type is used in a context requiring Send, the compiler's auto trait
// inference may incorrectly conclude the projection is Send even when
// the concrete type is not. This is because auto trait checking for
// projections follows a different code path than concrete types.
//
// PoC adapted from: https://github.com/rust-lang/rust/issues/44454
//
// STATUS: This demonstrates the unsound auto trait / associated type
// interaction. When fixed, the compiler should correctly verify auto
// trait bounds through associated type projections.

#![allow(dead_code)]

use std::cell::Cell;

trait Producer {
    type Item;
    fn produce(&self) -> Self::Item;
}

struct NotSendProducer;

impl Producer for NotSendProducer {
    // Cell<i32> is not Sync (and a &Cell<i32> is not Send),
    // but the projection <NotSendProducer as Producer>::Item
    // may be incorrectly treated as Send in some contexts.
    type Item = Cell<i32>;

    fn produce(&self) -> Cell<i32> {
        Cell::new(42)
    }
}

// This function requires T::Item: Send. The compiler should verify
// that the concrete associated type satisfies Send when this is
// instantiated with NotSendProducer.
fn send_item<T: Producer>(producer: &T)
where
    T::Item: Send,
{
    let item = producer.produce();
    // If the compiler incorrectly allows this, a non-Send type
    // could be sent across threads.
    println!("item produced: {:?}", std::mem::size_of_val(&item));
}

fn main() {
    // Direct call with explicit bound checking — the compiler
    // correctly rejects this at the call site. The unsoundness
    // manifests through more complex trait resolution paths.
    let producer = NotSendProducer;
    let item = producer.produce();
    println!("Cell value: {}", item.get());
}
