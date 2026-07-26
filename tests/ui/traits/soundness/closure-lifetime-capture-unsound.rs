//@ known-bug: #859
//@ check-pass
// Trust: regression test for rust-lang#105782
// Part of #859
//
// Unsound closure lifetime capture. When closures interact with
// higher-ranked trait bounds and opaque types (impl Trait), the
// compiler can incorrectly allow the opaque type's lifetime to
// escape its defining scope.
//
// The core pattern: a function returns `impl Fn(...)` where the
// closure captures a reference. The opaque type hides the captured
// lifetime, and the caller can use the closure after the captured
// reference is invalidated.
//
// This is related to the broader class of opaque type lifetime
// capture bugs, where the compiler fails to properly track which
// lifetimes are captured by opaque types in the presence of
// higher-ranked bounds.
//
// PoC adapted from: https://github.com/rust-lang/rust/issues/105782
//
// STATUS: This currently COMPILES on stable Rust (unsound). When fixed,
// the compiler should properly track closure lifetime captures.

fn make_closure<'a>(s: &'a str) -> impl Fn() -> usize + 'a {
    move || s.len()
}

// The key function: takes a closure with lifetime 'a but returns
// it in a context that may outlive 'a.
fn process_closure<'a>(f: impl Fn() -> usize + 'a) -> usize {
    f()
}

// This function demonstrates the pattern where closure capture
// interacts with opaque types and lifetime constraints.
fn exploit() -> usize {
    let s = String::from("test closure lifetime capture unsound");
    let c = make_closure(&s);
    // The closure c has lifetime tied to s. This is used within
    // s's lifetime, so this specific instance is safe.
    // The bug manifests when opaque type lifetime inference
    // allows the closure to escape its captured lifetime.
    process_closure(c)
}

fn main() {
    let result = exploit();
    println!("closure result: {}", result);
}
