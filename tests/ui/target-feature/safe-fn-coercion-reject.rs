// Trust: Regression test for #861 (rust-lang#116558).
// Test that #[target_feature] functions cannot be coerced to safe fn pointers,
// even when the calling context has the required features. The fn pointer can
// escape to a context without those features, making calls UB.
//
// Coercion to `unsafe fn()` pointers is still permitted.

//@ only-x86_64

#[target_feature(enable = "sse2")]
fn requires_sse2() {}

#[target_feature(enable = "sse2")]
fn also_has_sse2() {
    // Even though this function has sse2, coercion to safe fn ptr is rejected
    // because the pointer could escape to a context without sse2.
    let _: fn() = requires_sse2; //~ ERROR mismatched types
}

fn takes_safe_fn(_f: fn()) {}

fn main() {
    // Direct coercion in a context without the feature — always rejected.
    let _: fn() = requires_sse2; //~ ERROR mismatched types
    takes_safe_fn(requires_sse2); //~ ERROR mismatched types

    // Coercion to unsafe fn pointer is fine — caller must use unsafe to invoke.
    let _: unsafe fn() = requires_sse2; // OK
}
