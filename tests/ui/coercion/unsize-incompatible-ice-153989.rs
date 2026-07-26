// Regression test for rust-lang#153989
// Unsized coercion between incompatible types must emit a diagnostic error,
// not generate broken MIR that ICEs during validation.
//
// The ICE occurred because typeck recorded an Unsize coercion adjustment based
// on deferred obligations that later failed. The broken adjustment then produced
// invalid MIR (PointerCoercion::Unsize between non-coercible types) which
// crashed during MIR validation.
//
// This test verifies that the compiler does not ICE on code that attempts
// unsized coercions between incompatible types. Instead, it should produce
// a clean type error.
//
// Trust: regression test for root-cause fix of Unsize coercion MIR ICE

trait Foo {}
trait Bar {}

struct Baz;
impl Foo for Baz {}
// Note: Baz does NOT implement Bar

// Attempt coercion to a trait object for an unimplemented trait.
// This must produce a type error, not an ICE.
fn bad_trait_object(x: &Baz) -> &dyn Bar {
    x //~ ERROR the trait bound `Baz: Bar` is not satisfied
}

// Attempt to coerce between incompatible pointer types.
// This must produce a type error, not an ICE.
fn incompatible_ref(x: &[i32; 5]) -> &str {
    x //~ ERROR mismatched types
}

fn main() {}
