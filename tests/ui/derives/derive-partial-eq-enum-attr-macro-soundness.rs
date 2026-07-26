// Test that derive(PartialEq) on enums generates sound code when attribute
// macros could potentially add variants after derive expansion. Non-matching
// variants must return false, not panic.
//
// Trust: regression test for rust-lang#148423
//@ run-pass

#[derive(PartialEq, Debug)]
enum Foo {
    A(i32),
    B { x: i32 },
    C,
}

fn main() {
    // Matching variants with same fields
    assert_eq!(Foo::A(1), Foo::A(1));
    assert_eq!(Foo::B { x: 42 }, Foo::B { x: 42 });
    assert_eq!(Foo::C, Foo::C);

    // Matching variants with different fields
    assert_ne!(Foo::A(1), Foo::A(2));
    assert_ne!(Foo::B { x: 1 }, Foo::B { x: 2 });

    // Non-matching variants must return false
    assert_ne!(Foo::A(1), Foo::B { x: 1 });
    assert_ne!(Foo::A(1), Foo::C);
    assert_ne!(Foo::B { x: 1 }, Foo::C);
}
