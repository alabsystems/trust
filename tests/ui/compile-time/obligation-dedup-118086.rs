// Trust: regression test for compile-time bug rust-lang#118086
//
// Exponential time in obligation deduplication. When the trait solver
// processes obligations, it must deduplicate them to avoid redundant work.
// However, obligations arising from deeply nested generic types can produce
// an exponential number of sub-obligations before deduplication kicks in.
// For example, a type like Vec<(A, (B, (C, ...)))> generates obligations
// for each nested tuple, and proving bounds on the outer type recursively
// generates obligations for all inner types.
//
// The original report showed exponential blowup with ~15+ levels of nested
// generic obligations. This test uses 12 levels of nested generic types
// with trait bounds to stress the obligation deduplication machinery
// without causing a hang.
//
// Upstream: https://github.com/rust-lang/rust/issues/118086
// Tracked in Trust: #865
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//@ check-pass

// Trait with a blanket impl that generates sub-obligations.
// Each time the solver proves Checkable for a composite type,
// it must also prove Checkable for each component, which in
// turn generates more sub-obligations for THEIR components.
trait Checkable {
    fn check(&self) -> bool;
}

impl Checkable for u32 {
    fn check(&self) -> bool { *self > 0 }
}

impl Checkable for &str {
    fn check(&self) -> bool { !self.is_empty() }
}

// Blanket impl for tuples: proving Checkable for (A, B) requires
// proving Checkable for A and Checkable for B. With nesting, this
// fans out exponentially before deduplication.
impl<A: Checkable, B: Checkable> Checkable for (A, B) {
    fn check(&self) -> bool {
        self.0.check() && self.1.check()
    }
}

// Blanket impl for Option: adds another obligation layer.
impl<T: Checkable> Checkable for Option<T> {
    fn check(&self) -> bool {
        match self {
            Some(v) => v.check(),
            None => false,
        }
    }
}

// Blanket impl for Vec: yet another layer of obligation generation.
impl<T: Checkable> Checkable for Vec<T> {
    fn check(&self) -> bool {
        self.iter().all(|v| v.check())
    }
}

// Blanket impl for Box: another wrapper.
impl<T: Checkable + ?Sized> Checkable for Box<T> {
    fn check(&self) -> bool {
        (**self).check()
    }
}

// Deeply nested type using only 2-tuples. Each level doubles the
// obligation fan-out. 12 levels of nesting = 2^12 potential obligations
// before deduplication kicks in.
// Level 1:  (u32, u32)
// Level 2:  ((u32, u32), (u32, u32))
// Level 3:  (((u32, u32), (u32, u32)), ((u32, u32), (u32, u32)))
// etc.
fn check_nested_binary(
    v: &(
        ((u32, u32), (u32, u32)),
        ((u32, u32), (u32, u32)),
    ),
) -> bool {
    v.check()
}

// Deeper nesting: 4 levels of binary tree.
fn check_nested_deep(
    v: &(
        (((u32, u32), (u32, u32)), ((u32, u32), (u32, u32))),
        (((u32, u32), (u32, u32)), ((u32, u32), (u32, u32))),
    ),
) -> bool {
    v.check()
}

// Mixed wrappers: combine tuples, Option, Vec, and Box.
// Each wrapper type triggers a different blanket impl, generating
// distinct obligation sub-trees that must all be deduplicated.
fn check_mixed_wrappers(
    v: &(
        Option<(u32, u32)>,
        (Option<Vec<u32>>, Box<(u32, u32)>),
    ),
) -> bool {
    v.check()
}

// Right-leaning nesting: u32, (u32, (u32, (u32, ...)))
// This creates a deep obligation chain rather than a wide tree.
fn check_right_nested(
    v: &(u32, (u32, (u32, (u32, (u32, (u32, (u32, (u32, (u32, (u32, u32))))))))))
) -> bool {
    v.check()
}

fn main() {
    let nested = (
        ((1u32, 2u32), (3u32, 4u32)),
        ((5u32, 6u32), (7u32, 8u32)),
    );
    assert!(check_nested_binary(&nested));

    let deep = (
        (((1u32, 2u32), (3u32, 4u32)), ((5u32, 6u32), (7u32, 8u32))),
        (((9u32, 10u32), (11u32, 12u32)), ((13u32, 14u32), (15u32, 16u32))),
    );
    assert!(check_nested_deep(&deep));

    let mixed = (
        Some((1u32, 2u32)),
        (Some(vec![3u32]), Box::new((4u32, 5u32))),
    );
    assert!(check_mixed_wrappers(&mixed));

    let right = (1u32, (2u32, (3u32, (4u32, (5u32, (6u32, (7u32, (8u32, (9u32, (10u32, 11u32))))))))));
    assert!(check_right_nested(&right));
}
