// Regression test for rust-lang#109839.
// Incorrect codegen for thin pointer to unsized type: when a pointer to
// an unsized type (like a trait object or slice) was cast or coerced in
// certain ways, LLVM could generate code that treated it as a thin
// pointer (single word) instead of a fat pointer (data + metadata),
// losing the vtable or length information.
//
// The bug manifested when:
// 1. A concrete type was coerced to a trait object through a reference
// 2. The optimizer attempted to "thin" the pointer in intermediate steps
// 3. The vtable/length metadata was dropped, causing UB on dereference
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//@ build-pass
//@ compile-flags: -C opt-level=2

#![allow(dead_code)]

use std::fmt;

trait Describe {
    fn describe(&self) -> &'static str;
}

struct Alpha;
struct Beta(u64);
struct Gamma { x: f64, y: f64 }

impl Describe for Alpha {
    fn describe(&self) -> &'static str { "Alpha" }
}

impl Describe for Beta {
    fn describe(&self) -> &'static str { "Beta" }
}

impl Describe for Gamma {
    fn describe(&self) -> &'static str { "Gamma" }
}

// Force the trait object through a function boundary so the optimizer
// cannot devirtualize trivially.
#[inline(never)]
fn describe_via_trait_object(obj: &dyn Describe) -> &'static str {
    obj.describe()
}

// Pass trait object through a generic wrapper to stress pointer coercion.
#[inline(never)]
fn describe_boxed(obj: Box<dyn Describe>) -> &'static str {
    obj.describe()
}

// Slice coercion: array reference to slice reference must preserve length.
#[inline(never)]
fn sum_slice(data: &[u32]) -> u32 {
    data.iter().sum()
}

// Nested coercion: &Box<dyn Trait> should still dispatch correctly.
#[inline(never)]
fn describe_ref_boxed(obj: &Box<dyn Describe>) -> &'static str {
    obj.describe()
}

// Exercise fmt::Display trait objects — a common real-world pattern.
#[inline(never)]
fn format_display(obj: &dyn fmt::Display) -> String {
    format!("{}", obj)
}

fn main() {
    // Direct trait object coercion.
    let a = Alpha;
    let b = Beta(42);
    let g = Gamma { x: 1.0, y: 2.0 };

    assert_eq!(describe_via_trait_object(&a), "Alpha");
    assert_eq!(describe_via_trait_object(&b), "Beta");
    assert_eq!(describe_via_trait_object(&g), "Gamma");

    // Boxed trait objects.
    assert_eq!(describe_boxed(Box::new(Alpha)), "Alpha");
    assert_eq!(describe_boxed(Box::new(Beta(99))), "Beta");
    assert_eq!(describe_boxed(Box::new(Gamma { x: 0.0, y: 0.0 })), "Gamma");

    // Slice coercion from fixed-size array.
    let arr = [1u32, 2, 3, 4, 5];
    assert_eq!(sum_slice(&arr), 15);
    assert_eq!(sum_slice(&arr[1..4]), 9); // 2 + 3 + 4

    // Nested box reference.
    let boxed: Box<dyn Describe> = Box::new(Beta(0));
    assert_eq!(describe_ref_boxed(&boxed), "Beta");

    // Display trait objects with different concrete types.
    let n: i32 = 42;
    let s: &str = "hello";
    assert_eq!(format_display(&n), "42");
    assert_eq!(format_display(&s), "hello");
}
