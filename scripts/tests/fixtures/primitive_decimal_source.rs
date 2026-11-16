#![allow(dead_code)]
use std::fmt;

pub fn requested_capacity(n: usize) -> usize {
    let s = n.to_string();
    s.len() + s.len() / 3
}
pub fn bounded_allocation(n: usize) -> String {
    let s = n.to_string();
    String::with_capacity(s.len() + s.len() / 3)
}
pub fn direct_heap_mutation(n: usize) -> usize {
    let mut s = n.to_string();
    s.push_str("abcdefghijklmnopqrstu");
    s.len() + (usize::MAX - 20)
}
pub fn alias_heap_mutation(n: usize) -> usize {
    let mut s = n.to_string();
    let p = &mut s;
    p.push_str("abcdefghijklmnopqrstu");
    s.len() + (usize::MAX - 20)
}
pub fn moved_heap_mutation(n: usize) -> usize {
    let s = n.to_string();
    let mut moved = s;
    moved.push_str("abcdefghijklmnopqrstu");
    moved.len() + (usize::MAX - 20)
}
pub fn replaced_string(n: usize) -> usize {
    let mut s = n.to_string();
    std::hint::black_box(&s);
    s = String::from("abcdefghijklmnopqrstu");
    s.len() + (usize::MAX - 20)
}
pub fn numeric_return_reassigned(n: usize) -> usize {
    let mut len = n.to_string().len();
    std::hint::black_box(len);
    len = std::hint::black_box(usize::MAX);
    len + 1
}
pub fn real_overflow(n: usize) -> usize {
    n.to_string().len() + usize::MAX
}
struct Loud;
impl fmt::Display for Loud {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("abcdefghijklmnopqrstu")
    }
}
pub fn custom_display() -> usize {
    let s = Loud.to_string();
    s.len() + (usize::MAX - 20)
}
trait PrivateToString {
    fn to_string(&self) -> String;
}
impl PrivateToString for u64 {
    fn to_string(&self) -> String {
        String::from("abcdefghijklmnopqrstu")
    }
}
pub fn custom_trait(n: u64) -> usize {
    let s = PrivateToString::to_string(&n);
    s.len() + (usize::MAX - 20)
}
pub fn generic_display<T: fmt::Display>(n: &T) -> usize {
    let s = n.to_string();
    s.len()
}
pub fn float_display(n: f64) -> usize {
    let s = n.to_string();
    s.len()
}
pub fn extra_reference(n: u64) -> usize {
    let s = ToString::to_string(&&n);
    s.len()
}

mod foreign {
    // A real foreign-ABI MIR call with the same method spelling supplies no
    // compiler-owned ToString trait identity. This local definition makes the
    // native negative self-contained; no unavailable external library is used.
    #[allow(improper_ctypes_definitions)]
    pub extern "C" fn to_string(_: &u64) -> String {
        String::from("abcdefghijklmnopqrstu")
    }
}
pub fn foreign_call(n: u64) -> usize {
    let s = foreign::to_string(&n);
    s.len() + (usize::MAX - 20)
}

// Byte-identical frozen TY04c function; the wrapper only exposes native checks.
fn format_number(n: usize) -> String {
    let s = n.to_string();
    let mut result = String::with_capacity(s.len() + s.len() / 3);
    for (i, c) in s.chars().rev().enumerate() {
        if i > 0 && i % 3 == 0 {
            result.push(',');
        }
        result.push(c);
    }
    result.chars().rev().collect()
}
pub fn real_ty_format_number(n: usize) -> String { format_number(n) }
