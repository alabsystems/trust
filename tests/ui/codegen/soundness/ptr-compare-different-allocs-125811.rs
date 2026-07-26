// Regression test for rust-lang#125811.
// LLVM miscompiles comparison of pointers derived from different
// allocations: LLVM's alias analysis and pointer comparison folding
// can incorrectly assume that pointers from different allocations
// never compare equal. This is unsound because:
//
// 1. When one heap allocation is freed and another is created, the
//    new allocation may reuse the same address
// 2. When one stack variable ends at the exact byte where another
//    begins, their one-past-the-end and start pointers are equal
// 3. LLVM may fold `ptr_a == ptr_b` to `false` at compile time when
//    it can prove they derive from different allocations, even though
//    at runtime the addresses may coincide
//
// This is a provenance-vs-address issue: two pointers with different
// provenance can have the same address. Rust (via the Stacked Borrows
// or Tree Borrows models) permits address comparison across
// allocations — the result must reflect runtime addresses, not
// compile-time provenance reasoning.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//@ build-pass
//@ compile-flags: -C opt-level=2

#![allow(dead_code)]

use std::ptr;

// Compare pointers from two different stack allocations.
// The optimizer must not fold this to `false` based on provenance alone.
#[inline(never)]
fn compare_stack_ptrs(a: *const u8, b: *const u8) -> bool {
    ptr::eq(a, b)
}

// Compare one-past-the-end of one array with the start of the next.
// On many ABIs, consecutive stack allocations may be adjacent, making
// these pointers equal at runtime.
#[inline(never)]
fn compare_adjacent_ends(a: &[u8], b: &[u8]) -> bool {
    let end_a = a.as_ptr().wrapping_add(a.len());
    let start_b = b.as_ptr();
    // This comparison must be computed at runtime, not folded away.
    end_a == start_b
}

// Compare pointers after round-tripping through usize.
// addr_of(x) as usize == addr_of(y) as usize must behave consistently
// with addr_of(x) == addr_of(y).
#[inline(never)]
fn compare_via_usize(a: *const u32, b: *const u32) -> bool {
    let addr_a = a as usize;
    let addr_b = b as usize;
    addr_a == addr_b
}

// Compare pointers to fields within a struct vs. a separate allocation.
// LLVM must not use allocation identity to short-circuit this comparison.
struct TwoFields {
    first: u64,
    second: u64,
}

#[inline(never)]
fn compare_field_ptrs(s: &TwoFields, external: *const u64) -> (bool, bool) {
    let p_first = ptr::addr_of!(s.first);
    let p_second = ptr::addr_of!(s.second);
    (p_first == external, p_second == external)
}

// Pointer comparison in a loop — the optimizer might attempt to hoist
// or eliminate the comparison based on allocation provenance.
#[inline(never)]
fn find_matching_ptr(haystack: &[*const u8], needle: *const u8) -> Option<usize> {
    for (i, &p) in haystack.iter().enumerate() {
        if p == needle {
            return Some(i);
        }
    }
    None
}

// Box (heap) allocation: after dropping a Box and creating a new one,
// the allocator may return the same address. Pointer comparison must
// reflect runtime addresses.
#[inline(never)]
fn heap_reuse_compare() -> bool {
    let b1 = Box::new(42u64);
    let addr1 = &*b1 as *const u64;
    let addr1_val = addr1 as usize;
    drop(b1);

    let b2 = Box::new(99u64);
    let addr2 = &*b2 as *const u64;
    let addr2_val = addr2 as usize;
    drop(b2);

    // Whether these are equal depends on the allocator, but the
    // comparison itself must be computed at runtime, not folded to false.
    // We verify consistency between pointer and integer comparison.
    (addr1_val == addr2_val) == (addr1 == addr2)
}

fn main() {
    // Self-comparison: a pointer must always equal itself, regardless
    // of what provenance analysis says.
    let x: u8 = 1;
    let p = &x as *const u8;
    assert!(compare_stack_ptrs(p, p));

    // Same address via different references: create a reference, cast
    // to raw, compare — must be equal.
    let y: u8 = 2;
    let p1 = &y as *const u8;
    let p2 = &y as *const u8;
    assert!(compare_stack_ptrs(p1, p2));

    // Different allocations: these should NOT be equal (distinct stack slots).
    let a: u8 = 10;
    let b: u8 = 20;
    let pa = &a as *const u8;
    let pb = &b as *const u8;
    // We cannot assert inequality (the compiler might place them adjacently),
    // but we CAN assert the comparison is consistent with usize comparison.
    assert_eq!(
        (pa == pb),
        (pa as usize == pb as usize),
    );

    // Adjacent-end comparison: verify runtime consistency.
    let arr1 = [1u8, 2, 3];
    let arr2 = [4u8, 5, 6];
    let adjacent_result = compare_adjacent_ends(&arr1, &arr2);
    // Result depends on layout; verify consistency with address arithmetic.
    let expected = arr1.as_ptr().wrapping_add(arr1.len()) as usize == arr2.as_ptr() as usize;
    assert_eq!(adjacent_result, expected);

    // usize round-trip comparison consistency.
    let v1: u32 = 100;
    let v2: u32 = 200;
    let pv1 = &v1 as *const u32;
    let pv2 = &v2 as *const u32;
    // Same pointer must compare equal through usize.
    assert!(compare_via_usize(pv1, pv1));
    // Different pointers: result must be consistent.
    assert_eq!(compare_via_usize(pv1, pv2), (pv1 == pv2));

    // Field pointer comparison.
    let s = TwoFields { first: 1, second: 2 };
    let ext = &s.first as *const u64;
    let (eq_first, eq_second) = compare_field_ptrs(&s, ext);
    assert!(eq_first); // Same field, must be equal.
    assert!(!eq_second); // Different field at different offset.

    // Haystack search: find a pointer among a set of pointers from
    // different allocations.
    let vals = [1u8, 2, 3, 4];
    let ptrs: Vec<*const u8> = vals.iter().map(|v| v as *const u8).collect();
    let needle = &vals[2] as *const u8;
    assert_eq!(find_matching_ptr(&ptrs, needle), Some(2));

    // Heap reuse: comparison must be computed at runtime.
    assert!(heap_reuse_compare());
}
