//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ compile-flags: --crate-type=lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-pass
//! Every fixed-size array TYPE is ONE first-class `Ty::Array` in the THIR producer, whatever
//! its element and whatever its length, so mapping a type costs its TEXT and never its length.
//!
//! Until 2026-09-23 the producer spelled an array whose element was not a scalar, float,
//! struct or enum — a tuple, `()`, a reference, a fat pointer, a fn pointer, another array — as
//! a tuple of N copies of the element type, built eagerly with `vec![elem; n]` inside
//! `mir_built`. tests/ui/const-generics/transmute-fail.rs's `[[[u32; 8888888]; 9999999];
//! 777777777]` asked for ~7e15 of them and took the machine down with it (the 2026-09-21
//! incident). Each signature below must now compile in the memory an ordinary three-line
//! function takes.
//!
//! WHAT THIS FILE DISCRIMINATES, measured one function per file under a 4 GiB ceiling on the
//! pre-change compiler (7bc480faf): `nested_zst` and `unit_4e9` grew into the ceiling and were
//! killed. The rest are CONTROLS that were already bounded there (a reference's pointee is not
//! mapped until it is used, and their element reads are refused at the `Index` lane, in
//! constant memory); they pin that arrays of tuples, references, `&str`, fn pointers and nested
//! arrays at these lengths STAY bounded, not that anything changed for them.
//!
//! compiletest imposes no memory ceiling, so a regression here is a machine-sized compile, not a
//! red test. To probe one safely, compile it directly under a ceiling:
//! `taskpolicy -m 4096 <stage1 Mach-O rustc> -Ztrust-verify=on --crate-type=lib <this file>`.
//!
//! Only TYPES are huge here: no value of a huge array is built (a huge `[x; N]` VALUE, and a
//! tuple/struct CONSTRUCTED over a huge array, are separate, still value-proportional lanes
//! until trust-ir has a uniform-array value — see
//! trust_ir_huge_array_construction_value_proportional.rs).

#![allow(dead_code)]

// transmute-fail's `overflow` shape, with a zero-sized element so the transmute is valid: two
// nested arrays of ~7e15 zero-sized elements each, both spelled as three constant-size types.
pub fn nested_zst(
    v: [[[(); 8888888]; 9999999]; 777777777],
) -> [[[(); 9999999]; 777777777]; 8888888] {
    unsafe { std::mem::transmute(v) }
}

// The `[(); N]` canary lengths of tests/ui/consts/huge-values.rs and
// tests/ui/consts/large-zst-array-77062.rs, as parameter and return types.
pub fn unit_4e9(v: [(); 4_000_000_000]) -> [(); 4_000_000_000] {
    v
}

// A CONTROL: the largest `[(); N]`, behind a reference.
pub fn unit_max(v: &[(); usize::MAX]) -> &[(); usize::MAX] {
    v
}

// A CONTROL: a nested array of non-zero-sized elements (3.5e14 bytes), read through a
// reference at its last element.
pub fn nested(v: &[[u32; 8888888]; 9999999]) -> u32 {
    v[9999998][8888887]
}

// CONTROLS from here down (see the header): arrays of tuples, references, fat pointers and fn
// pointers behind a reference, and a struct field of nested arrays read at one cell.
pub fn tuples(v: &[(u8, u16); 1_000_000_000]) -> u16 {
    v[999_999_999].1
}

pub fn refs<'a>(v: &[&'a u64; 3_000_000_000]) -> &'a u64 {
    v[2_999_999_999]
}

pub fn strs<'a>(v: &[&'a str; 2_000_000_000]) -> &'a str {
    v[7]
}

pub fn fn_ptrs(v: &[fn() -> u8; 2_000_000_000]) -> fn() -> u8 {
    v[1]
}

// A struct FIELD of huge nested-array type (2e10 bytes), read at one cell.
pub struct Grid {
    cells: [[(u8, bool); 100_000]; 100_000],
}

pub fn cell(g: &Grid) -> bool {
    g.cells[99_999][99_999].1
}
