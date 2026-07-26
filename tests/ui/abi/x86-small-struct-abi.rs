// Trust: Regression test for rust-lang#102174 / #921
// Small structs should be passed correctly on i386 per System V ABI.
// Over-aligned structs (alignment > 4 bytes) must be passed indirectly,
// not via byval, because the x86-32 stack is only 4-byte aligned.
//
//@ check-pass
//@ only-x86

#[repr(C)]
#[derive(Clone, Copy)]
struct Small4 {
    a: u32,
}

#[repr(C)]
#[derive(Clone, Copy)]
struct Small8 {
    a: u32,
    b: u32,
}

#[repr(C)]
#[derive(Clone, Copy)]
struct Large12 {
    a: u32,
    b: u32,
    c: u32,
}

// Trust: #921 — Over-aligned struct that must go indirect on x86-32.
// Alignment of 8 exceeds the 4-byte stack alignment guarantee,
// so clang passes this indirectly (pointer) instead of byval.
#[repr(C, align(8))]
#[derive(Clone, Copy)]
struct OverAligned {
    a: u32,
    b: u32,
}

// Trust: #921 — Single-element float struct (returned in FP register
// on platforms with abi_return_struct_as_int).
#[repr(C)]
#[derive(Clone, Copy)]
struct SingleFloat {
    a: f32,
}

#[repr(C)]
#[derive(Clone, Copy)]
struct SingleDouble {
    a: f64,
}

extern "C" fn takes_small4(s: Small4) -> Small4 {
    s
}

extern "C" fn takes_small8(s: Small8) -> Small8 {
    s
}

extern "C" fn takes_large12(s: Large12) -> Large12 {
    s
}

extern "C" fn takes_overaligned(s: OverAligned) -> OverAligned {
    s
}

extern "C" fn takes_single_float(s: SingleFloat) -> SingleFloat {
    s
}

extern "C" fn takes_single_double(s: SingleDouble) -> SingleDouble {
    s
}

fn main() {
    let s4 = Small4 { a: 1 };
    let r4 = takes_small4(s4);
    assert_eq!(r4.a, 1);

    let s8 = Small8 { a: 1, b: 2 };
    let r8 = takes_small8(s8);
    assert_eq!(r8.a, 1);
    assert_eq!(r8.b, 2);

    let s12 = Large12 { a: 1, b: 2, c: 3 };
    let r12 = takes_large12(s12);
    assert_eq!(r12.a, 1);
    assert_eq!(r12.b, 2);
    assert_eq!(r12.c, 3);

    let so = OverAligned { a: 1, b: 2 };
    let ro = takes_overaligned(so);
    assert_eq!(ro.a, 1);
    assert_eq!(ro.b, 2);

    let sf = SingleFloat { a: 3.14 };
    let rf = takes_single_float(sf);
    assert_eq!(rf.a, 3.14);

    let sd = SingleDouble { a: 2.718281828 };
    let rd = takes_single_double(sd);
    assert_eq!(rd.a, 2.718281828);
}
