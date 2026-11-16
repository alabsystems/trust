#![allow(dead_code, unused_assignments, unused_mut, unused_variables, unreachable_code, unconditional_panic)]

#[repr(C)]
struct Cell {
    guard: u64,
    field: u64,
}

pub fn compound_effect_order() -> u64 {
    let mut a = [Cell { guard: 1, field: 2 }, Cell { guard: 3, field: 4 }];
    let mut n = 0;
    a[{ n = n * 10 + 1; 0 }].field += { n = n * 10 + 2; 7 };
    n * 10000 + a[0].guard * 1000 + a[0].field * 100 + a[1].guard * 10 + a[1].field
}

pub fn compound_rhs_replaces_array() -> u64 {
    let mut a = [Cell { guard: 1, field: 2 }, Cell { guard: 3, field: 4 }];
    a[0].field += {
        a = [Cell { guard: 5, field: 6 }, Cell { guard: 7, field: 8 }];
        9
    };
    a[0].guard * 10000 + a[0].field * 100 + a[1].guard * 10 + a[1].field
}

pub fn compound_index_replaces_array() -> u64 {
    let mut a = [Cell { guard: 1, field: 2 }, Cell { guard: 3, field: 4 }];
    a[{
        a = [Cell { guard: 5, field: 6 }, Cell { guard: 7, field: 8 }];
        0
    }].field += 9;
    a[0].guard * 10000 + a[0].field * 100 + a[1].guard * 10 + a[1].field
}

pub fn compound_nested() -> u64 {
    let mut a = [Cell { guard: 1, field: 2 }, Cell { guard: 3, field: 4 }];
    let mut n = 0;
    a[{
        a[1].field += { n = n * 10 + 2; 8 };
        n = n * 10 + 3;
        0
    }].field += { n = n * 10 + 1; 7 };
    n * 10000 + a[0].guard * 1000 + a[0].field * 100 + a[1].guard * 10 + a[1].field
}

pub fn compound_loop() -> u64 {
    let mut a = [Cell { guard: 1, field: 2 }, Cell { guard: 3, field: 4 }];
    let mut i = 0;
    while i < 2 {
        a[i].field += 10;
        i += 1;
    }
    a[0].guard * 1000 + a[0].field * 100 + a[1].guard * 10 + a[1].field
}

pub fn compound_mixed_shift(shift: u64) -> u64 {
    let mut a = [Cell { guard: 1, field: 2 }, Cell { guard: 3, field: 4 }];
    a[1].field <<= shift as u32;
    a[1].field ^ a[0].field
}

#[repr(C)]
struct FloatCell {
    guard: f32,
    field: f64,
}

pub fn compound_float() -> u64 {
    let mut a = [FloatCell { guard: 1.25, field: 2.5 }, FloatCell { guard: 3.75, field: 4.5 }];
    a[1].field *= 2.0;
    a[0].guard += 1.0;
    if a[0].guard == 2.25 && a[0].field == 2.5 && a[1].guard == 3.75 && a[1].field == 9.0 {
        1
    } else {
        0
    }
}

pub fn compound_rhs_return_before_bounds() -> u64 {
    let mut a = [Cell { guard: 1, field: 2 }];
    a[9].field += { return 29; 0u64 };
    0
}

pub fn compound_index_return_after_rhs() -> u64 {
    let mut a = [Cell { guard: 1, field: 2 }];
    let mut n = 1;
    a[{ return n; 0usize }].field += { n = n * 10 + 1; 7 };
    0
}

pub fn compound_bounds(index: u64) -> u64 {
    let mut a = [Cell { guard: 1, field: 2 }];
    a[index as usize].field += 1;
    a[0].field
}

pub fn compound_checked_add(rhs: u64) -> u64 {
    let mut a = [Cell { guard: 1, field: u64::MAX }];
    a[0].field += rhs;
    a[0].field
}

pub fn compound_divisor(rhs: u64) -> u64 {
    let mut a = [Cell { guard: 1, field: 17 }];
    a[0].field /= rhs;
    a[0].field
}

struct SignedCell {
    guard: i64,
    field: i64,
}

pub fn compound_signed_divisor(rhs: u64) -> u64 {
    let mut a = [SignedCell { guard: 1, field: i64::MIN }];
    a[0].field /= rhs as i64;
    a[0].field as u64
}

pub fn compound_bit_ops(x: u64) -> u64 {
    let mut a = [Cell { guard: 1, field: x }];
    a[0].field |= 0xf0;
    a[0].field ^= 0x35;
    a[0].field &= 0xff;
    a[0].field >>= 3u8;
    a[0].field
}

pub fn compound_sub_mul_rem(x: u64) -> u64 {
    let mut a = [Cell { guard: 1, field: (x & 255) + 10 }];
    a[0].field -= 3;
    a[0].field *= 5;
    a[0].field %= 17;
    a[0].field
}

pub fn compound_borrowed_refused(rhs: u64) -> u64 {
    let mut a = [Cell { guard: 1, field: 2 }];
    let p = &mut a;
    p[0].field += rhs;
    p[0].field
}

struct Droppy {
    field: u64,
}

impl Drop for Droppy {
    fn drop(&mut self) {}
}

pub fn compound_drop_refused(rhs: u64) -> u64 {
    let mut a = [Droppy { field: 2 }];
    a[0].field += rhs;
    a[0].field
}

struct Nested {
    inner: Cell,
    field: u64,
}

pub fn compound_nested_sibling_refused(rhs: u64) -> u64 {
    let mut a = [Nested { inner: Cell { guard: 1, field: 2 }, field: 3 }];
    a[0].field += rhs;
    a[0].inner.guard + a[0].inner.field + a[0].field
}
