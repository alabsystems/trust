#![allow(dead_code, unused_assignments)]

struct Inner {
    small: u16,
    wide: u64,
}

struct Nested {
    left: Inner,
    field: u64,
    right: Inner,
}

pub fn nested_assignment() -> u64 {
    let mut a = [
        Nested { left: Inner { small: 1, wide: 2 }, field: 3, right: Inner { small: 4, wide: 5 } },
        Nested { left: Inner { small: 6, wide: 7 }, field: 8, right: Inner { small: 9, wide: 10 } },
    ];
    a[1].field = 11;
    a[0].left.small as u64 + a[0].left.wide * 2 + a[0].field * 3
        + a[0].right.small as u64 * 4 + a[0].right.wide * 5
        + a[1].left.small as u64 * 6 + a[1].left.wide * 7 + a[1].field * 8
        + a[1].right.small as u64 * 9 + a[1].right.wide * 10
}

pub fn nested_compound_effects() -> u64 {
    let mut a = [Nested {
        left: Inner { small: 1, wide: 2 }, field: 3, right: Inner { small: 4, wide: 5 },
    }];
    let mut n = 0;
    a[{ n = n * 10 + 1; 0 }].field += {
        a = [Nested {
            left: Inner { small: 6, wide: 7 }, field: 8, right: Inner { small: 9, wide: 10 },
        }];
        n = n * 10 + 2;
        11
    };
    n * 1_000_000 + a[0].left.small as u64 * 100_000 + a[0].left.wide * 10_000
        + a[0].field * 100 + a[0].right.small as u64 * 10 + a[0].right.wide
}

struct TupleSibling {
    before: (u64, bool),
    field: u64,
    after: (u16, u64),
}

pub fn nested_tuple_siblings() -> u64 {
    let mut a = [TupleSibling { before: (1, true), field: 2, after: (3, 4) }];
    a[0].field += 5;
    a[0].before.0 * 1000 + if a[0].before.1 { 100 } else { 0 }
        + a[0].field * 10 + a[0].after.0 as u64 + a[0].after.1
}

struct ArraySibling {
    before: [u16; 2],
    field: u64,
    after: [Inner; 2],
}

pub fn nested_array_siblings() -> u64 {
    let mut a = [ArraySibling {
        before: [1, 2], field: 3,
        after: [Inner { small: 4, wide: 5 }, Inner { small: 6, wide: 7 }],
    }];
    a[0].field *= 8;
    a[0].before[0] as u64 + a[0].before[1] as u64 * 2 + a[0].field * 3
        + a[0].after[0].small as u64 * 4 + a[0].after[0].wide * 5
        + a[0].after[1].small as u64 * 6 + a[0].after[1].wide * 7
}

struct DropInner;
impl Drop for DropInner {
    fn drop(&mut self) {}
}
struct DropSibling {
    inner: DropInner,
    field: u64,
}

pub fn nested_drop_refused() -> u64 {
    let mut a = [DropSibling { inner: DropInner, field: 1 }];
    a[0].field += 1;
    a[0].field
}

struct PointerSibling {
    inner: *const u64,
    field: u64,
}

pub fn nested_pointer_refused() -> u64 {
    let value = 3;
    let mut a = [PointerSibling { inner: &value, field: 1 }];
    a[0].field += 1;
    a[0].field
}

enum Choice { First(u64), Second }
struct EnumSibling {
    inner: Choice,
    field: u64,
}

pub fn nested_enum_refused() -> u64 {
    let mut a = [EnumSibling { inner: Choice::First(3), field: 1 }];
    a[0].field += 1;
    a[0].field
}
