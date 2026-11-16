#![allow(dead_code, unused_assignments, unused_mut, unused_variables)]
#![allow(unreachable_code, unconditional_panic)]

// The second field is at a nonzero byte offset. Value surgery must select the
// field by its descriptor index and retain both neighboring fields/elements.
#[repr(C)]
struct Cell {
    guard: u32,
    field: u32,
}

pub fn field_index_effectful_order() -> u32 {
    let mut a = [Cell { guard: 1, field: 2 }, Cell { guard: 3, field: 4 }];
    let mut n = 0u32;
    a[{ n = n * 10 + 1; 0 }].field = { n = n * 10 + 2; 7 };
    n * 10000 + a[0].guard * 1000 + a[0].field * 100 + a[1].guard * 10 + a[1].field
}

pub fn rhs_replaces_array() -> u32 {
    let mut a = [Cell { guard: 1, field: 2 }, Cell { guard: 3, field: 4 }];
    a[0].field = {
        a = [Cell { guard: 5, field: 6 }, Cell { guard: 7, field: 8 }];
        9
    };
    a[0].guard * 1000 + a[0].field * 100 + a[1].guard * 10 + a[1].field
}

pub fn index_replaces_array() -> u32 {
    let mut a = [Cell { guard: 1, field: 2 }, Cell { guard: 3, field: 4 }];
    a[{
        a = [Cell { guard: 5, field: 6 }, Cell { guard: 7, field: 8 }];
        0
    }].field = 9;
    a[0].guard * 1000 + a[0].field * 100 + a[1].guard * 10 + a[1].field
}

pub fn nested_index_assignment() -> u32 {
    let mut a = [Cell { guard: 1, field: 2 }, Cell { guard: 3, field: 4 }];
    let mut n = 0;
    a[{ a[1].field = { n = n * 10 + 2; 8 }; n = n * 10 + 3; 0 }].field = {
        n = n * 10 + 1;
        7
    };
    n * 10000 + a[0].guard * 1000 + a[0].field * 100 + a[1].guard * 10 + a[1].field
}

pub fn loop_field_update() -> u32 {
    let mut a = [Cell { guard: 1, field: 2 }, Cell { guard: 3, field: 4 }];
    let mut i = 0;
    while i < 2 {
        a[i].field = a[i].field + 10;
        i += 1;
    }
    a[0].guard * 1000 + a[0].field * 100 + a[1].guard * 10 + a[1].field
}

#[repr(C)]
struct FloatCell {
    guard: f32,
    field: f64,
}

pub fn float_fields_update() -> u32 {
    let mut a = [FloatCell { guard: 1.25, field: 2.5 }, FloatCell { guard: 3.75, field: 4.5 }];
    a[1].field = 6.5;
    a[0].guard = 2.25;
    if a[0].guard == 2.25 && a[0].field == 2.5 && a[1].guard == 3.75 && a[1].field == 6.5 {
        1
    } else {
        0
    }
}

pub fn rhs_return_before_bounds() -> u32 {
    let mut a = [Cell { guard: 1, field: 2 }];
    a[9].field = { return 29; };
    0
}

pub fn index_return_after_rhs() -> u32 {
    let mut a = [Cell { guard: 1, field: 2 }];
    let mut n = 1;
    a[{ return n; 0usize }].field = { n = n * 10 + 1; 7 };
    0
}

pub fn bounds_panic() -> u32 {
    let mut a = [Cell { guard: 1, field: 2 }];
    let mut n = 0;
    a[{ n += 1; 9 }].field = { n += 2; 7 };
    n
}

pub fn bounds_panic_predecessor() -> u32 {
    let mut a = [Cell { guard: 1, field: 2 }];
    let index = 9usize;
    let mut n = 1;
    if n == 1 {
        n += 1;
    } else {
        n += 2;
    }
    a[index].field = { n += 3; 7 };
    n
}

pub fn rhs_borrow_refused() -> u32 {
    let mut a = [Cell { guard: 1, field: 2 }];
    a[0].field = { let p = &mut a; p[0].guard = 3; 7 };
    a[0].guard * 10 + a[0].field
}

pub fn index_borrow_refused() -> u32 {
    let mut a = [Cell { guard: 1, field: 2 }];
    a[{ let p = &mut a; p[0].guard = 3; 0 }].field = 7;
    a[0].guard * 10 + a[0].field
}

struct Droppy {
    field: u32,
}

impl Drop for Droppy {
    fn drop(&mut self) {}
}

pub fn needs_drop_refused() -> u32 {
    let mut a = [Droppy { field: 2 }];
    a[0].field = 7;
    a[0].field
}

struct Nested {
    inner: Cell,
    field: u32,
}

pub fn non_scalar_sibling_refused() -> u32 {
    let mut a = [Nested { inner: Cell { guard: 1, field: 2 }, field: 3 }];
    a[0].field = 7;
    a[0].inner.guard * 100 + a[0].inner.field * 10 + a[0].field
}
