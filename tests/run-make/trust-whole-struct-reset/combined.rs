//! One registered scalar struct used by both replacement and indexed-field writes.

#[repr(C)]
struct Cell {
    guard: u32,
    field: u32,
}

pub fn combined_type_registration() -> u32 {
    let mut state = Cell { guard: 5, field: 6 };
    let reference = &mut state;
    let prior = reference.guard;
    *reference = Cell { guard: 7, field: 8 };
    reference.guard = prior + 1;
    let mut a = [Cell { guard: 1, field: 2 }, Cell { guard: 3, field: 4 }];
    let mut order = 0u32;
    a[{ order = order * 10 + 1; 1 }].field = {
        order = order * 10 + 2;
        state.field
    };
    order * 1_000_000 + a[0].guard * 100_000 + a[0].field * 10_000
        + a[1].guard * 1_000 + a[1].field * 100 + state.guard * 10 + state.field
}
