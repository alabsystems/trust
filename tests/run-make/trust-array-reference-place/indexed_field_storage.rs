#[repr(C)]
struct Cell { guard: u32, field: u32 }

pub fn rhs_mut_reseat() -> u32 {
    let mut a = [Cell { guard: 11, field: 12 }, Cell { guard: 21, field: 22 }];
    a[1].field = {
        let p = &mut a;
        *p = [Cell { guard: 31, field: 32 }, Cell { guard: 41, field: 42 }];
        7
    };
    a[0].guard * 100_000 + a[0].field * 1_000 + a[1].guard * 10 + a[1].field
}

pub fn index_mut_reseat() -> u32 {
    let mut a = [Cell { guard: 11, field: 12 }, Cell { guard: 21, field: 22 }];
    a[{
        let p = &mut a;
        *p = [Cell { guard: 31, field: 32 }, Cell { guard: 41, field: 42 }];
        1
    }].field = 7;
    a[0].guard * 100_000 + a[0].field * 1_000 + a[1].guard * 10 + a[1].field
}

pub fn rhs_mut_field() -> u32 {
    let mut a = [Cell { guard: 11, field: 12 }, Cell { guard: 21, field: 22 }];
    a[1].field = {
        let p = &mut a;
        p[0].guard = 31;
        7
    };
    a[0].guard * 100_000 + a[0].field * 1_000 + a[1].guard * 10 + a[1].field
}

pub fn index_mut_field() -> u32 {
    let mut a = [Cell { guard: 11, field: 12 }, Cell { guard: 21, field: 22 }];
    a[{
        let p = &mut a;
        p[0].guard = 31;
        1
    }].field = 7;
    a[0].guard * 100_000 + a[0].field * 1_000 + a[1].guard * 10 + a[1].field
}

pub fn rhs_mut_loan_read() -> u32 {
    let mut a = [Cell { guard: 11, field: 12 }, Cell { guard: 21, field: 22 }];
    a[1].field = {
        let p = &mut a;
        p[0].field
    };
    a[0].guard * 100_000 + a[0].field * 1_000 + a[1].guard * 10 + a[1].field
}

pub fn shared_identity_then_store() -> u32 {
    let mut a = [Cell { guard: 11, field: 12 }, Cell { guard: 21, field: 22 }];
    let before = &a as *const [Cell; 2];
    a[1].field = 7;
    let after = &a as *const [Cell; 2];
    (before == after) as u32 * 10_000_000
        + a[0].guard * 100_000 + a[0].field * 1_000 + a[1].guard * 10 + a[1].field
}
