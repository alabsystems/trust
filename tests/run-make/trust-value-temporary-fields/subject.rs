#![allow(unused_assignments, unused_mut, unconditional_panic)]

#[derive(Clone, Copy)]
pub struct Pair {
    pub x: u32,
    pub y: u32,
}

#[derive(Clone, Copy)]
pub struct Outer {
    pub inner: Pair,
}

#[derive(Clone, Copy)]
pub struct Numbers {
    pub arr: [u32; 2],
}

pub fn struct_compound() -> u32 {
    let mut p = Pair { x: 1, y: 2 };
    (p as Pair).x += 3;
    p.x
}

pub fn tuple_compound() -> u32 {
    let mut p = (1u32, 2u32);
    (p as (u32, u32)).0 += 3;
    p.0
}

pub fn struct_plain() -> u32 {
    let mut p = Pair { x: 1, y: 2 };
    (p as Pair).x = 4;
    p.x
}

pub fn tuple_plain() -> u32 {
    let mut p = (1u32, 2u32);
    (p as (u32, u32)).0 = 4;
    p.0
}

pub fn promoted_struct_compound() -> u32 {
    let mut p = Pair { x: 1, y: 2 };
    let _pin = &mut p;
    (p as Pair).x += 3;
    p.x
}

pub fn promoted_struct_plain() -> u32 {
    let mut p = Pair { x: 1, y: 2 };
    let _pin = &mut p;
    (p as Pair).x = 4;
    p.x
}

pub fn promoted_tuple_compound() -> u32 {
    let mut p = (1u32, 2u32);
    let _pin = &mut p;
    (p as (u32, u32)).0 += 3;
    p.0
}

pub fn promoted_tuple_plain() -> u32 {
    let mut p = (1u32, 2u32);
    let _pin = &mut p;
    (p as (u32, u32)).0 = 4;
    p.0
}

pub fn nested_compound() -> u32 {
    let mut p = Outer { inner: Pair { x: 1, y: 2 } };
    (p as Outer).inner.x += 3;
    p.inner.x
}

pub fn nested_plain() -> u32 {
    let mut p = Outer { inner: Pair { x: 1, y: 2 } };
    (p as Outer).inner.x = 4;
    p.inner.x
}

pub fn rhs_replaces_struct() -> u32 {
    let mut p = Pair { x: u32::MAX, y: 2 };
    (p as Pair).x += {
        p = Pair { x: 7, y: 8 };
        3
    };
    p.x
}

pub fn rhs_replaces_tuple() -> u32 {
    let mut p = (u32::MAX, 2u32);
    (p as (u32, u32)).0 += {
        p = (7, 8);
        3
    };
    p.0
}

pub fn side_effecting_base_compound() -> u32 {
    let mut n = 0;
    let p = Pair { x: 1, y: 2 };
    ({
        n += 1;
        p
    } as Pair)
        .x += {
        n += 2;
        3
    };
    n * 10 + p.x
}

pub fn side_effecting_base_plain() -> u32 {
    let mut n = 0;
    let p = Pair { x: 1, y: 2 };
    ({
        n += 1;
        p
    } as Pair)
        .x = {
        n += 2;
        4
    };
    n * 10 + p.x
}

pub fn guard_compound() -> u32 {
    let mut p = Pair { x: 1, y: 2 };
    match 0 {
        0 if {
            (p as Pair).x += 3;
            false
        } =>
        {
            99
        }
        _ => p.x,
    }
}

pub fn real_struct_place() -> u32 {
    let mut p = Pair { x: 1, y: 2 };
    p.x += 3;
    p.x
}

pub fn real_tuple_place() -> u32 {
    let mut p = (1u32, 2u32);
    p.0 += 3;
    p.0
}

pub fn deref_of_cast_reference() -> u32 {
    let mut p = Pair { x: 1, y: 2 };
    let r = &mut p;
    (*(r as &mut Pair)).x += 3;
    p.x
}

pub fn overflow_temporary() -> u32 {
    let p = Pair { x: u32::MAX, y: 2 };
    (p as Pair).x += 1;
    0
}

pub fn divide_by_zero_temporary() -> u32 {
    let p = Pair { x: 1, y: 2 };
    (p as Pair).x /= 0;
    0
}

pub fn indexed_field_plain() -> u32 {
    let b = Numbers { arr: [1, 2] };
    (b as Numbers).arr[0] = 4;
    b.arr[0]
}

pub fn indexed_field_compound() -> u32 {
    let b = Numbers { arr: [1, 2] };
    (b as Numbers).arr[0] += 3;
    b.arr[0]
}

pub fn copied_array_field() -> u32 {
    let b = Numbers { arr: [1, 2] };
    (b.arr as [u32; 2])[0] = 4;
    b.arr[0]
}

pub fn indexed_field_effect_order() -> u32 {
    let mut b = Numbers { arr: [1, 2] };
    let mut n = 0;
    ({
        n += 1;
        b
    } as Numbers)
        .arr[{
        n *= 10;
        b.arr = [7, 8];
        0
    }] = {
        n += 2;
        4
    };
    n * 100 + b.arr[0]
}

pub fn indexed_field_oob() -> u32 {
    let b = Numbers { arr: [1, 2] };
    (b as Numbers).arr[2] = 4;
    0
}

pub fn copied_deref_array_plain() -> u32 {
    let mut a = [1u32, 2];
    let r = &mut a;
    (*r as [u32; 2])[0] = 4;
    a[0]
}

pub fn copied_deref_array_compound() -> u32 {
    let mut a = [1u32, 2];
    let r = &mut a;
    (*r as [u32; 2])[0] += 3;
    a[0]
}

pub fn deref_of_cast_array_reference_plain() -> u32 {
    let mut a = [1u32, 2];
    let r = &mut a;
    (*(r as &mut [u32; 2]))[0] = 4;
    a[0]
}

pub fn deref_of_cast_array_reference_compound() -> u32 {
    let mut a = [1u32, 2];
    let r = &mut a;
    (*(r as &mut [u32; 2]))[0] += 3;
    a[0]
}

pub struct Dropping(pub u32);

impl Drop for Dropping {
    fn drop(&mut self) {
        assert_eq!(self.0, 4);
    }
}

pub fn dropping_plain_refused() -> u32 {
    (Dropping(1) as Dropping).0 = 4;
    7
}

pub fn dropping_compound_refused() -> u32 {
    (Dropping(1) as Dropping).0 += 3;
    7
}

pub fn asm_refused() -> u32 {
    let p = Pair { x: 1, y: 2 };
    ({
        unsafe {
            core::arch::asm!("");
        }
        p
    } as Pair)
        .x += 3;
    p.x
}
