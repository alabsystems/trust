#![allow(unused_assignments, unused_mut, unconditional_panic)]

#[derive(Clone, Copy)]
pub struct Pair {
    pub x: u32,
    pub y: u32,
}

pub fn block_field_plain() -> u32 {
    let p = Pair { x: 1, y: 2 };
    ({ p }).x = 4;
    p.x
}

pub fn block_field_compound() -> u32 {
    let p = Pair { x: 1, y: 2 };
    ({ p }).x += 3;
    p.x
}

pub fn block_array_plain() -> u32 {
    let a = [1u32, 2];
    ({ a })[0] = 4;
    a[0]
}

pub fn block_array_compound() -> u32 {
    let a = [1u32, 2];
    ({ a })[0] += 3;
    a[0]
}

pub fn if_field_plain() -> u32 {
    let p = Pair { x: 1, y: 2 };
    (if true { p } else { p }).x = 4;
    p.x
}

pub fn if_field_compound() -> u32 {
    let p = Pair { x: 1, y: 2 };
    (if false { Pair { x: 7, y: 8 } } else { p }).x += 3;
    p.x
}

pub fn if_array_plain() -> u32 {
    let a = [1u32, 2];
    (if true { a } else { a })[0] = 4;
    a[0]
}

pub fn if_array_compound() -> u32 {
    let a = [1u32, 2];
    (if false { [7, 8] } else { a })[0] += 3;
    a[0]
}

pub fn loop_field_plain() -> u32 {
    let p = Pair { x: 1, y: 2 };
    (loop { break p }).x = 4;
    p.x
}

pub fn loop_array_compound() -> u32 {
    let a = [1u32, 2];
    (loop { break a })[0] += 3;
    a[0]
}

pub fn match_field_compound() -> u32 {
    let p = Pair { x: 1, y: 2 };
    (match 1 { 0 => Pair { x: 7, y: 8 }, _ => p }).x += 3;
    p.x
}

pub fn literal_field_plain() -> u32 {
    (Pair { x: 1, y: 2 }).x = 4;
    1
}

pub fn literal_tuple_compound() -> u32 {
    (1u32, 2u32).0 += 3;
    1
}

pub fn literal_array_plain() -> u32 {
    [1u32, 2][0] = 4;
    1
}

pub fn repeat_array_compound() -> u32 {
    [1u32; 2][0] += 3;
    1
}

pub fn make_pair() -> Pair {
    Pair { x: 1, y: 2 }
}

pub fn make_array() -> [u32; 2] {
    [1, 2]
}

pub fn call_field_plain() -> u32 {
    make_pair().x = 4;
    1
}

pub fn call_array_compound() -> u32 {
    make_array()[0] += 3;
    1
}

pub const PAIR: Pair = Pair { x: 1, y: 2 };

pub fn named_const_field_plain() -> u32 {
    PAIR.x = 4;
    PAIR.x
}

pub fn inline_const_array_compound() -> u32 {
    (const { [1u32, 2] })[0] += 3;
    1
}

pub fn inline_const_tuple_compound() -> u32 {
    (const { (1u32, 2u32) }).0 += 3;
    1
}

pub fn inline_const_struct_compound() -> u32 {
    (const { Pair { x: 1, y: 2 } }).x += 3;
    1
}

pub fn inline_const_array_value() -> u32 {
    (const { [13u32, 17] })[1]
}

pub fn inline_const_tuple_value() -> u32 {
    (const { (13u32, 17u32) }).1
}

pub fn inline_const_struct_value() -> u32 {
    (const { Pair { x: 13, y: 17 } }).y
}

pub fn inline_const_nested_value() -> u32 {
    (const { ([13u32, 17], (19u32, 23u32)) }).0[1]
}

pub fn block_field_rhs_order() -> u32 {
    let mut p = Pair { x: u32::MAX, y: 2 };
    ({ p }).x += {
        p = Pair { x: 7, y: 8 };
        3
    };
    p.x
}

pub fn block_array_effect_order() -> u32 {
    let mut a = [1u32, 2];
    let mut n = 0;
    ({ n += 1; a })[{
        n *= 10;
        a = [7, 8];
        0
    }] = {
        n += 2;
        4
    };
    n * 100 + a[0]
}

pub fn if_base_effect_order() -> u32 {
    let mut n = 0;
    (if { n = n * 10 + 2; true } {
        n = n * 10 + 3;
        Pair { x: 1, y: 2 }
    } else {
        Pair { x: 7, y: 8 }
    }).x = {
        n = n * 10 + 1;
        4
    };
    n
}

pub fn loop_base_effect_order() -> u32 {
    let mut n = 0;
    (loop {
        n = n * 10 + 2;
        break Pair { x: 1, y: 2 };
    }).x += {
        n = n * 10 + 1;
        3
    };
    n
}

pub fn real_reference_compound() -> u32 {
    let mut p = Pair { x: 1, y: 2 };
    let r = &mut p;
    (*(r as &mut Pair)).x += 3;
    p.x
}

pub fn block_field_overflow() -> u32 {
    let p = Pair { x: u32::MAX, y: 2 };
    ({ p }).x += 1;
    0
}

pub fn block_array_capture_overflow() -> u32 {
    let mut a = [u32::MAX, 2];
    ({ a })[{ a = [7, 8]; 0 }] += 1;
    0
}

pub fn block_field_divide_by_zero() -> u32 {
    let p = Pair { x: 1, y: 2 };
    ({ p }).x /= 0;
    0
}

pub fn block_array_oob() -> u32 {
    let a = [1u32, 2];
    ({ a })[2] = 4;
    0
}

pub struct Dropping(pub u32);

impl Drop for Dropping {
    fn drop(&mut self) {
        assert_eq!(self.0, 4);
    }
}

pub fn dropping_block_refused() -> u32 {
    ({ Dropping(1) }).0 = 4;
    7
}

pub fn dropping_if_refused() -> u32 {
    (if true { Dropping(1) } else { Dropping(2) }).0 += 3;
    7
}

pub fn asm_refused() -> u32 {
    ({
        unsafe { core::arch::asm!(""); }
        Pair { x: 1, y: 2 }
    }).x += 3;
    1
}
