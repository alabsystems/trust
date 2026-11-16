//! Field pointers into promoted struct locals: `&mut s.f` / `&s.f` written or read through,
//! beside direct field writes and reads. `M`'s fields are declared in an order rustc reorders
//! (`wide @ 0, half @ 4, tag @ 6`), so a declaration-order offset is a different field.

pub struct W {
    pub a: i32,
    pub b: i32,
}

pub struct M {
    pub tag: u8,
    pub wide: u32,
    pub half: u16,
}

#[unsafe(no_mangle)]
pub extern "C" fn fill_through_ref(x: i32, y: i32) -> i32 {
    let mut w = W { a: 0, b: 0 };
    let r = &mut w.b;
    *r = y;
    w.a = x;
    w.a - w.b
}

#[unsafe(no_mangle)]
pub extern "C" fn read_through_ref(x: i32, y: i32) -> i32 {
    let w = W { a: x, b: y };
    let r = &w.a;
    *r - w.b
}

#[unsafe(no_mangle)]
pub extern "C" fn mixed_through_ref(t: u32, v: u32, h: u32) -> u32 {
    let mut m = M { tag: 0, wide: 0, half: 0 };
    let p = &mut m.half;
    *p = h as u16;
    let q = &mut m.tag;
    *q = t as u8;
    m.wide = v;
    m.wide - (m.half as u32) - (m.tag as u32) - (m.tag as u32)
}
