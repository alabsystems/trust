//! Actual source bodies for owned primitive homes; the independent Rust oracle
//! and complete-original-module observer use these same maintained bytes.
#![allow(dead_code)]

#[inline(never)]
pub fn store_bool(dst: &mut bool, value: bool) { *dst = value; }

pub fn delayed_bool(a: bool, b: bool, replacement: bool, flag: bool) -> (bool, bool) {
    let mut local;
    if flag { local = a; } else { local = b; }
    let before = local;
    let alias = &mut local;
    store_bool(alias, replacement);
    (before, local)
}

pub fn tuple_bool(a: bool, b: bool, replacement: bool) -> (bool, bool, bool) {
    let original = (a, b);
    let (mut local, sibling) = original;
    let alias = &mut local;
    store_bool(alias, replacement);
    (local, sibling, original.0)
}

pub fn nested_bool(a: bool, b: bool, c: bool, replacement: bool) -> (bool, bool, bool, bool, bool) {
    let original = (a, (b, c));
    let (mut x, (mut y, z)) = original;
    store_bool(&mut x, replacement);
    let before_y = y;
    store_bool(&mut y, x);
    (x, before_y, y, z, original.0)
}

#[inline(never)]
// Char reference-parameter writes stay outside the existing registration lane.
// Exercise actual local alias writes with an ordinary by-value call instead.
pub fn identity_char(value: char) -> char { value }

pub fn delayed_char(a: char, b: char, replacement: char, flag: bool) -> (char, char) {
    let mut local;
    if flag { local = a; } else { local = b; }
    let before = local;
    let alias = &mut local;
    *alias = identity_char(replacement);
    (before, local)
}

pub fn tuple_char(a: char, b: char, replacement: char) -> (char, char, char) {
    let original = (a, b);
    let (mut local, sibling) = original;
    let alias = &mut local;
    *alias = identity_char(replacement);
    (local, sibling, original.0)
}

pub fn nested_char(a: char, b: char, c: char, replacement: char) -> (char, char, char, char, char) {
    let original = (a, (b, c));
    let (mut x, (mut y, z)) = original;
    let alias_x = &mut x;
    *alias_x = identity_char(replacement);
    let before_y = y;
    let alias_y = &mut y;
    *alias_y = identity_char(x);
    (x, before_y, y, z, original.0)
}

#[inline(never)]
pub fn store_i8(dst: &mut i8, value: i8) { *dst = value; }

pub fn delayed_i8(a: i8, b: i8, replacement: i8, flag: bool) -> (i8, i8) {
    let mut local;
    if flag { local = a; } else { local = b; }
    let before = local;
    let alias = &mut local;
    store_i8(alias, replacement);
    (before, local)
}

pub fn tuple_i8(a: i8, b: i8, replacement: i8) -> (i8, i8, i8) {
    let original = (a, b);
    let (mut local, sibling) = original;
    let alias = &mut local;
    store_i8(alias, replacement);
    (local, sibling, original.0)
}

pub fn nested_i8(a: i8, b: i8, c: i8, replacement: i8) -> (i8, i8, i8, i8, i8) {
    let original = (a, (b, c));
    let (mut x, (mut y, z)) = original;
    store_i8(&mut x, replacement);
    let before_y = y;
    store_i8(&mut y, x);
    (x, before_y, y, z, original.0)
}

#[inline(never)]
pub fn store_i16(dst: &mut i16, value: i16) { *dst = value; }

pub fn delayed_i16(a: i16, b: i16, replacement: i16, flag: bool) -> (i16, i16) {
    let mut local;
    if flag { local = a; } else { local = b; }
    let before = local;
    let alias = &mut local;
    store_i16(alias, replacement);
    (before, local)
}

pub fn tuple_i16(a: i16, b: i16, replacement: i16) -> (i16, i16, i16) {
    let original = (a, b);
    let (mut local, sibling) = original;
    let alias = &mut local;
    store_i16(alias, replacement);
    (local, sibling, original.0)
}

pub fn nested_i16(a: i16, b: i16, c: i16, replacement: i16) -> (i16, i16, i16, i16, i16) {
    let original = (a, (b, c));
    let (mut x, (mut y, z)) = original;
    store_i16(&mut x, replacement);
    let before_y = y;
    store_i16(&mut y, x);
    (x, before_y, y, z, original.0)
}

#[inline(never)]
pub fn store_i32(dst: &mut i32, value: i32) { *dst = value; }

pub fn delayed_i32(a: i32, b: i32, replacement: i32, flag: bool) -> (i32, i32) {
    let mut local;
    if flag { local = a; } else { local = b; }
    let before = local;
    let alias = &mut local;
    store_i32(alias, replacement);
    (before, local)
}

pub fn tuple_i32(a: i32, b: i32, replacement: i32) -> (i32, i32, i32) {
    let original = (a, b);
    let (mut local, sibling) = original;
    let alias = &mut local;
    store_i32(alias, replacement);
    (local, sibling, original.0)
}

pub fn nested_i32(a: i32, b: i32, c: i32, replacement: i32) -> (i32, i32, i32, i32, i32) {
    let original = (a, (b, c));
    let (mut x, (mut y, z)) = original;
    store_i32(&mut x, replacement);
    let before_y = y;
    store_i32(&mut y, x);
    (x, before_y, y, z, original.0)
}

#[inline(never)]
pub fn store_i64(dst: &mut i64, value: i64) { *dst = value; }

pub fn delayed_i64(a: i64, b: i64, replacement: i64, flag: bool) -> (i64, i64) {
    let mut local;
    if flag { local = a; } else { local = b; }
    let before = local;
    let alias = &mut local;
    store_i64(alias, replacement);
    (before, local)
}

pub fn tuple_i64(a: i64, b: i64, replacement: i64) -> (i64, i64, i64) {
    let original = (a, b);
    let (mut local, sibling) = original;
    let alias = &mut local;
    store_i64(alias, replacement);
    (local, sibling, original.0)
}

pub fn nested_i64(a: i64, b: i64, c: i64, replacement: i64) -> (i64, i64, i64, i64, i64) {
    let original = (a, (b, c));
    let (mut x, (mut y, z)) = original;
    store_i64(&mut x, replacement);
    let before_y = y;
    store_i64(&mut y, x);
    (x, before_y, y, z, original.0)
}

#[inline(never)]
pub fn store_i128(dst: &mut i128, value: i128) { *dst = value; }

pub fn delayed_i128(a: i128, b: i128, replacement: i128, flag: bool) -> (i128, i128) {
    let mut local;
    if flag { local = a; } else { local = b; }
    let before = local;
    let alias = &mut local;
    store_i128(alias, replacement);
    (before, local)
}

pub fn tuple_i128(a: i128, b: i128, replacement: i128) -> (i128, i128, i128) {
    let original = (a, b);
    let (mut local, sibling) = original;
    let alias = &mut local;
    store_i128(alias, replacement);
    (local, sibling, original.0)
}

pub fn nested_i128(a: i128, b: i128, c: i128, replacement: i128) -> (i128, i128, i128, i128, i128) {
    let original = (a, (b, c));
    let (mut x, (mut y, z)) = original;
    store_i128(&mut x, replacement);
    let before_y = y;
    store_i128(&mut y, x);
    (x, before_y, y, z, original.0)
}

#[inline(never)]
pub fn store_isize(dst: &mut isize, value: isize) { *dst = value; }

pub fn delayed_isize(a: isize, b: isize, replacement: isize, flag: bool) -> (isize, isize) {
    let mut local;
    if flag { local = a; } else { local = b; }
    let before = local;
    let alias = &mut local;
    store_isize(alias, replacement);
    (before, local)
}

pub fn tuple_isize(a: isize, b: isize, replacement: isize) -> (isize, isize, isize) {
    let original = (a, b);
    let (mut local, sibling) = original;
    let alias = &mut local;
    store_isize(alias, replacement);
    (local, sibling, original.0)
}

pub fn nested_isize(a: isize, b: isize, c: isize, replacement: isize) -> (isize, isize, isize, isize, isize) {
    let original = (a, (b, c));
    let (mut x, (mut y, z)) = original;
    store_isize(&mut x, replacement);
    let before_y = y;
    store_isize(&mut y, x);
    (x, before_y, y, z, original.0)
}

#[inline(never)]
pub fn store_u8(dst: &mut u8, value: u8) { *dst = value; }

pub fn delayed_u8(a: u8, b: u8, replacement: u8, flag: bool) -> (u8, u8) {
    let mut local;
    if flag { local = a; } else { local = b; }
    let before = local;
    let alias = &mut local;
    store_u8(alias, replacement);
    (before, local)
}

pub fn tuple_u8(a: u8, b: u8, replacement: u8) -> (u8, u8, u8) {
    let original = (a, b);
    let (mut local, sibling) = original;
    let alias = &mut local;
    store_u8(alias, replacement);
    (local, sibling, original.0)
}

pub fn nested_u8(a: u8, b: u8, c: u8, replacement: u8) -> (u8, u8, u8, u8, u8) {
    let original = (a, (b, c));
    let (mut x, (mut y, z)) = original;
    store_u8(&mut x, replacement);
    let before_y = y;
    store_u8(&mut y, x);
    (x, before_y, y, z, original.0)
}

#[inline(never)]
pub fn store_u16(dst: &mut u16, value: u16) { *dst = value; }

pub fn delayed_u16(a: u16, b: u16, replacement: u16, flag: bool) -> (u16, u16) {
    let mut local;
    if flag { local = a; } else { local = b; }
    let before = local;
    let alias = &mut local;
    store_u16(alias, replacement);
    (before, local)
}

pub fn tuple_u16(a: u16, b: u16, replacement: u16) -> (u16, u16, u16) {
    let original = (a, b);
    let (mut local, sibling) = original;
    let alias = &mut local;
    store_u16(alias, replacement);
    (local, sibling, original.0)
}

pub fn nested_u16(a: u16, b: u16, c: u16, replacement: u16) -> (u16, u16, u16, u16, u16) {
    let original = (a, (b, c));
    let (mut x, (mut y, z)) = original;
    store_u16(&mut x, replacement);
    let before_y = y;
    store_u16(&mut y, x);
    (x, before_y, y, z, original.0)
}

#[inline(never)]
pub fn store_u32(dst: &mut u32, value: u32) { *dst = value; }

pub fn delayed_u32(a: u32, b: u32, replacement: u32, flag: bool) -> (u32, u32) {
    let mut local;
    if flag { local = a; } else { local = b; }
    let before = local;
    let alias = &mut local;
    store_u32(alias, replacement);
    (before, local)
}

pub fn tuple_u32(a: u32, b: u32, replacement: u32) -> (u32, u32, u32) {
    let original = (a, b);
    let (mut local, sibling) = original;
    let alias = &mut local;
    store_u32(alias, replacement);
    (local, sibling, original.0)
}

pub fn nested_u32(a: u32, b: u32, c: u32, replacement: u32) -> (u32, u32, u32, u32, u32) {
    let original = (a, (b, c));
    let (mut x, (mut y, z)) = original;
    store_u32(&mut x, replacement);
    let before_y = y;
    store_u32(&mut y, x);
    (x, before_y, y, z, original.0)
}

#[inline(never)]
pub fn store_u64(dst: &mut u64, value: u64) { *dst = value; }

pub fn delayed_u64(a: u64, b: u64, replacement: u64, flag: bool) -> (u64, u64) {
    let mut local;
    if flag { local = a; } else { local = b; }
    let before = local;
    let alias = &mut local;
    store_u64(alias, replacement);
    (before, local)
}

pub fn tuple_u64(a: u64, b: u64, replacement: u64) -> (u64, u64, u64) {
    let original = (a, b);
    let (mut local, sibling) = original;
    let alias = &mut local;
    store_u64(alias, replacement);
    (local, sibling, original.0)
}

pub fn nested_u64(a: u64, b: u64, c: u64, replacement: u64) -> (u64, u64, u64, u64, u64) {
    let original = (a, (b, c));
    let (mut x, (mut y, z)) = original;
    store_u64(&mut x, replacement);
    let before_y = y;
    store_u64(&mut y, x);
    (x, before_y, y, z, original.0)
}

#[inline(never)]
pub fn store_u128(dst: &mut u128, value: u128) { *dst = value; }

pub fn delayed_u128(a: u128, b: u128, replacement: u128, flag: bool) -> (u128, u128) {
    let mut local;
    if flag { local = a; } else { local = b; }
    let before = local;
    let alias = &mut local;
    store_u128(alias, replacement);
    (before, local)
}

pub fn tuple_u128(a: u128, b: u128, replacement: u128) -> (u128, u128, u128) {
    let original = (a, b);
    let (mut local, sibling) = original;
    let alias = &mut local;
    store_u128(alias, replacement);
    (local, sibling, original.0)
}

pub fn nested_u128(a: u128, b: u128, c: u128, replacement: u128) -> (u128, u128, u128, u128, u128) {
    let original = (a, (b, c));
    let (mut x, (mut y, z)) = original;
    store_u128(&mut x, replacement);
    let before_y = y;
    store_u128(&mut y, x);
    (x, before_y, y, z, original.0)
}

#[inline(never)]
pub fn store_usize(dst: &mut usize, value: usize) { *dst = value; }

pub fn delayed_usize(a: usize, b: usize, replacement: usize, flag: bool) -> (usize, usize) {
    let mut local;
    if flag { local = a; } else { local = b; }
    let before = local;
    let alias = &mut local;
    store_usize(alias, replacement);
    (before, local)
}

pub fn tuple_usize(a: usize, b: usize, replacement: usize) -> (usize, usize, usize) {
    let original = (a, b);
    let (mut local, sibling) = original;
    let alias = &mut local;
    store_usize(alias, replacement);
    (local, sibling, original.0)
}

pub fn nested_usize(a: usize, b: usize, c: usize, replacement: usize) -> (usize, usize, usize, usize, usize) {
    let original = (a, (b, c));
    let (mut x, (mut y, z)) = original;
    store_usize(&mut x, replacement);
    let before_y = y;
    store_usize(&mut y, x);
    (x, before_y, y, z, original.0)
}

#[inline(never)]
pub fn store_f32(dst: &mut f32, value: f32) { *dst = value; }

pub fn delayed_f32(a: f32, b: f32, replacement: f32, flag: bool) -> (f32, f32) {
    let mut local;
    if flag { local = a; } else { local = b; }
    let before = local;
    let alias = &mut local;
    store_f32(alias, replacement);
    (before, local)
}

pub fn tuple_f32(a: f32, b: f32, replacement: f32) -> (f32, f32, f32) {
    let original = (a, b);
    let (mut local, sibling) = original;
    let alias = &mut local;
    store_f32(alias, replacement);
    (local, sibling, original.0)
}

pub fn nested_f32(a: f32, b: f32, c: f32, replacement: f32) -> (f32, f32, f32, f32, f32) {
    let original = (a, (b, c));
    let (mut x, (mut y, z)) = original;
    store_f32(&mut x, replacement);
    let before_y = y;
    store_f32(&mut y, x);
    (x, before_y, y, z, original.0)
}

#[inline(never)]
pub fn store_f64(dst: &mut f64, value: f64) { *dst = value; }

pub fn delayed_f64(a: f64, b: f64, replacement: f64, flag: bool) -> (f64, f64) {
    let mut local;
    if flag { local = a; } else { local = b; }
    let before = local;
    let alias = &mut local;
    store_f64(alias, replacement);
    (before, local)
}

pub fn tuple_f64(a: f64, b: f64, replacement: f64) -> (f64, f64, f64) {
    let original = (a, b);
    let (mut local, sibling) = original;
    let alias = &mut local;
    store_f64(alias, replacement);
    (local, sibling, original.0)
}

pub fn nested_f64(a: f64, b: f64, c: f64, replacement: f64) -> (f64, f64, f64, f64, f64) {
    let original = (a, (b, c));
    let (mut x, (mut y, z)) = original;
    store_f64(&mut x, replacement);
    let before_y = y;
    store_f64(&mut y, x);
    (x, before_y, y, z, original.0)
}

#[inline(never)]
// Unit has zero payload; indirect Unit writes and Unit ref-param registration
// keep their existing refusals. Read the real local home, then assign directly.
pub fn identity_unit(value: ()) -> () { value }

pub fn delayed_unit(a: (), b: (), replacement: (), flag: bool) -> ((), ()) {
    let mut local;
    if flag { local = a; } else { local = b; }
    let before = local;
    let alias = &mut local;
    let _copied = *alias;
    local = identity_unit(replacement);
    (before, local)
}

pub fn tuple_unit(a: (), b: (), replacement: ()) -> ((), (), ()) {
    let original = (a, b);
    let (mut local, sibling) = original;
    let alias = &mut local;
    let _copied = *alias;
    local = identity_unit(replacement);
    (local, sibling, original.0)
}

pub fn nested_unit(a: (), b: (), c: (), replacement: ()) -> ((), (), (), (), ()) {
    let original = (a, (b, c));
    let (mut x, (mut y, z)) = original;
    let alias_x = &mut x;
    let _copied_x = *alias_x;
    x = identity_unit(replacement);
    let before_y = y;
    let alias_y = &mut y;
    let _copied_y = *alias_y;
    y = identity_unit(x);
    (x, before_y, y, z, original.0)
}

struct Pair { left: i32, right: i32 }

pub fn struct_i32(a: i32, b: i32, replacement: i32) -> (i32, i32, i32) {
    let original = Pair { left: a, right: b };
    let Pair { left: mut local, right: sibling } = original;
    store_i32(&mut local, replacement);
    (local, sibling, original.left)
}

pub fn array_i32(a: i32, b: i32, replacement: i32) -> (i32, i32, i32) {
    let original = [a, b];
    let [mut local, sibling] = original;
    store_i32(&mut local, replacement);
    (local, sibling, original[0])
}

pub fn parameter_bool((mut x, mut y): (bool, bool), replacement: bool) -> (bool, bool, bool) {
    store_bool(&mut x, replacement);
    let before_y = y;
    store_bool(&mut y, x);
    (x, before_y, y)
}

pub fn parameter_char((mut x, mut y): (char, char), replacement: char) -> (char, char, char) {
    let alias_x = &mut x;
    *alias_x = identity_char(replacement);
    let before_y = y;
    let alias_y = &mut y;
    *alias_y = identity_char(x);
    (x, before_y, y)
}

pub fn parameter_i8((mut x, mut y): (i8, i8), replacement: i8) -> (i8, i8, i8) {
    store_i8(&mut x, replacement);
    let before_y = y;
    store_i8(&mut y, x);
    (x, before_y, y)
}

pub fn parameter_i16((mut x, mut y): (i16, i16), replacement: i16) -> (i16, i16, i16) {
    store_i16(&mut x, replacement);
    let before_y = y;
    store_i16(&mut y, x);
    (x, before_y, y)
}

pub fn parameter_i32((mut x, mut y): (i32, i32), replacement: i32) -> (i32, i32, i32) {
    store_i32(&mut x, replacement);
    let before_y = y;
    store_i32(&mut y, x);
    (x, before_y, y)
}

pub fn parameter_i64((mut x, mut y): (i64, i64), replacement: i64) -> (i64, i64, i64) {
    store_i64(&mut x, replacement);
    let before_y = y;
    store_i64(&mut y, x);
    (x, before_y, y)
}

pub fn parameter_i128((mut x, mut y): (i128, i128), replacement: i128) -> (i128, i128, i128) {
    store_i128(&mut x, replacement);
    let before_y = y;
    store_i128(&mut y, x);
    (x, before_y, y)
}

pub fn parameter_isize((mut x, mut y): (isize, isize), replacement: isize) -> (isize, isize, isize) {
    store_isize(&mut x, replacement);
    let before_y = y;
    store_isize(&mut y, x);
    (x, before_y, y)
}

pub fn parameter_u8((mut x, mut y): (u8, u8), replacement: u8) -> (u8, u8, u8) {
    store_u8(&mut x, replacement);
    let before_y = y;
    store_u8(&mut y, x);
    (x, before_y, y)
}

pub fn parameter_u16((mut x, mut y): (u16, u16), replacement: u16) -> (u16, u16, u16) {
    store_u16(&mut x, replacement);
    let before_y = y;
    store_u16(&mut y, x);
    (x, before_y, y)
}

pub fn parameter_u32((mut x, mut y): (u32, u32), replacement: u32) -> (u32, u32, u32) {
    store_u32(&mut x, replacement);
    let before_y = y;
    store_u32(&mut y, x);
    (x, before_y, y)
}

pub fn parameter_u64((mut x, mut y): (u64, u64), replacement: u64) -> (u64, u64, u64) {
    store_u64(&mut x, replacement);
    let before_y = y;
    store_u64(&mut y, x);
    (x, before_y, y)
}

pub fn parameter_u128((mut x, mut y): (u128, u128), replacement: u128) -> (u128, u128, u128) {
    store_u128(&mut x, replacement);
    let before_y = y;
    store_u128(&mut y, x);
    (x, before_y, y)
}

pub fn parameter_usize((mut x, mut y): (usize, usize), replacement: usize) -> (usize, usize, usize) {
    store_usize(&mut x, replacement);
    let before_y = y;
    store_usize(&mut y, x);
    (x, before_y, y)
}

pub fn parameter_f32((mut x, mut y): (f32, f32), replacement: f32) -> (f32, f32, f32) {
    store_f32(&mut x, replacement);
    let before_y = y;
    store_f32(&mut y, x);
    (x, before_y, y)
}

pub fn parameter_f64((mut x, mut y): (f64, f64), replacement: f64) -> (f64, f64, f64) {
    store_f64(&mut x, replacement);
    let before_y = y;
    store_f64(&mut y, x);
    (x, before_y, y)
}

pub fn parameter_unit((mut x, mut y): ((), ()), replacement: ()) -> ((), (), ()) {
    let alias_x = &mut x;
    let _copied_x = *alias_x;
    x = identity_unit(replacement);
    let before_y = y;
    let alias_y = &mut y;
    let _copied_y = *alias_y;
    y = identity_unit(x);
    (x, before_y, y)
}
