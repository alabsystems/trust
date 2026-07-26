// Option combinators over CERTIFIED-leaf closures — harvest family option-combinators2.
// Wrappers at Option<u8> and Option<i32>: map(&3), map(|1), and_then(pos), filter(!=0),
// xor, or, and, is_some_and(>0).

#[inline(never)]
fn map_and3_u8(o: Option<u8>) -> Option<u8> {
    o.map(|x| x & 3)
}

#[inline(never)]
fn map_and3_i32(o: Option<i32>) -> Option<i32> {
    o.map(|x| x & 3)
}

#[inline(never)]
fn map_or1_u8(o: Option<u8>) -> Option<u8> {
    o.map(|x| x | 1)
}

#[inline(never)]
fn map_or1_i32(o: Option<i32>) -> Option<i32> {
    o.map(|x| x | 1)
}

#[inline(never)]
fn and_then_pos_u8(o: Option<u8>) -> Option<u8> {
    o.and_then(|x| if x > 0 { Some(x) } else { None })
}

#[inline(never)]
fn and_then_pos_i32(o: Option<i32>) -> Option<i32> {
    o.and_then(|x| if x > 0 { Some(x) } else { None })
}

#[inline(never)]
fn filter_nonzero_u8(o: Option<u8>) -> Option<u8> {
    o.filter(|x| *x != 0)
}

#[inline(never)]
fn filter_nonzero_i32(o: Option<i32>) -> Option<i32> {
    o.filter(|x| *x != 0)
}

#[inline(never)]
fn xor_u8(o: Option<u8>, p: Option<u8>) -> Option<u8> {
    o.xor(p)
}

#[inline(never)]
fn xor_i32(o: Option<i32>, p: Option<i32>) -> Option<i32> {
    o.xor(p)
}

#[inline(never)]
fn or_u8(o: Option<u8>, p: Option<u8>) -> Option<u8> {
    o.or(p)
}

#[inline(never)]
fn or_i32(o: Option<i32>, p: Option<i32>) -> Option<i32> {
    o.or(p)
}

#[inline(never)]
fn and_u8(o: Option<u8>, p: Option<u8>) -> Option<u8> {
    o.and(p)
}

#[inline(never)]
fn and_i32(o: Option<i32>, p: Option<i32>) -> Option<i32> {
    o.and(p)
}

#[inline(never)]
fn is_some_and_pos_u8(o: Option<u8>) -> bool {
    o.is_some_and(|x| x > 0)
}

#[inline(never)]
fn is_some_and_pos_i32(o: Option<i32>) -> bool {
    o.is_some_and(|x| x > 0)
}

fn main() {
    let n = std::env::args().count();
    let u = n as u8;
    let i = n as i32;
    let ou: Option<u8> = if n > 1 { Some(u) } else { None };
    let pu: Option<u8> = if n > 2 { Some(u.wrapping_add(1)) } else { None };
    let oi: Option<i32> = if n > 1 { Some(i) } else { None };
    let pi: Option<i32> = if n > 2 { Some(i + 1) } else { None };

    let mut acc: u32 = 0;
    acc = acc.wrapping_add(map_and3_u8(ou).unwrap_or(0) as u32);
    acc = acc.wrapping_add(map_and3_i32(oi).unwrap_or(0) as u32);
    acc = acc.wrapping_add(map_or1_u8(ou).unwrap_or(0) as u32);
    acc = acc.wrapping_add(map_or1_i32(oi).unwrap_or(0) as u32);
    acc = acc.wrapping_add(and_then_pos_u8(ou).unwrap_or(0) as u32);
    acc = acc.wrapping_add(and_then_pos_i32(oi).unwrap_or(0) as u32);
    acc = acc.wrapping_add(filter_nonzero_u8(ou).unwrap_or(0) as u32);
    acc = acc.wrapping_add(filter_nonzero_i32(oi).unwrap_or(0) as u32);
    acc = acc.wrapping_add(xor_u8(ou, pu).unwrap_or(0) as u32);
    acc = acc.wrapping_add(xor_i32(oi, pi).unwrap_or(0) as u32);
    acc = acc.wrapping_add(or_u8(ou, pu).unwrap_or(0) as u32);
    acc = acc.wrapping_add(or_i32(oi, pi).unwrap_or(0) as u32);
    acc = acc.wrapping_add(and_u8(ou, pu).unwrap_or(0) as u32);
    acc = acc.wrapping_add(and_i32(oi, pi).unwrap_or(0) as u32);
    acc = acc.wrapping_add(is_some_and_pos_u8(ou) as u32);
    acc = acc.wrapping_add(is_some_and_pos_i32(oi) as u32);
    std::process::exit((acc & 0x7f) as i32);
}
