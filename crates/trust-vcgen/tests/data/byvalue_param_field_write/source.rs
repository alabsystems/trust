pub struct S {
    pub a: u8,
    pub b: u8,
}

#[inline(never)]
pub fn id(x: u8) -> u8 {
    x
}

pub fn z(mut s: S) -> u8
    ensures s.a == 0
{
    s.a = 0;
    1
}

pub fn two(mut s: S) -> u8
    ensures result == s.a
{
    s.a = s.b;
    s.a
}

pub fn tup(mut t: (u8, u8)) -> u8
    ensures result == t.0
{
    t.0 = t.1;
    t.0
}

pub fn callw(mut s: S) -> u8
    ensures s.a == 4
{
    s.a = id(4);
    0
}

pub fn viaref(mut s: S) -> u8
    ensures result == s.a
{
    let p = &mut s.a;
    *p = 9;
    s.a
}

pub fn neg(mut s: S) -> bool
    ensures result == !(s.a == 0)
{
    s.a = 0;
    s.a != 0
}

pub fn k(mut s: S) -> u8
    ensures result == s.a
{
    let old = s.a;
    s.a = 0;
    old
}

pub fn ok(s: S) -> u8
    ensures result == s.a
{
    s.a
}

pub fn unrel(mut s: S) -> u8
    ensures result == s.a
{
    s.b = 0;
    s.a
}

pub fn mref(s: &mut S) -> u8
    ensures s.a == 0
{
    s.a = 0;
    1
}
