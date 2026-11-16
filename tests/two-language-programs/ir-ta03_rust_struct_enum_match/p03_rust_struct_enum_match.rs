// FEATURE rust.struct_enum_match — struct, enum with payloads, match.
// EXPECT: 29
pub struct Pt { pub x: u64, pub y: u64 }
pub enum Shape { Circle(u64), Rect(u64, u64), Empty }
#[inline(never)]
pub fn norm1(p: &Pt) -> u64 { p.x + p.y }
#[inline(never)]
pub fn area(s: &Shape) -> u64 {
    match s {
        Shape::Circle(r) => *r * *r * 3,
        Shape::Rect(w, h) => *w * *h,
        Shape::Empty => 0,
    }
}
pub fn program() -> u64 {
    norm1(&Pt { x: 3, y: 4 }) + area(&Shape::Rect(2, 5)) + area(&Shape::Circle(2)) + area(&Shape::Empty)
}

#[cfg(not(parta_lib))]
fn main() {
    println!("{}", program());
}
