pub struct P { pub x: i32, pub y: i32 } pub fn f(p: &P) -> i32 { p.x.wrapping_add(p.y) }
