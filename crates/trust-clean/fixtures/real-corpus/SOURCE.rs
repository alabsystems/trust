pub struct Point { pub x: u32, pub y: u32 }
pub struct Wrapper<T> { pub value: T, pub count: u32 }
pub fn pt_sum(p: Point) -> u32 { p.x + p.y }
pub fn pt_dx(p: Point, q: Point) -> u32 { p.x - q.x }
pub fn wrap_count(w: Wrapper<u64>) -> u32 { w.count + 1 }
pub fn uadd(a: u32, b: u32) -> u32 { a + b }
pub fn usub(a: u32, b: u32) -> u32 { a - b }
pub fn umul(a: u32, b: u32) -> u32 { a * b }
pub fn sadd(a: i32, b: i32) -> i32 { a + b }
pub fn ssub(a: i32, b: i32) -> i32 { a - b }
pub fn udiv(a: u32, b: u32) -> u32 { a / b }
pub fn sdiv(a: i32, b: i32) -> i32 { a / b }
pub fn index(s: &[u32], i: usize) -> u32 { s[i] }
pub fn vec_len_idx(v: &Vec<u32>, i: usize) -> u32 { v[i] }
pub fn negate(x: i32) -> i32 { -x }
pub fn shift_l(x: u32, n: u32) -> u32 { x << n }
pub fn fbits(f: f32) -> f32 { f }
pub fn id_u32(x: u32) -> u32 { x }
pub fn bump_i32(x: i32) -> i32 { x + 1 }
pub fn box_inner(b: Box<u32>) -> u32 { *b }
