pub fn g(a: i32, b: i32) -> (i32, bool) {
    a.overflowing_add(b)
}
pub fn f(a: i32, b: i32) -> (i32, bool) {
    g(a, b)
}
