pub fn g(a: i32, b: i32) -> i32 {
    a.saturating_add(b)
}
pub fn f(a: i32, b: i32) -> i32 {
    g(a, b)
}
