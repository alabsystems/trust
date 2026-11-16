pub fn f(g: impl Fn(u32) -> u32, x: u32) -> u32 {
    g(x)
}
