pub fn f(n: u32) -> u32 {
    let mut i = 0u32;
    while i < n.min(10) {
        i += 1;
    }
    i
}
