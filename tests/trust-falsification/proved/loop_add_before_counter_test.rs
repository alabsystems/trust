#![crate_type = "lib"]
// The correct twin of `mutant/loop_add_before_counter_test.rs`: with 12 elements,
// `a[c]` is in bounds. The add runs before the exit test, so it runs once more than
// the loop's 10 continuing iterations, 11 times, and `c <= 11`.
pub fn add_before_test() -> u8 {
    let a = [7u8; 12];
    let mut c = 0usize;
    let mut i = 0u32;
    loop {
        c += 1;
        if i >= 10 {
            break;
        }
        i += 1;
    }
    a[c]
}
