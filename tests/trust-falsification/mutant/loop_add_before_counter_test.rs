#![crate_type = "lib"]
// MUTANT of `proved/loop_add_before_counter_test.rs`: the add runs BEFORE the exit
// test, so it runs once more than the loop's 10 continuing iterations and `c` ends at
// 11, one past the 11-element array. The manual-counter lane used to bound `c` by the
// test's trip count (`c <= 10`) and proved `a[c]` in bounds.
pub fn add_before_test() -> u8 {
    let a = [7u8; 11];
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
