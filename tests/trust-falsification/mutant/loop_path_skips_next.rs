#![crate_type = "lib"]
// MUTANT of `proved/loop_counter_behind_some_edge.rs`: when `flag` is set, the loop
// cycles through `c += 1; continue` and never calls `next`, so `c` overflows at 256.
// The accumulator lane used to bound every self-add by the range's trip count
// (`c <= 10`) because the loop HAS a `next` call, and proved this.
pub fn skips_next(flag: bool) -> u8 {
    let mut c = 0u8;
    let mut r = 0..10u32;
    loop {
        if flag {
            c += 1;
            continue;
        }
        match r.next() {
            Some(_) => {}
            None => break,
        }
    }
    c
}
