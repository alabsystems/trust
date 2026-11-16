#![crate_type = "lib"]
// MUTANT of `proved/loop_counter_behind_some_edge.rs`: the range is built INSIDE the
// loop, so every iteration takes `Some(0)` from a fresh `0..10`. The loop never ends
// and `c += 1` overflows at 256. The accumulator lane used to take the trip count 10
// from the range (`c <= 10`) and proved this, kernel-certified under certify.
pub fn rebuilt() -> u8 {
    let mut c = 0u8;
    loop {
        let mut r = 0..10u32;
        match r.next() {
            Some(_) => c += 1,
            None => break,
        }
    }
    c
}
