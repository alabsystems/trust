#![crate_type = "lib"]
// MUTANT of `proved/loop_counter_behind_some_edge.rs`: the add is on the `None` arm and
// the loop never breaks, so once `0..10` is exhausted every iteration adds, and `c`
// overflows. The accumulator lane used to bound the add by the range's trip count
// (`c <= 10`) and proved this.
pub fn add_on_none() -> u8 {
    let mut c = 0u8;
    let mut r = 0..10u32;
    loop {
        match r.next() {
            Some(_) => {}
            None => c += 1,
        }
    }
}
