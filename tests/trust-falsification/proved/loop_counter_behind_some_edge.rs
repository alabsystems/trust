#![crate_type = "lib"]
// The correct twin of three mutants (`loop_iterator_rebuilt_every_iteration`,
// `loop_path_skips_next`, `loop_add_on_none_arm`): the range is built once, every
// iteration calls `next`, and the add sits behind the `Some` arm, so it runs at most
// 10 times and `c <= 10` bounds it.
pub fn behind_some() -> u8 {
    let mut c = 0u8;
    let mut r = 0..10u32;
    loop {
        match r.next() {
            Some(_) => c += 1,
            None => break,
        }
    }
    c
}
