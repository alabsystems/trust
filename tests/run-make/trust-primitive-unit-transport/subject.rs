#![allow(dead_code)]
#[inline(never)]
pub fn tick(counter: &mut i32) { *counter += 1; }

pub fn unit_call_once(start: i32, (mut value,): ((),)) -> (i32, ()) {
    let mut counter = start;
    let alias = &mut value;
    let _copied = *alias;
    value = tick(&mut counter);
    (counter, value)
}

pub fn unit_call_after_branch(start: i32, flag: bool) -> (i32, ()) {
    let mut counter = start;
    let mut value;
    if flag { value = (); } else { value = (); }
    let alias = &mut value;
    let _copied = *alias;
    value = tick(&mut counter);
    (counter, value)
}

pub fn unit_tuple_field(unit: (), answer: i32) -> ((), i32) {
    let pair = (unit, answer);
    (pair.0, pair.1)
}
