// The edited program of trust-obligation-ids: a.rs with twenty comment lines
// and an unrelated function inserted at the top, `add3` and `div_index`
// swapped, and three edits inside `f`: a division of the SAME kind inserted
// above `a / b`, an unrelated line inserted below it, and the two
// multiplications swapped. A key that ranked rows by kind and position would
// move under each of those; a content-addressed key moves under none.
//
// unrelated comment 1
// unrelated comment 2
// unrelated comment 3
// unrelated comment 4
// unrelated comment 5
// unrelated comment 6
// unrelated comment 7
// unrelated comment 8
// unrelated comment 9
// unrelated comment 10
// unrelated comment 11
// unrelated comment 12
// unrelated comment 13
// unrelated comment 14
// unrelated comment 15
// unrelated comment 16

pub fn unrelated(x: u64) -> u64 {
    x / 7
}

pub fn add3(a: u64, b: u64, c: u64) -> u64 {
    a + b + c
}

pub fn div_index(xs: &[u64], i: usize, d: u64) -> u64 {
    xs[i] / d
}

pub fn f(a: u64, b: u64) -> u64 {
    let _w = b / a;
    let x = a / b;
    let _unrelated = 0u64;
    let z = a * 5;
    let y = x * 3;
    y + a + z
}

macro_rules! halve {
    ($x:expr, $d:expr) => {
        $x / $d
    };
}

pub fn macro_div(a: u64, d: u64) -> u64 {
    halve!(a, d)
}
