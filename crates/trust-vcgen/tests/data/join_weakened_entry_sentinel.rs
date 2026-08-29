extern crate trust;

// Diamond join between the in-place update and the use, to make the
// semantic-guard BFS weaken (and drop the establish-versioned sibling def),
// leaving the pinned path def with its free `n#e` as the ONLY carrier.
#[trust::requires(n < 30)]
pub fn h(mut n: u32, a: &[u8; 10], b: bool, c: bool) -> u8 {
    n /= 3;
    let mut t: u32 = 0;
    if b {
        t = 1;
    } else {
        t = 2;
    }
    if c && t > 0 { a[n as usize] } else { 0 }
}
