extern crate trust;

// `join_weakened_entry_sentinel` + a DROPPABLE local. The diamond makes the
// pinned `n#s?_? == n#e / 3` the only carrier; the drop adds cleanup blocks, so
// some block's entry-version map is EMPTY and the tie's MINT-SIDE clause refuses.
#[trust::requires(n < 30)]
pub fn h(mut n: u32, a: &[u8; 10], b: bool, c: bool) -> u8 {
    let s = String::new();
    n /= 3;
    let mut t: u32 = 0;
    if b { t = 1; } else { t = 2; }
    let r = if c && t > 0 { a[n as usize] } else { 0 };
    drop(s);
    r
}
