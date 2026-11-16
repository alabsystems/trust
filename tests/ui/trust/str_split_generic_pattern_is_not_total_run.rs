//@ run-fail
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=off
//@ error-pattern: index out of bounds: the len is 4 but the index is 97
//@ ignore-emscripten no processes
//! The WITNESS for `str_split_generic_pattern_is_not_total.rs` (ITER-RECV-1): the
//! `count_pieces` that file's BEFORE compiler certified panic-free, driven with a
//! `&mut` closure pattern that indexes a 4-entry table by the `char` it is asked
//! about. `'a'` is 97, so the first `next` panics inside the certified loop.
//!
//! Built with verification OFF, so it passes before and after the fix alike: it
//! pins that the panic is real, not the verdict. Measured 2026-10-04 on the stage 1
//! of `38e6c69b1c` (`scratchpad/stage1-w11fix`): this file built
//! `-Ztrust-verify=off` exits 101 with the message above, from the closure in
//! `main`. Built `-Ztrust-verify=on` the same compiler refuses the binary, but only for
//! `main` and its closure (the closure's `slice` row fails); `count_pieces` itself
//! still reads `unreach proved` and nothing else, which is the lie.

#[inline(never)]
pub fn count_pieces<'a, 'b, F: FnMut(char) -> bool>(it: core::str::Split<'a, &'b mut F>) -> usize {
    let mut n = 0usize;
    for _p in it {
        n = n.wrapping_add(1);
    }
    n
}

fn main() {
    let table: Vec<bool> = vec![false; 4];
    let mut pred = |c: char| table[c as usize];
    let s = String::from("abc");
    println!("pieces = {}", count_pieces(s.split(&mut pred)));
}
