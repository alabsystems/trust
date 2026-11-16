//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
#![crate_type = "lib"]
//! The return interval is exactly as wide as the helper can return, and nothing
//! narrower. Every caller below panics on the witness input.

fn widen(x: u8) -> u32 {
    x as u32 + 1
}

// x = 255: `widen` returns 256.
pub fn index_past_the_interval(a: &[u8; 256], x: u8) -> u8 { //~ ERROR strict verification failed for `return_interval_bounds_the_call_result_refused::index_past_the_interval`
    a[widen(x) as usize]
}

fn clamp10(n: u32) -> u32 {
    if n > 10 { 10 } else { n }
}

// n = 0: the clamp returns 0.
pub fn divide_by_clamp(h: u32, n: u32) -> u32 { //~ ERROR strict verification failed for `return_interval_bounds_the_call_result_refused::divide_by_clamp`
    h / clamp10(n)
}

#[derive(Clone, Copy)]
pub enum Dir {
    North,
    East,
    South,
    West,
}

impl Dir {
    pub fn index(self) -> usize {
        self as usize
    }
}

// d = West: index 3 into a table of 3.
pub fn lookup_short_table(table: &[u8; 3], d: Dir) -> u8 { //~ ERROR strict verification failed for `return_interval_bounds_the_call_result_refused::lookup_short_table`
    table[d.index()]
}

fn wraps(x: u32) -> u32 {
    x.wrapping_sub(1)
}

// x = 0: `wraps` returns `u32::MAX`.
pub fn index_by_wrap(a: &[u8; 16], x: u32) -> u8 { //~ ERROR strict verification failed for `return_interval_bounds_the_call_result_refused::index_by_wrap`
    if x < 16 { a[wraps(x) as usize] } else { 0 }
}

// ── Round 10 of the review: bodies the interval domain cannot follow lend no
// interval (`return_interval_admissible`). Each caller was PROVED, kernel-certified,
// and panicked, before the gate.

// A `u128` has no representable range here; `high_half(u128::MAX)` is 2^64 - 1.
fn high_half(x: u128) -> u64 {
    (x >> 64) as u64
}

pub fn doubled_high_half(x: u128) -> u64 { //~ ERROR strict verification failed for `return_interval_bounds_the_call_result_refused::doubled_high_half`
    high_half(x) * 2
}

// The write through `r` reaches `x`, which the domain cannot name from `r`.
fn select_write(v: u8, c: bool) -> u8 {
    let mut x: u8 = v / 50;
    let mut y: u8 = v / 50;
    let r = if c { &mut x } else { &mut y };
    *r = 200;
    x
}

pub fn index_by_select_write(t: &[u8; 6], v: u8, c: bool) -> u8 { //~ ERROR strict verification failed for `return_interval_bounds_the_call_result_refused::index_by_select_write`
    t[select_write(v, c) as usize]
}

// A destructor writes through the `&mut` it holds.
pub struct Guard<'a>(pub &'a mut u8);

impl Drop for Guard<'_> {
    fn drop(&mut self) {
        *self.0 = 200;
    }
}

fn guarded(v: u8) -> u8 {
    let mut x: u8 = v / 50;
    {
        let _g = Guard(&mut x);
    }
    x
}

pub fn index_by_guarded(t: &[u8; 6], v: u8) -> u8 { //~ ERROR strict verification failed for `return_interval_bounds_the_call_result_refused::index_by_guarded`
    t[guarded(v) as usize]
}

// A shift amount's interval reaching 128 made `x >> k` zero whatever its lower end.
fn shift_capped(x: u32, s: u32) -> u32 {
    let k = s.min(31);
    x >> k
}

pub fn index_by_shift(t: &[u8; 1], x: u32, s: u32) -> u8 { //~ ERROR strict verification failed for `return_interval_bounds_the_call_result_refused::index_by_shift`
    t[shift_capped(x, s) as usize]
}
