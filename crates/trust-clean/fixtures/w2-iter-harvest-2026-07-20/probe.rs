// W2 iterator target corpus probe crate.
// All wrappers #[inline(never)], all CALLED from main; slices built locally from arrays.

#[inline(never)]
fn sum_loop(s: &[i32]) -> i32 {
    let mut a = 0;
    for x in s {
        a += *x;
    }
    a
}

#[inline(never)]
fn count_pos(s: &[i32]) -> usize {
    let mut c = 0;
    for x in s {
        if *x > 0 {
            c += 1;
        }
    }
    c
}

#[inline(never)]
fn sum_iter(s: &[i32]) -> i32 {
    s.iter().sum()
}

#[inline(never)]
fn len_via_count(s: &[i32]) -> usize {
    s.iter().count()
}

#[inline(never)]
fn first_or(s: &[i32], d: i32) -> i32 {
    *s.first().unwrap_or(&d)
}

#[inline(never)]
fn while_idx(s: &[i32]) -> i32 {
    let mut a = 0;
    let mut i = 0;
    while i < s.len() {
        a += s[i];
        i += 1;
    }
    a
}

fn main() {
    let n = std::env::args().count() as i32;
    let arr = [n, n + 1, n - 3, 7];
    let s: &[i32] = &arr;
    let r1 = sum_loop(s);
    let r2 = count_pos(s);
    let r3 = sum_iter(s);
    let r4 = len_via_count(s);
    let r5 = first_or(s, n);
    let r6 = while_idx(s);
    println!("{} {} {} {} {} {}", r1, r2, r3, r4, r5, r6);
}
