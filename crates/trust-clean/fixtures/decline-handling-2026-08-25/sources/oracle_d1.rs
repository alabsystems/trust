// D1 runtime oracle — the `Rvalue::PtrOffset`-compensated-decline family.
// Build: rustc -O -C debug-assertions=on cs_oracle_d1.rs -o cs_oracle_d1
use std::hint::black_box;
use std::panic::catch_unwind;

// ---- the memchr `One::count` spine, both leaves -----------------------------

#[inline(never)]
pub fn count_raw_ok(_s1: u8, start: *const u8, end: *const u8) -> u64 {
    (black_box(end) as usize - black_box(start) as usize) as u64
}

#[inline(never)]
pub fn count_raw_panics(_s1: u8, _start: *const u8, _end: *const u8) -> u64 {
    panic!("count_raw leaf panics")
}

/// PROBE B — `One::count` as the fixture spells it (the body the `Rvalue::PtrOffset`
/// re-spelling models). Panic-free.
#[inline(never)]
pub fn count_ok(s1: u8, haystack: &[u8]) -> u64 {
    let start = black_box(haystack).as_ptr();
    let end = unsafe { start.add(haystack.len()) };
    count_raw_ok(s1, start, end)
}

/// PROBE C — the same spine whose LEAF panics.
#[inline(never)]
pub fn count_panicking_leaf(s1: u8, haystack: &[u8]) -> u64 {
    let start = black_box(haystack).as_ptr();
    let end = unsafe { start.add(haystack.len()) };
    count_raw_panics(s1, start, end)
}

// ---- the natural call-prefix graph shape ------------------------------------

#[inline(never)]
pub fn always_panics(h: &[u8]) -> u64 {
    panic!("leaf panics (len={})", black_box(h).len())
}

/// PROBE G — `let r = always_panics(h); let s = h.as_ptr(); let _e = s.add(h.len()); r`.
/// Every call sits in a prefix; the offset is the last statement before `Return`.
#[inline(never)]
pub fn count_after_panicking_leaf(haystack: &[u8]) -> u64 {
    let r = always_panics(black_box(haystack));
    let start = haystack.as_ptr();
    let end = unsafe { start.add(haystack.len()) };
    black_box(end);
    r
}

fn sweep(name: &str, f: impl Fn(usize) -> bool) {
    let (mut p, mut t, mut first) = (0usize, 0usize, None);
    for len in 0usize..24 {
        t += 1;
        if f(len) {
            p += 1;
            if first.is_none() {
                first = Some(format!("(len={len})"));
            }
        }
    }
    println!("{name}: {p}/{t} panicked first={first:?}");
}

fn main() {
    std::panic::set_hook(Box::new(|_| {}));
    sweep("B count_ok", |len| {
        let v: Vec<u8> = vec![7; len];
        catch_unwind(move || count_ok(b'x', &v)).is_err()
    });
    sweep("C count_panicking_leaf", |len| {
        let v: Vec<u8> = vec![7; len];
        catch_unwind(move || count_panicking_leaf(b'x', &v)).is_err()
    });
    sweep("G count_after_panicking_leaf", |len| {
        let v: Vec<u8> = vec![7; len];
        catch_unwind(move || count_after_panicking_leaf(&v)).is_err()
    });
}
