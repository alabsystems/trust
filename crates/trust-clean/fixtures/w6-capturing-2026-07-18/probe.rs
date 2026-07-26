// W6 increment-3 harvest probe: CAPTURING closures + Option combinators.
// Assert-free bitwise closure leaves (no overflow VCs), plus a stretch and_then
// and an FnMut forgery. Input from args().count() so nothing folds to a constant.

#[inline(never)]
fn cap_and(o: Option<u8>, k: u8) -> Option<u8> {
    o.map(move |x| x & k)
}

#[inline(never)]
fn cap_or(o: Option<u8>, k: u8) -> Option<u8> {
    o.map(move |x| x | k)
}

#[inline(never)]
fn cap_min_flag(o: Option<i32>, k: i32) -> Option<i32> {
    o.and_then(move |x| if x > k { Some(x) } else { None })
}

// FORGERY (a): an FnMut closure that MUTATES its capture. `Option::map` accepts it
// (FnMut: FnOnce), but the recorded ClosureCallKind is FnMut — both the capturing
// leaf read and the compose lane MUST decline.
#[inline(never)]
fn cap_fnmut(o: Option<i32>, k: i32) -> Option<i32> {
    let mut acc = k;
    o.map(move |x| {
        acc = acc.wrapping_add(x);
        acc
    })
}

fn main() {
    let n = std::env::args().count() as i32;
    let ou = if n > 0 { Some(n as u8) } else { None };
    let oi = if n > 0 { Some(n) } else { None };
    let a = cap_and(ou, n as u8);
    let b = cap_or(ou, n as u8);
    let c = cap_min_flag(oi, n);
    let d = cap_fnmut(oi, n);
    println!("{:?} {:?} {:?} {:?}", a, b, c, d);
}
