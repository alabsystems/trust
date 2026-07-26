// W6 harvest probe: closures + Option combinators.

#[inline(never)]
fn map_add1(o: Option<i32>) -> Option<i32> {
    o.map(|x| x + 1)
}

#[inline(never)]
fn map_cap(o: Option<i32>, k: i32) -> Option<i32> {
    o.map(move |x| x + k)
}

#[inline(never)]
fn and_then_pos(o: Option<i32>) -> Option<i32> {
    o.and_then(|x| if x > 0 { Some(x) } else { None })
}

#[inline(never)]
fn filter_pos(o: Option<i32>) -> Option<i32> {
    o.filter(|x| *x > 0)
}

#[inline(never)]
fn direct_call(x: i32) -> i32 {
    let f = |y: i32| y * 2;
    f(x)
}

fn main() {
    let n = std::env::args().count() as i32;
    let o = if n > 0 { Some(n) } else { None };
    let a = map_add1(o);
    let b = map_cap(o, n);
    let c = and_then_pos(o);
    let d = filter_pos(o);
    let e = direct_call(n);
    println!("{:?} {:?} {:?} {:?} {}", a, b, c, d, e);
}
