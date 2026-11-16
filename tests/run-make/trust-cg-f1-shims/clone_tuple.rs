// `Shim(Clone(<tuple>))`: tuples have no library `Clone` impl; rustc clones them field-wise.
#[derive(Clone)]
pub struct L(pub u64);

fn dup<T: Clone>(t: &T) -> T {
    t.clone()
}

pub fn one(x: u64) -> u64 {
    dup(&(x,)).0
}

pub fn two(x: u64) -> u64 {
    let p = dup(&(x, x));
    p.0 ^ p.1
}

pub fn mixed(x: u64) -> u64 {
    let p = dup(&(x, L(x)));
    p.0 ^ (p.1).0
}

// The tuple clone shim used as a VALUE (reified).
pub fn as_value() -> fn(&(i32, i32)) -> (i32, i32) {
    <(i32, i32) as Clone>::clone
}
