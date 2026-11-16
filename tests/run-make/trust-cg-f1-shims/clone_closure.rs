// `Shim(Clone(<closure>))`: a closure is `Clone` when its captures are, by a synthesized shim.
fn dup<T: Clone>(t: &T) -> T {
    t.clone()
}

pub fn run(x: u64) -> u64 {
    let c = move || x;
    let d = dup(&c);
    d()
}
