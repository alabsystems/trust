// `Shim(Clone(<fn item>))`: the derived `Clone` of `W<F>` clones its field through `F: Clone`,
// and `F` is a fn-item type here.
#[derive(Clone)]
pub struct W<F>(F);

fn inc(x: u64) -> u64 {
    x ^ 1
}

pub fn run(x: u64) -> u64 {
    let w = W(inc);
    let v = w.clone();
    (v.0)(x)
}
