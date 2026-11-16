// `Shim(Reify(..))`: a `#[track_caller]` item reified to a fn pointer, then called.
#[track_caller]
fn tc(x: u64) -> u64 {
    x ^ 1
}

pub fn run(x: u64) -> u64 {
    let f: fn(u64) -> u64 = tc;
    f(x)
}
