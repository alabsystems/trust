// `Shim(FnPtr(.., <fn item>))`: a fn item called through `Fn::call`.
fn twice<F: Fn(u64) -> u64>(f: F, x: u64) -> u64 {
    f(f(x))
}

fn inc(x: u64) -> u64 {
    x ^ 1
}

pub fn run(x: u64) -> u64 {
    twice(inc, x)
}
